#!/usr/bin/env python3
"""Exact two-generator contact-ideal interface for the Full187 pure face.

The executable freezes the literal coprime G/E partition and the algebraic
certificates used in the accompanying note.  It deliberately does not expand
the 60th powers: those are the compact module basis to feed to a shifted
reducer, not a dense target computation.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import struct
import time

from flint import nmod_poly

import full187_target_charge13_transposed_four_residue_gate_6900 as T


def polynomial_row_sha256(rows: list[list[nmod_poly]]) -> str:
    digest = hashlib.sha256()
    chunk: list[int] = []
    for row in rows:
        for poly in row:
            digest.update(struct.pack("<q", poly.degree()))
            for j in range(poly.degree() + 1):
                chunk.append(int(poly[j]))
                if len(chunk) == 16_384:
                    digest.update(struct.pack(f"<{len(chunk)}I", *chunk))
                    chunk.clear()
    if chunk:
        digest.update(struct.pack(f"<{len(chunk)}I", *chunk))
    return digest.hexdigest()


def shifted_affine_popov(g: nmod_poly, e: nmod_poly) -> dict:
    """Euclidean weak-Popov reduction of [0,E],[-G,G], shift [0,W]."""
    zero = nmod_poly([], T.P)
    rows = [[zero, e], [-g, g]]
    negative_infinity = -10**18

    def shifted_data(row: list[nmod_poly]) -> tuple[int, int]:
        degrees = (
            row[0].degree() if row[0] else negative_infinity,
            (row[1].degree() + T.W) if row[1] else negative_infinity,
        )
        shifted_degree = max(degrees)
        # CompPoly's convention: the larger position wins a tie.
        leading_position = 1 if degrees[1] >= degrees[0] else 0
        return shifted_degree, leading_position

    started = time.monotonic()
    steps = 0
    while shifted_data(rows[0])[1] == shifted_data(rows[1])[1]:
        degree0, position = shifted_data(rows[0])
        degree1, _ = shifted_data(rows[1])
        high = 0 if degree0 >= degree1 else 1
        low = 1 - high
        quotient, remainder = divmod(
            rows[high][position], rows[low][position])
        assert quotient
        assert remainder == (
            rows[high][position] - quotient * rows[low][position])
        rows[high] = [
            rows[high][j] - quotient * rows[low][j] for j in range(2)
        ]
        steps += 1
        assert steps <= T.N

    data = tuple(shifted_data(row) for row in rows)
    assert {position for _, position in data} == {0, 1}
    determinant = rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0]
    assert determinant == g * e
    assert determinant.degree() == T.N
    assert sum(degree for degree, _ in data) == T.N + T.W
    assert data == ((196_608, 0), (196_607, 1))
    component_degrees = tuple(
        (row[0].degree(), row[1].degree()) for row in rows)
    assert component_degrees == ((196_608, 65_535), (196_607, 65_536))

    return {
        "input_rows": "[0,E],[-G,G]",
        "shift": (0, T.W),
        "full_quotient_euclidean_steps": steps,
        "output_shifted_degree_and_leading_position": data,
        "output_component_degrees": component_degrees,
        "shifted_degree_sum": sum(degree for degree, _ in data),
        "determinant": "G*E=X^N-1",
        "row_coefficients_sha256": polynomial_row_sha256(rows),
        "elapsed_seconds": time.monotonic() - started,
        "decision": "GREEN_EXACT_AFFINE_WEAK_POPOV_BASIS",
    }


def main() -> None:
    instance = T.build_target_instance()
    p = T.P
    h = nmod_poly(instance.xi_h_coefficients, p)
    r = nmod_poly(instance.xi_r_coefficients, p)
    e = nmod_poly(instance.xi_e_coefficients, p)
    g = h * r
    omega = nmod_poly([-1] + [0] * (T.N - 1) + [1], p)
    assert g * e == omega

    gcd, bez_g, bez_e = g.xgcd(e)
    assert gcd == nmod_poly([1], p)
    assert bez_g * g + bez_e * e == gcd
    affine_popov = shifted_affine_popov(g, e)

    # If A=E*Y and B=G*(Y-1), then
    #   E*B-G*A = -GE,
    #   bez_g*Y*B + bez_e*(Y-1)*A = Y(Y-1).
    # Together with A and B themselves, these recover all four generators of
    # (G,Y)(E,Y-1).  This is an algebraic coefficient identity; the X-side
    # check needed by it is exactly the Bezout equality asserted above.
    basis_rows = tuple(
        {
            "i": i,
            "factor": f"(E*Y)^{i}*(G*(Y-1))^{T.M-i}",
            "X_factor_degree": i * T.E + (T.M - i) * T.G,
            "minimum_Y_degree": i,
            "maximum_Y_degree": T.M,
        }
        for i in range(T.M + 1)
    )
    assert len(basis_rows) == 61

    stable = {
        "scope": (
            "exact unbounded Fp[X,Y] pure-face contact ideal and compact "
            "power basis; no tapered membership result, Full187 lift, "
            "score, candidate, or submission"
        ),
        "target_p_N_G_E_M": (p, T.N, T.G, T.E, T.M),
        "partition": "G*E=X^N-1 and gcd(G,E)=1",
        "bezout_degree_G_coefficient": bez_g.degree(),
        "bezout_degree_E_coefficient": bez_e.degree(),
        "simple_contact_ideals": {
            "agreements": "(G,Y)",
            "errors": "(E,Y-1)",
            "sum_is_unit": True,
        },
        "two_generator_graph_ideal": "I=(E*Y, G*(Y-1))",
        "recovery_identities": (
            "E*G*(Y-1)-G*E*Y=-G*E",
            "bez_g*Y*G*(Y-1)+bez_e*(Y-1)*E*Y=Y*(Y-1)",
        ),
        "fat_contact_ideal": "I^60",
        "compact_power_basis": basis_rows,
        "basis_row_count": len(basis_rows),
        "affine_shifted_popov": affine_popov,
        "decision": (
            "GREEN_EXACT_TWO_GENERATOR_CONTACT_IDEAL__"
            "GREEN_61_ROW_UNBOUNDED_POWER_BASIS__"
            "GREEN_AFFINE_WEAK_POPOV_START__"
            "NEXT_MULTIPLICITY60_SYMMETRIC_POWER_REDUCTION"
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
