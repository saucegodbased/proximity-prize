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

from flint import nmod_poly

import full187_target_charge13_transposed_four_residue_gate_6900 as T


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
        "decision": (
            "GREEN_EXACT_TWO_GENERATOR_CONTACT_IDEAL__"
            "GREEN_61_ROW_UNBOUNDED_POWER_BASIS__"
            "NEXT_SHIFTED_REDUCE_WITH_LITERAL_TAPER"
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
