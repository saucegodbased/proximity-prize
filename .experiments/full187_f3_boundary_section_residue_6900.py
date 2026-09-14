#!/usr/bin/env python3
"""Exact legal agreement section for the Full187 F3 pure boundary.

This is a small discriminator, not a Full187 construction.  It identifies a
particularly simple polynomial with the prescribed Y-linear coefficient and
all agreement multiplicities, then computes its complete error Hasse residue
modulo Xi_E on the literal target.  The point is to give subsequent coupled
approximant gates the one structured right-hand side they actually have to
lift instead of asking them to be onto an arbitrary codomain.
"""

from __future__ import annotations

from math import comb
import hashlib
import json
from pathlib import Path
import resource
import struct

from flint import nmod_poly

import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = T.P
M = T.M
W = T.W
G_DEG = T.G
H_DEG = T.H
R_DEG = G_DEG - H_DEG
E_DEG = T.E
D = T.D


def sha256_poly_sequence(polys: list[nmod_poly]) -> str:
    digest = hashlib.sha256()
    for poly in polys:
        degree = max(-1, poly.degree())
        digest.update(struct.pack("<q", degree))
        if degree >= 0:
            chunk: list[int] = []
            for j in range(degree + 1):
                chunk.append(int(poly[j]))
                if len(chunk) == 16_384:
                    digest.update(struct.pack(f"<{len(chunk)}I", *chunk))
                    chunk.clear()
            if chunk:
                digest.update(struct.pack(f"<{len(chunk)}I", *chunk))
    return digest.hexdigest()


def main() -> None:
    assert H_DEG == W + 1
    assert R_DEG == G_DEG - W - 1
    assert D == M * G_DEG

    # K0 = -R^60 Y (Y-H)^59.  Its coefficient of Y^n is
    #   -binom(59,n-1)(-H)^(60-n)R^60,  1 <= n <= 60.
    # In particular [Y]K0=H^59R^60=B.  The exact degree is strictly inside
    # every source window, with n-1 spare coefficient positions.
    coefficient_rows = []
    for n in range(1, M + 1):
        degree = M * R_DEG + (M - n) * H_DEG
        width = D - n * W
        assert degree == D - n * H_DEG
        assert width - (degree + 1) == n - 1
        coefficient_rows.append((n, degree, width, n - 1))
    assert coefficient_rows[0] == (1, D - H_DEG, D - W, 0)

    # At an H-root, (Y-H) and Y both belong to the local maximal ideal, so
    # their 60 factors give order 60.  At an R-root, R^60 does.  Dividing the
    # n-th coefficient by G^(60-n) gives a scalar multiple of R^n; hence in
    # the graph coordinates F=G^-60 K(GV),
    #
    #             F0 = -R V (R V - 1)^59,
    #
    # and deg(R^n)=n*(G-W-1)<n*(G-W).
    transformed_rows = []
    for n in range(1, M + 1):
        transformed_degree = n * R_DEG
        transformed_cap = n * (G_DEG - W)
        assert transformed_cap - (transformed_degree + 1) == n - 1
        transformed_rows.append(
            (n, transformed_degree, transformed_cap, n - 1))

    instance = T.build_target_instance()
    h = nmod_poly(instance.xi_h_coefficients, P)
    r = nmod_poly(instance.xi_r_coefficients, P)
    e = nmod_poly(instance.xi_e_coefficients, P)
    assert (h.degree(), r.degree(), e.degree()) == (
        H_DEG, R_DEG, E_DEG)
    assert h * r * e == nmod_poly([-1] + [0] * (T.N - 1) + [1], P)

    # Around the error centre Y=1, the j-th Y-Hasse coefficient is
    #
    # -R^60 (1-H)^(59-j)
    #       * (binom(60,j) - H*binom(59,j-1)).
    #
    # We evaluate all sixty formulas modulo E.  Nonzero mod E already proves
    # K0 alone misses every required E^(60-j) divisibility; the sequence is
    # the structured target for the correction module.
    one = nmod_poly([1], P)
    h_mod = h % e
    t = (one - h_mod) % e
    r60 = r.pow_mod(M, e)
    t_powers = [one]
    for _ in range(M - 1):
        t_powers.append((t_powers[-1] * t) % e)

    residues: list[nmod_poly] = []
    residue_degrees: list[int] = []
    for j in range(M):
        bracket = nmod_poly([comb(M, j) % P], P)
        if j > 0:
            bracket = (
                bracket - (comb(M - 1, j - 1) % P) * h_mod
            ) % e
        residue = (-r60 * t_powers[M - 1 - j] * bracket) % e
        assert residue != 0
        residues.append(residue)
        residue_degrees.append(residue.degree())

    stable = {
        "scope": (
            "exact prescribed-boundary agreement section and its error "
            "residue modulo E; no correction, membership, Full187 lift, "
            "score, candidate, or submission"
        ),
        "target_p_N_W_G_E_H_R_M_D": (
            P, T.N, W, G_DEG, E_DEG, H_DEG, R_DEG, M, D
        ),
        "section": "K0 = -R^60 * Y * (Y-H)^59",
        "Y1_coefficient": "H^59*R^60 = B",
        "agreement_order": {
            "H_nodes": "Y*(Y-H)^59 has local order 60",
            "R_nodes": "R^60 has local order 60",
        },
        "source_degree_rows_n_degree_width_spare": tuple(coefficient_rows),
        "graph_transform": "F0 = -R*V*(R*V-1)^59",
        "transformed_rows_n_degree_cap_spare": tuple(transformed_rows),
        "error_hasse_residue_formula": (
            "rho_j=-R^60*(1-H)^(59-j)*"
            "(binom(60,j)-H*binom(59,j-1)) mod E"
        ),
        "all_60_error_residues_nonzero_mod_E": True,
        "error_residue_degrees": tuple(residue_degrees),
        "error_residue_sequence_sha256": sha256_poly_sequence(residues),
        "decision": (
            "GREEN_EXPLICIT_LEGAL_AGREEMENT_SECTION__"
            "GREEN_STRUCTURED_ERROR_RIGHT_HAND_SIDE__"
            "NEXT_TEST_TARGET_MEMBERSHIP_NOT_ARBITRARY_SURJECTIVITY"
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
