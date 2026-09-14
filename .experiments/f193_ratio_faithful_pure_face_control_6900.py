#!/usr/bin/env python3
"""Exact fixed-boundary pure-face control in the F193 ratio chamber."""

from __future__ import annotations

from math import comb
import hashlib
import json
from pathlib import Path
import resource

import f101_o2_bordered_filtration_mechanism_6900 as BM
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F


P = 193
N = 64
G_COUNT = 44
E_COUNT = N - G_COUNT
W = 31
M = 4
D = M * G_COUNT


def contact_column(a: int, n: int, u0: tuple[int, ...], scale: int = 1):
    column = {}
    for node in range(N):
        for dx in range(M):
            for dy in range(M - dx):
                if a < dx or n < dy:
                    continue
                value = (
                    scale * comb(a, dx) * pow(node, a - dx, P)
                    * comb(n, dy) * pow(u0[node], n - dy, P)
                ) % P
                if value:
                    column[(node, dx, dy)] = value
    return column


def main() -> None:
    BM.PRIME = BM.T.PRIME = BM.F.PRIME = F.PRIME = P
    agreement = tuple(range(G_COUNT))
    h_nodes = tuple(range(W + 1))
    r_nodes = tuple(range(W + 1, G_COUNT))
    h = F.locator(h_nodes)
    r = F.locator(r_nodes)
    boundary = F.poly_mul(F.poly_pow(h, M - 1), F.poly_pow(r, M))
    assert len(boundary) - 1 == D - W - 1
    u0 = (0,) * G_COUNT + (1,) * E_COUNT

    # A constant lane would have to be divisible by G^4, whose degree is D,
    # and is therefore zero under the strict degree<D source bound.  The Y
    # lane is frozen to B.  These are exactly all remaining pure corrections.
    echelon = BM.ColumnEchelon()
    correction_count = 0
    lane_rows = []
    for n in range(2, (D - 1) // W + 1):
        width = D - n * W
        before = echelon.rank
        for a in range(width):
            echelon.add(contact_column(a, n, u0), correction_count)
            correction_count += 1
        lane_rows.append((n, width, echelon.rank - before))

    target = {}
    for a, coefficient in enumerate(boundary):
        if not coefficient:
            continue
        for row, value in contact_column(a, 1, u0, int(coefficient)).items():
            target[row] = (target.get(row, 0) + value) % P
            if not target[row]:
                target.pop(row)
    residue = echelon.reduce(target)
    assert correction_count == echelon.rank == 270
    assert tuple(lane_rows) == ((2, 114, 114), (3, 83, 83),
                                (4, 52, 52), (5, 21, 21))
    assert len(residue) == 62

    stable = {
        "scope": (
            "exact pure bivariate fixed-boundary control in the same F193 "
            "ratio-faithful chamber as the full connector gate; not a "
            "Full187 inference"
        ),
        "p_N_g_e_w_m_D": (P, N, G_COUNT, E_COUNT, W, M, D),
        "boundary": "B*Y with B=H^3*R^4 and deg(B)=D-W-1",
        "correction_lanes_n_width_rank_gain": tuple(lane_rows),
        "correction_columns_and_rank": (correction_count, echelon.rank),
        "contact_row_count": N * M * (M + 1) // 2,
        "target_contact_support": len(target),
        "reduced_target_residue_support": len(residue),
        "reduced_target_residue_sha256": hashlib.sha256(
            repr(tuple(sorted(residue.items()))).encode()).hexdigest(),
        "decision": "RED_FIXED_BOUNDARY_PURE_FACE_NOT_IN_CORRECTION_IMAGE",
        "semantic_guard": (
            "A GREEN full pure+R shell connector would therefore use "
            "genuine translated slope/contact coupling; it would not imply "
            "pure bivariate membership."
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
