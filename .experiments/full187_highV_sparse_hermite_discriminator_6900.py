#!/usr/bin/env python3
"""Exact finite-field discriminator for the high-V top-error transfer.

This is deliberately a *small* model, not a target proof.  It retains the
literal multiplier-width formula and the full 60-layer shifted filtration,
but scales `(g,e,w)` from `(180413,81731,131071)` to `(11,5,8)`.  This keeps
the load-bearing ratios particularly closely:
`(g-w)/e = 3/5` versus `49342/81731`, and `w/e = 8/5` versus
`131071/81731`.  The signs and the high-V facet transition are unchanged.

For the top passive channel `c=d=0`, a row is

    p_b(X) L(X)^max(60-b,0) V^b.

At an error node use the deliberately minimal local transfer

    V = 1 + E + T R,

where `T` is the X-local parameter, `E` has contact weight three, and `R` is
the first passive direction.  The `(E^j R^r)` coefficient of `V^b` is
`binom(b,r) binom(b-r,j) T^r`; consequently its remaining X-Hasse layers are
`t < 60-r-3j`.  `--r-max 0` keeps only the top E channel, while `--r-max 1`
also keeps the first passive Hermite layer.  Multiplier columns are included
through their exact scaled strict source width.  This is the minimum of the
active `Y^b` cutoff and the pure-seed `Z^b Q^b` cutoff; the latter is narrower
here because `deg(Q)=2e>w`.  Different values of `b` have different seed
degree, so that endpoint cannot cancel between lanes.
"""

from __future__ import annotations

import argparse
import gc
import json
import math
from dataclasses import dataclass

import numpy as np
from flint import nmod_mat


PRIME = 257
M = 60
G = 11
EDEG = 5
WGT = 8
D = M * G
ERROR_NODES = tuple(range(EDEG))
AGREEMENT_ROOTS = tuple(range(20, 20 + G))
PAYLOAD_X = 100
PAYLOAD_V = 2


@dataclass(frozen=True)
class Schedule:
    name: str
    support: tuple[int, ...]
    mechanism: str


# Phase-one divergent schedules.  These are intentionally selected before
# looking at any ranks.
SCHEDULES = (
    Schedule(
        "fifo_contiguous_low",
        tuple(range(14, 35)),
        "Twenty-one adjacent b lanes; the binomial transform acts as a FIFO finite-difference packet.",
    ),
    Schedule(
        "returns_contiguous_high",
        tuple(range(62, 83)),
        "Place all lanes after locator saturation, testing the narrow high-b return path.",
    ),
    Schedule(
        "even_stride_crossdock",
        tuple(14 + 2 * i for i in range(21)),
        "Stride-two lanes emulate a sparse (V^2-1)-packet while retaining independent multipliers.",
    ),
    Schedule(
        "triple_stride_crossdock",
        tuple(14 + 3 * i for i in range(21)),
        "Stride-three lanes push cancellation toward the high-V facet with minimal lane count.",
    ),
    Schedule(
        "two_hub_low_high",
        tuple(range(14, 24)) + tuple(range(73, 83)),
        "Ten wide low-b lanes and ten narrow high-b lanes joined as a meet-in-the-middle transfer.",
    ),
    Schedule(
        "just_in_time_boundary",
        tuple(range(42, 63)),
        "Concentrate lanes around b=60 where agreement locator inventory reaches zero.",
    ),
)

# This is not one of the six precommitted divergent schedules.  It is the
# follow-up structural audit containing every b-lane with nonzero literal
# source width in the requested range.
ALL_SOURCE_LEGAL_HIGH_V = Schedule(
    "all_source_legal_highV",
    tuple(range(14, 66)),
    "All b=14..65 lanes; b>=66 have zero width from the pure-seed endpoint.",
)


def conv_trunc(a: list[int], b: list[int], n: int) -> list[int]:
    out = [0] * n
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b[: n - i]):
                out[i + j] = (out[i + j] + ai * bj) % PRIME
    return out


def pow_trunc(a: list[int], exponent: int, n: int) -> list[int]:
    out = [1] + [0] * (n - 1)
    base = a[:]
    k = exponent
    while k:
        if k & 1:
            out = conv_trunc(out, base, n)
        base = conv_trunc(base, base, n)
        k >>= 1
    return out


def locator_taylor_at(x: int) -> list[int]:
    out = [1] + [0] * (M - 1)
    for root in AGREEMENT_ROOTS:
        out = conv_trunc(out, [(x - root) % PRIME, 1], M)
    return out


def multiplier_dimension(b: int) -> int:
    ell = max(M - b, 0)
    active_cutoff = D - b * WGT
    pure_seed_cutoff = D - 2 * EDEG * b
    # Both strict inequalities deg(p L^ell) < cutoff must hold.
    return max(0, min(active_cutoff, pure_seed_cutoff) - ell * G)


def row_offsets(r_max: int) -> tuple[dict[tuple[int, int, int], int], int]:
    offsets: dict[tuple[int, int, int], int] = {}
    cursor = 0
    for ni, _x in enumerate(ERROR_NODES):
        for r in range(r_max + 1):
            for j in range((M - r - 1) // 3 + 1):
                offsets[(ni, r, j)] = cursor
                cursor += M - r - 3 * j
    return offsets, cursor


def build_matrix(
    schedule: Schedule, r_max: int
) -> tuple[nmod_mat, list[int], list[tuple[int, int]]]:
    offsets, nrows = row_offsets(r_max)
    columns = [
        (b, a)
        for b in schedule.support
        for a in range(multiplier_dimension(b))
    ]
    dense = np.zeros((nrows, len(columns)), dtype=np.int64)
    payload = [0] * len(columns)

    by_b: dict[int, list[tuple[int, int]]] = {}
    for col, (b, a) in enumerate(columns):
        by_b.setdefault(b, []).append((col, a))

    for b, tagged_columns in by_b.items():
        ell = max(M - b, 0)
        for ni, x in enumerate(ERROR_NODES):
            base = pow_trunc(locator_taylor_at(x), ell, M)
            current = base
            generated: dict[int, list[int]] = {}
            max_a = tagged_columns[-1][1]
            for a in range(max_a + 1):
                generated[a] = current
                nxt = [0] * M
                for t in range(M):
                    nxt[t] = x * current[t]
                    if t:
                        nxt[t] += current[t - 1]
                    nxt[t] %= PRIME
                current = nxt
            for col, a in tagged_columns:
                jet = generated[a]
                for r in range(min(r_max, b) + 1):
                    for j in range(min((M - r - 1) // 3, b - r) + 1):
                        height = M - r - 3 * j
                        factor = (
                            math.comb(b, r) * math.comb(b - r, j)
                        ) % PRIME
                        start = offsets[(ni, r, j)]
                        dense[start : start + height, col] = (
                            factor * np.asarray(jet[:height], dtype=np.int64)
                        ) % PRIME

        l_payload = 1
        for root in AGREEMENT_ROOTS:
            l_payload = l_payload * (PAYLOAD_X - root) % PRIME
        for col, a in tagged_columns:
            payload[col] = (
                pow(PAYLOAD_X, a, PRIME)
                * pow(l_payload, ell, PRIME)
                * pow(PAYLOAD_V, b, PRIME)
            ) % PRIME

    # python-flint's dense constructor is substantially faster than millions
    # of scalar assignments.  Release the NumPy and Python staging objects as
    # soon as the matrix is built.
    rows = dense.tolist()
    matrix = nmod_mat(rows, PRIME)
    del rows, dense
    gc.collect()
    return matrix, payload, columns


def run_schedule(schedule: Schedule, r_max: int = 0) -> dict[str, object]:
    matrix, payload, columns = build_matrix(schedule, r_max)
    rank = matrix.rank()
    nrows = matrix.nrows()
    ncols = matrix.ncols()
    augmented_rows = [[int(matrix[i, j]) for j in range(ncols)] for i in range(nrows)]
    augmented_rows.append(payload)
    augmented_rank = nmod_mat(augmented_rows, PRIME).rank()
    del matrix, augmented_rows
    gc.collect()
    return {
        "name": schedule.name,
        "mechanism": schedule.mechanism,
        "support": list(schedule.support),
        "rows": nrows,
        "columns": ncols,
        "rank": rank,
        "nullity": ncols - rank,
        "payload_rank_gain": augmented_rank - rank,
        "passive_R_degree_max": r_max,
        "multiplier_widths": {
            str(b): multiplier_dimension(b) for b in schedule.support
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--schedule", action="append", default=[])
    parser.add_argument("--r-max", type=int, default=0)
    parser.add_argument("--include-structural-audit", action="store_true")
    args = parser.parse_args()
    wanted = set(args.schedule)
    available = SCHEDULES + ((ALL_SOURCE_LEGAL_HIGH_V,)
        if args.include_structural_audit or ALL_SOURCE_LEGAL_HIGH_V.name in wanted
        else ())
    selected = [s for s in available if not wanted or s.name in wanted]
    if wanted - {s.name for s in selected}:
        raise SystemExit(f"unknown schedules: {sorted(wanted - {s.name for s in selected})}")
    if args.r_max < 0:
        raise SystemExit("--r-max must be nonnegative")
    results = [run_schedule(s, args.r_max) for s in selected]
    print(json.dumps({
        "field": PRIME,
        "scaled_parameters": {"m": M, "g": G, "e": EDEG, "w": WGT},
        "scope": (
            "necessary V=1+E+T*R local subsystem through passive R degree "
            f"{args.r_max}"
        ),
        "results": results,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
