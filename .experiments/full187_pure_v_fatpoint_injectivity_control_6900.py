#!/usr/bin/env python3
"""Exact all-lane controls for the pure-V bivariate fat-point problem.

The source is the literal filtered part of (L,V)^m with no V^0/V^1
boundary term:

  sum_{2 <= b <= floor((m*g-1)/(2e))}
    L^max(m-b,0) X^a V^b,
  0 <= a < m*g - 2e*b - g*max(m-b,0).

Every column lies in I_G=(L,V)^m.  Its image consists of all X/V Hasse
jets of total order below m at the error points, so a zero column
combination is exactly membership in I_E=(H,V-1)^m.  Since I_G and I_E are
comaximal, this is the product/intersection test, not a single-b packet
test.  The affine right hand side is L^(m-1)V, which asks whether a source
element can give the required correction.

Finite fields are controls only.  The target arithmetic record is exact but
does not promote the finite ranks to the target field.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import resource

from flint import nmod_mat


P = 101


def poly_mul(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % P
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def poly_pow(base: tuple[int, ...], exponent: int) -> tuple[int, ...]:
    out = (1,)
    power = base
    while exponent:
        if exponent & 1:
            out = poly_mul(out, power)
        power = poly_mul(power, power)
        exponent //= 2
    return out


def locator(nodes: tuple[int, ...]) -> tuple[int, ...]:
    out = (1,)
    for node in nodes:
        out = poly_mul(out, ((-node) % P, 1))
    return out


def translated_coeff(poly: tuple[int, ...], x: int, degree: int) -> int:
    """The coefficient of t^degree in poly(x+t), in F_P."""
    return sum(
        coefficient * math.comb(power, degree) * pow(x, power - degree, P)
        for power, coefficient in enumerate(poly)
        if power >= degree
    ) % P


def horizontal_concat(left: nmod_mat, right: nmod_mat) -> nmod_mat:
    assert left.nrows() == right.nrows()
    return nmod_mat(left.nrows(), left.ncols() + right.ncols(), [
        int(left[i, j]) if j < left.ncols()
        else int(right[i, j - left.ncols()])
        for i in range(left.nrows())
        for j in range(left.ncols() + right.ncols())
    ], P)


def run_case(e: int, g: int, m: int) -> dict[str, object]:
    assert 0 < 2 * e < g < 3 * e
    assert g + e < P and m < P
    agreements = tuple(range(g))
    errors = tuple(range(g, g + e))
    L = locator(agreements)
    D = m * g
    max_b = (D - 1) // (2 * e)
    rows = tuple(
        (x, dx, dv)
        for x in errors
        for dx in range(m)
        for dv in range(m - dx)
    )
    row_index = {row: i for i, row in enumerate(rows)}

    columns: list[list[int]] = []
    widths: list[tuple[int, int]] = []
    for b in range(2, max_b + 1):
        lpower = max(m - b, 0)
        width = D - 2 * e * b - lpower * g
        assert width > 0
        # This is all of the filtered I_G coefficient strip, including all
        # high b > m lanes.  No packet or fixed-degree restriction occurs.
        widths.append((b, width))
        base = poly_pow(L, lpower)
        for a in range(width):
            q = (0,) * a + base
            column = [0] * len(rows)
            for x in errors:
                for dx in range(m):
                    qdx = translated_coeff(q, x, dx)
                    if not qdx:
                        continue
                    for dv in range(min(b, m - dx - 1) + 1):
                        column[row_index[(x, dx, dv)]] = (
                            qdx * math.comb(b, dv)) % P
            columns.append(column)

    matrix = nmod_mat(len(rows), len(columns), [
        columns[column][row]
        for row in range(len(rows))
        for column in range(len(columns))
    ], P)
    rhs_poly = poly_pow(L, m - 1)
    rhs = [0] * len(rows)
    for x in errors:
        for dx in range(m):
            value = translated_coeff(rhs_poly, x, dx)
            rhs[row_index[(x, dx, 0)]] = value
            if dx + 1 < m:
                rhs[row_index[(x, dx, 1)]] = value
    augmented = horizontal_concat(matrix, nmod_mat(len(rows), 1, rhs, P))
    rank = matrix.rank()
    augmented_rank = augmented.rank()
    return {
        "field": P,
        "parameters_e_g_m": (e, g, m),
        "weights_x_v": (1, 2 * e),
        "strict_cutoff": D,
        "max_b_including_rounding": max_b,
        "high_b_offset": max_b - m,
        "all_lane_widths": widths,
        "rows_columns": (len(rows), len(columns)),
        "matrix_rank_augmented_rank": (rank, augmented_rank),
        "intersection_kernel_dimension": len(columns) - rank,
        "rhs_in_source_image": rank == augmented_rank,
        "meaning": (
            "kernel zero means the complete listed pure-V source has zero "
            "intersection with I_E; RHS false means L^(m-1)V cannot be "
            "matched by that entire source."
        ),
    }


def target_arithmetic() -> dict[str, object]:
    e, g, m = 81_731, 180_413, 60
    D, weight_v = m * g, 2 * e
    max_b = (D - 1) // weight_v
    widths = [
        (b, D - weight_v * b - max(m - b, 0) * g)
        for b in range(2, max_b + 1)
    ]
    assert max_b == 66
    assert widths[-1] == (66, 36_288)
    return {
        "parameters_e_g_m": (e, g, m),
        "weights_x_v": (1, weight_v),
        "strict_cutoff": D,
        "max_b": max_b,
        "b66_width": widths[-1][1],
        "all_positive_lane_count": len(widths),
        "source_column_count": sum(width for _b, width in widths),
        "warnings": (
            "This is only the exact target rounding ledger.  It does not "
            "claim a target-field rank theorem."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=("small", "rounding", "target"),
                        required=True)
    args = parser.parse_args()
    if args.case == "small":
        result: dict[str, object] = run_case(3, 7, 8)
    elif args.case == "rounding":
        # g/e=11/5 is close to the target 180413/81731.  Here b_max=m+6,
        # so every high lane is present in one all-source computation.
        result = run_case(5, 11, 61)
    else:
        result = target_arithmetic()
    result["scope"] = "pure-V bivariate fat-point exact control; finite rank is not target proof"
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    print(json.dumps(result, indent=2, sort_keys=True))
    print("canonical_sha256=" + hashlib.sha256(canonical.encode()).hexdigest())
    print("max_rss_kib=" + str(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))


if __name__ == "__main__":
    main()
