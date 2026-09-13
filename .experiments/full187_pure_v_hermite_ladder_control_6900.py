#!/usr/bin/env python3
"""Exact finite controls for the Full187 pure-V Hermite ladder.

For disjoint monic locators L (agreements, degree g) and H (errors, degree e)
and multiplicity m, the proposed restricted source is

    h = sum_{k=2..K} p_k(X) L(X)^(m-k) V^k       (k <= m)
        + sum_{k=m+1..K} p_k(X) V^k,

where every resulting V^k coefficient q_k has the single uniform strict
window

    deg(q_k) + 2 e k < m g.

The requested F0 correction is equivalent, on the normalized error chart
V=1+local, to

    h - L^(m-1) V in (H, V-1)^m.

This script constructs that literal bivariate Taylor matrix over F_101.  It
uses all X/V jets of total order below m at every error node and reports
whether the distinguished RHS lies in the restricted ladder image.  These
are finite discriminators, not a theorem for the target locators.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import resource

from flint import nmod_mat


P = 101


def poly_mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % P
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def poly_pow(base, exponent):
    out = (1,)
    power = base
    while exponent:
        if exponent & 1:
            out = poly_mul(out, power)
        power = poly_mul(power, power)
        exponent //= 2
    return out


def locator(nodes):
    out = (1,)
    for x in nodes:
        out = poly_mul(out, ((-x) % P, 1))
    return out


def translated_coeff(poly, x, degree):
    """Coefficient of t^degree in poly(x+t)."""
    return sum(
        coefficient * math.comb(power, degree) * pow(x, power - degree, P)
        for power, coefficient in enumerate(poly)
        if power >= degree
    ) % P


def compact_nullspace(matrix):
    raw, nullity = matrix.nullspace()
    answer = nmod_mat(matrix.ncols(), nullity, [
        int(raw[i, j]) % P
        for i in range(matrix.ncols()) for j in range(nullity)
    ], P)
    assert matrix * answer == nmod_mat(matrix.nrows(), nullity, P)
    return answer


def horizontal_concat(left, right):
    assert left.nrows() == right.nrows()
    return nmod_mat(left.nrows(), left.ncols() + right.ncols(), [
        int(left[i, j]) if j < left.ncols()
        else int(right[i, j - left.ncols()])
        for i in range(left.nrows())
        for j in range(left.ncols() + right.ncols())
    ], P)


def run_case(e, g, m):
    assert 0 < 2 * e < g and g + e < P
    agreements = tuple(range(g))
    errors = tuple(range(g, g + e))
    L = locator(agreements)
    max_k = (m * g - 1) // (2 * e)
    rows = tuple(
        (x, dx, dv)
        for x in errors
        for dx in range(m)
        for dv in range(m - dx)
    )
    row_index = {row: i for i, row in enumerate(rows)}

    columns = []
    labels = []
    for k in range(2, max_k + 1):
        lpower = max(m - k, 0)
        base = poly_pow(L, lpower)
        width = m * g - 2 * e * k - lpower * g
        assert width == (k * (g - 2 * e) if k <= m
                         else m * g - 2 * e * k)
        for a in range(width):
            q = (0,) * a + base
            column = [0] * len(rows)
            for x in errors:
                for dx in range(m):
                    qdx = translated_coeff(q, x, dx)
                    if not qdx:
                        continue
                    for dv in range(min(k, m - dx - 1) + 1):
                        column[row_index[(x, dx, dv)]] = (
                            qdx * math.comb(k, dv)) % P
            columns.append(column)
            labels.append((k, a, width))

    matrix = nmod_mat(len(rows), len(columns), [
        columns[j][i]
        for i in range(len(rows)) for j in range(len(columns))
    ], P)
    rhs_poly = poly_pow(L, m - 1)
    rhs = [0] * len(rows)
    for x in errors:
        for dx in range(m):
            value = translated_coeff(rhs_poly, x, dx)
            rhs[row_index[(x, dx, 0)]] = value
            if dx + 1 < m:
                rhs[row_index[(x, dx, 1)]] = value
    rhs_column = nmod_mat(len(rows), 1, rhs, P)
    augmented = horizontal_concat(matrix, rhs_column)
    rank = matrix.rank()
    augmented_rank = augmented.rank()
    solution = None
    if rank == augmented_rank:
        # A solution is not needed for the rank gate.  Record the kernel
        # dimension because it detects accidental square/full-rank cases.
        solution = True
    result = {
        "scope": "literal normalized pure-V fat-point control; finite only",
        "field": P,
        "parameters_e_g_m": (e, g, m),
        "agreement_error_nodes": (agreements, errors),
        "max_power": max_k,
        "rows_columns": (len(rows), len(columns)),
        "matrix_rank_augmented_rank": (rank, augmented_rank),
        "rhs_in_image": rank == augmented_rank,
        "kernel_dimension": len(columns) - rank,
        "uniform_window_identity_checked": True,
        "interpretation": (
            "The rows are exactly all coefficients of (X-x)^dx "
            "(V-1)^dv with dx+dv<m. Failure is a decisive obstruction "
            "for this finite locator fixture only."
        ),
    }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=("tiny", "ratio", "all"),
                        required=True)
    args = parser.parse_args()
    cases = {
        "tiny": (3, 7, 8),
        "ratio": (5, 11, 12),
    }
    selected = cases.items() if args.case == "all" else ((args.case, cases[args.case]),)
    result = {label: run_case(*parameters) for label, parameters in selected}
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    print(json.dumps(result, indent=2, sort_keys=True))
    print("canonical_sha256=" + hashlib.sha256(canonical.encode()).hexdigest())
    print("max_rss_kib=" + str(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))


if __name__ == "__main__":
    main()
