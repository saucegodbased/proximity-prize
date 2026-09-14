#!/usr/bin/env python3
"""Interpolate fixed bordered-minor charts in the tiny exact-G two-error model.

This deliberately studies *fixed raw minors*, not an RREF Schur determinant.
The row/column charts are selected once over F_101 by
``k0_two_error_adjacent_probe_6900.py`` and then evaluated over a larger prime
so the degree-103 seed bound is below the characteristic.  It is a lightweight
discriminator for mismatch factors and chart dependence; it is not a target
rank certificate.
"""

from __future__ import annotations

import argparse
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import k0_two_error_adjacent_probe_6900 as Two  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


LIMIT_BYTES = 3900 * 1024**2
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
new_hard = LIMIT_BYTES if hard == resource.RLIM_INFINITY else min(hard, LIMIT_BYTES)
resource.setrlimit(resource.RLIMIT_AS, (min(LIMIT_BYTES, new_hard), new_hard))


def interpolate(values: list[int], prime: int) -> nmod_poly:
    """Unique polynomial of degree < len(values) through x=0,...,n-1."""
    answer = nmod_poly([], prime)
    for x, value in enumerate(values):
        numerator = nmod_poly([1], prime)
        denominator = 1
        for y in range(len(values)):
            if y == x:
                continue
            numerator *= nmod_poly([-y, 1], prime)
            denominator = denominator * (x - y) % prime
        answer += (value * pow(denominator, -1, prime)) * numerator
    return answer


def boundary(monomials, prime):
    return nmod_mat(
        4, len(monomials),
        [
            pow(Two.BOUNDARY_X, monomial[0], prime)
            if sum(monomial[1:]) == 1 and monomial[1:][coordinate] == 1
            else 0
            for coordinate in range(4)
            for monomial in monomials
        ], prime,
    )


def fixed_minor_det(monomials, rows, chart, b, c, prime, d4=1, d5=1):
    pivrows, pivcols, extras = chart
    chosen = pivcols + extras
    chosen_monomials = tuple(monomials[j] for j in chosen)
    chosen_rows = tuple(rows[i] for i in pivrows)
    row_index = {row: i for i, row in enumerate(chosen_rows)}
    matrix = nmod_mat(len(chosen_rows) + 4, len(chosen), prime)
    u0 = (0, 0, 0, 0, d4 % prime, d5 % prime)
    u1 = (0, 0, 0, 1, b % prime, c % prime)
    for column_index, (xp, yp, rp, sp, zp) in enumerate(chosen_monomials):
        for node in Two.NODES:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                Two.PROFILE.m, 2, prime,
            )
            for term, value in expansion.items():
                row = row_index.get((node, term))
                if row is not None:
                    matrix[row, column_index] = value
    bdry = boundary(chosen_monomials, prime)
    for i in range(4):
        for j in range(len(chosen)):
            matrix[len(chosen_rows) + i, j] = bdry[i, j]
    return int(matrix.det()) % prime


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--chart", type=int, choices=(0, 1, 2, 3), required=True)
    parser.add_argument("--variable", choices=("b", "c", "d4", "d5", "line"),
                        required=True)
    parser.add_argument("--fixed", type=int, default=0,
                        help="fixed value of the other error direction")
    parser.add_argument("--b-line", default="4,1",
                        help="b=b0+b1*t in line mode")
    parser.add_argument("--c-line", default="10,1",
                        help="c=c0+c1*t in line mode")
    parser.add_argument("--prime", type=int, default=1009)
    parser.add_argument("--samples", type=int, default=105)
    parser.add_argument("--b", type=int, default=0)
    parser.add_argument("--c", type=int, default=10)
    parser.add_argument("--d4", type=int, default=1)
    parser.add_argument("--d5", type=int, default=1)
    args = parser.parse_args()
    started = time.monotonic()

    monomials = Two.K0.support(Two.PROFILE)
    sparse = Two.columns(monomials, 1, 4, 10)
    rows = tuple(sorted(set().union(*(set(c) for c in sparse)), key=repr))
    bdry101 = Two.boundary(monomials)
    charts = (
        Two.extract_chart(monomials, rows, bdry101, 1, 4, 10),
        Two.extract_chart(monomials, rows, bdry101, 1, 0, 10),
        Two.extract_chart(monomials, rows, bdry101, 1, 4, 0),
        Two.extract_chart(monomials, rows, bdry101, 1, 0, 0),
    )
    chart = charts[args.chart]
    values = []
    b0, b1 = map(int, args.b_line.split(","))
    c0, c1 = map(int, args.c_line.split(","))
    def point(x):
        if args.variable == "b":
            return x, args.fixed, args.d4, args.d5
        if args.variable == "c":
            return args.fixed, x, args.d4, args.d5
        if args.variable == "d4":
            return args.b, args.c, x, args.d5
        if args.variable == "d5":
            return args.b, args.c, args.d4, x
        return b0 + b1 * x, c0 + c1 * x, args.d4, args.d5

    for x in range(args.samples):
        b, c, d4, d5 = point(x)
        values.append(fixed_minor_det(
            monomials, rows, chart, b, c, args.prime, d4, d5))
        if (x + 1) % 10 == 0:
            print(f"sample {x + 1}/{args.samples}", file=sys.stderr,
                  flush=True)
    polynomial = interpolate(values, args.prime)
    # Last sample is a holdout whenever the true degree is below samples-1.
    holdout_b, holdout_c, holdout_d4, holdout_d5 = point(args.samples)
    holdout_ok = (args.samples < args.prime and
                  int(polynomial(args.samples)) % args.prime ==
                  fixed_minor_det(monomials, rows, chart,
                                  holdout_b, holdout_c, args.prime,
                                  holdout_d4, holdout_d5))
    print("chart", args.chart, "variable", args.variable,
          "fixed", args.fixed, "prime", args.prime)
    print("degree", polynomial.degree(), "factor", polynomial.factor())
    print("coefficients", polynomial.coeffs())
    print("holdout_ok", holdout_ok)
    print("seconds", round(time.monotonic() - started, 3),
          "rss_kib", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


if __name__ == "__main__":
    main()
