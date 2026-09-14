#!/usr/bin/env python3
"""Deterministic two-error rank-adaptivity gate for exact-g k=0.

The complete conormal gains four ranks in five theorem-directed mismatch
patterns, but the old contact rank itself varies.  Consequently a proof based
on one fixed maximal-contact bordered minor cannot be uniform even in this
first two-error chamber.  This does not claim the target rank theorem.
"""

from __future__ import annotations

import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


P = 101
PROFILE = K0.Profile(6, 2, 4, 3, 3, 1, 4, 6, 0, 1)
NODES = tuple(range(6))
AGREEMENT = tuple(range(4))
BOUNDARY_X = 6


def columns(monomials, a, b, c, d4=1, d5=1):
    u0 = (0, 0, 0, 0, d4 % P, d5 % P)
    u1 = (0, 0, 0, a % P, b % P, c % P)
    answer = []
    for xp, yp, rp, sp, zp in monomials:
        column = {}
        for node in NODES:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                PROFILE.m, 2, P,
            )
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        answer.append(column)
    return tuple(answer)


def dense(sparse_columns, rows):
    return nmod_mat(
        len(rows), len(sparse_columns),
        [sparse_columns[j].get(rows[i], 0)
         for i in range(len(rows)) for j in range(len(sparse_columns))], P,
    )


def submatrix(matrix, row_indices, column_indices):
    return nmod_mat(
        len(row_indices), len(column_indices),
        [int(matrix[i, j])
         for i in row_indices for j in column_indices], P,
    )


def independent_columns(matrix, count):
    basis = {}
    answer = []
    for column in range(matrix.ncols()):
        vector = [int(matrix[row, column]) % P
                  for row in range(matrix.nrows())]
        while any(vector):
            pivot = next(i for i, value in enumerate(vector) if value)
            if pivot not in basis:
                inverse = pow(vector[pivot], -1, P)
                vector = [value * inverse % P for value in vector]
                basis[pivot] = vector
                answer.append(column)
                break
            scale = vector[pivot]
            old = basis[pivot]
            vector = [(x - scale*y) % P for x, y in zip(vector, old)]
        if len(answer) == count:
            return tuple(answer)
    raise AssertionError((len(answer), count))


def boundary(monomials):
    return nmod_mat(
        4, len(monomials),
        [
            pow(BOUNDARY_X, monomial[0], P)
            if sum(monomial[1:]) == 1 and monomial[1:][coordinate] == 1
            else 0
            for coordinate in range(4)
            for monomial in monomials
        ], P,
    )


def extract_chart(monomials, rows, bdry, a, b, c):
    contact = dense(columns(monomials, a, b, c), rows)
    cap = len(NODES) * relaxed_rank_bound(
        PROFILE.m, PROFILE.L, PROFILE.B, PROFILE.s, PROFILE.U)
    actual_rank = contact.rank()
    print("contact rank", actual_rank, "sum cap", cap)
    cap = actual_rank
    pivcols = independent_columns(contact, cap)
    pivrows = independent_columns(
        submatrix(contact, tuple(range(contact.nrows())), pivcols).transpose(),
        cap,
    )
    pivot = submatrix(contact, pivrows, pivcols)
    nonpivot = tuple(i for i in range(len(monomials)) if i not in set(pivcols))
    schur = (
        submatrix(bdry, tuple(range(4)), nonpivot)
        - submatrix(bdry, tuple(range(4)), pivcols)
        * (pivot.inv() * submatrix(contact, pivrows, nonpivot))
    )
    extras = tuple(nonpivot[i] for i in independent_columns(schur, 4))
    return pivrows, pivcols, extras


def seed_degree(monomials, rows, chart):
    pivrows, pivcols, extras = chart
    chosen = pivcols + extras
    return (sum(rows[i][1][-1] for i in pivrows) + 1
            - sum(monomials[j][-1] for j in chosen))


def bordered_rank(monomials, rows, bdry, chart, a, b, c):
    pivrows, pivcols, extras = chart
    chosen = pivcols + extras
    contact = dense(columns(monomials, a, b, c), rows)
    top = submatrix(contact, pivrows, chosen)
    bottom = submatrix(bdry, tuple(range(4)), chosen)
    matrix = nmod_mat(
        top.nrows() + 4, top.ncols(),
        [int(top[i, j]) for i in range(top.nrows()) for j in range(top.ncols())]
        + [int(bottom[i, j]) for i in range(4) for j in range(bottom.ncols())],
        P,
    )
    return matrix.rank(), int(matrix.det())


def full_increment(monomials, rows, bdry, a, b, c):
    contact = dense(columns(monomials, a, b, c), rows)
    stacked = nmod_mat(
        contact.nrows() + 4, contact.ncols(),
        [int(contact[i, j])
         for i in range(contact.nrows()) for j in range(contact.ncols())]
        + [int(bdry[i, j])
           for i in range(4) for j in range(bdry.ncols())],
        P,
    )
    cr = contact.rank()
    ar = stacked.rank()
    return cr, ar, ar - cr


def main():
    started = time.monotonic()
    monomials = K0.support(PROFILE)
    assert len(monomials) == 815
    sparse = columns(monomials, 1, 4, 10)
    rows = tuple(sorted(set().union(*(set(c) for c in sparse)), key=repr))
    bdry = boundary(monomials)
    charts = (
        extract_chart(monomials, rows, bdry, 1, 4, 10),
        extract_chart(monomials, rows, bdry, 1, 0, 10),
        extract_chart(monomials, rows, bdry, 1, 4, 0),
    )
    cases = (
        ("matched", 4, 10),
        ("first_mismatch", 0, 10),
        ("second_mismatch", 4, 0),
        ("both_mismatch", 0, 0),
        ("generic", 7, 13),
    )
    full = tuple(
        (label, full_increment(monomials, rows, bdry, 1, b, c))
        for label, b, c in cases
    )
    assert full == (
        ("matched", (724, 728, 4)),
        ("first_mismatch", (726, 730, 4)),
        ("second_mismatch", (726, 730, 4)),
        ("both_mismatch", (722, 726, 4)),
        ("generic", (724, 728, 4)),
    )
    expected_extras = (
        ((7, 1, 1, 0, 0), (6, 1, 1, 0, 1),
         (7, 1, 1, 0, 1), (6, 1, 0, 1, 0)),
        ((8, 1, 1, 0, 0), (7, 1, 1, 0, 1),
         (8, 1, 1, 0, 1), (6, 1, 0, 1, 0)),
        ((8, 1, 1, 0, 0), (7, 1, 1, 0, 1),
         (8, 1, 1, 0, 1), (6, 1, 0, 1, 0)),
    )
    expected_seed_degrees = (93, 103, 103)
    expected_bordered = (
        ((728, 78), (728, 5), (728, 52), (724, 0), (728, 38)),
        ((723, 0), (730, 95), (730, 9), (723, 0), (726, 0)),
        ((723, 0), (730, 95), (730, 9), (723, 0), (726, 0)),
    )
    print("source", len(monomials), "rows", len(rows))
    for item in full:
        print("full", *item)
    for ci, chart in enumerate(charts):
        degree = seed_degree(monomials, rows, chart)
        extras = tuple(monomials[i] for i in chart[2])
        bordered = tuple(
            bordered_rank(monomials, rows, bdry, chart, 1, b, c)
            for _, b, c in cases
        )
        assert degree == expected_seed_degrees[ci]
        assert extras == expected_extras[ci]
        assert bordered == expected_bordered[ci]
        print("chart", ci, "seed_degree", degree, "extras", extras)
        for (label, _, _), result in zip(cases, bordered):
            print(ci, label, result)
    print("rss_kib", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    print("elapsed", round(time.monotonic() - started, 3))


if __name__ == "__main__":
    main()
