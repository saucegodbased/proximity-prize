#!/usr/bin/env python3
"""Exact algebraic-closure cover for the first k=0 Newton obstruction.

This is deliberately a theorem-directed small chamber, not a random rank
scan.  Work over F_101 with the literal relaxed second-jet source

    (n,w,g,m,B,s,U,L,k,n0) = (5,2,4,3,3,1,4,6,0,1), D = m*g = 12.

After the source-safe degree-two shear, normalize the agreement direction to

    u1(0),u1(1),u1(2),u1(3) = 0,0,0,a.

Thus ``a != 0`` is exactly the first extra Newton/divided-difference
obstruction.  There is one error node, with nonzero value residual ``delta``
and arbitrary direction ``b``.  At the generic boundary point P=gamma=0,
append the four coefficientwise Y,R,S,Z rows to the complete all-node contact
matrix.

Two deterministic fixed raw 609-by-609 bordered minors have formulas

  D0 = -18 delta^22 a^17 (b-4a)^22,

  D1 =  15 delta^22 a^17
          (b-48a)^3 (b-47a)^2 (b-32a) (b-30a)
          (b-3a)^10 (b+23a) (b+25a) (b+37a)^3.

The full agreement interpolant has Q(4)=4a.  Hence D0 is nonzero off the
matched-error chart b=Q(4), and D1 is nonzero on that chart.  Since the
literal contact rank is universally at most 5*121=605, these two raw minors
prove four-coordinate conormal rank four for every a,delta != 0 and every b
in the algebraic closure of F_101.

The determinant identities are recovered from 40 projective samples.  This
is exact because the passive-seed grading makes each raw determinant
homogeneous of u1-degree 39; after a=1 its b-degree is at most 39.  The
centered-total grading independently gives the exact delta exponent 22.
An extra sample is checked, as are direct non-normalized (a,b,delta) values.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat


sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402


PRIME = 101
PROFILE = K0.K0_SMALL
NODES = tuple(range(5))
AGREEMENT = (0, 1, 2, 3)
ERROR = 4
BOUNDARY_X = 5
CHART_REFERENCES = (0, 4)


def contact_columns(monomials, a: int, b: int, delta: int):
    u0 = (0, 0, 0, 0, delta % PRIME)
    u1 = (0, 0, 0, a % PRIME, b % PRIME)
    columns = []
    for xp, yp, rp, sp, zp in monomials:
        column = {}
        for node in NODES:
            expansion = translated_column(
                xp, (yp, rp, sp), zp, node, u0[node], u1[node],
                PROFILE.m, 2, PRIME,
            )
            for term, value in expansion.items():
                if value:
                    column[(node, term)] = value
        columns.append(column)
    return tuple(columns)


def dense(columns, rows):
    return nmod_mat(
        len(rows), len(columns),
        [columns[j].get(rows[i], 0)
         for i in range(len(rows)) for j in range(len(columns))],
        PRIME,
    )


def submatrix(matrix, row_indices, column_indices):
    return nmod_mat(
        len(row_indices), len(column_indices),
        [int(matrix[i, j])
         for i in row_indices for j in column_indices],
        PRIME,
    )


def independent_columns(matrix, count):
    """First ``count`` columns independent in the declared order."""
    basis = {}
    answer = []
    for column in range(matrix.ncols()):
        vector = [int(matrix[row, column]) % PRIME
                  for row in range(matrix.nrows())]
        while any(vector):
            pivot = next(i for i, value in enumerate(vector) if value)
            if pivot not in basis:
                inverse = pow(vector[pivot], -1, PRIME)
                vector = [value * inverse % PRIME for value in vector]
                basis[pivot] = vector
                answer.append(column)
                break
            scale = vector[pivot]
            old = basis[pivot]
            vector = [(x - scale*y) % PRIME
                      for x, y in zip(vector, old)]
        if len(answer) == count:
            return tuple(answer)
    raise AssertionError((len(answer), count))


def boundary_matrix(monomials):
    return nmod_mat(
        4, len(monomials),
        [
            pow(BOUNDARY_X, monomial[0], PRIME)
            if sum(monomial[1:]) == 1 and monomial[1:][coordinate] == 1
            else 0
            for coordinate in range(4)
            for monomial in monomials
        ],
        PRIME,
    )


def poly_add(left, right):
    answer = [0] * max(len(left), len(right))
    for i, value in enumerate(left):
        answer[i] = (answer[i] + value) % PRIME
    for i, value in enumerate(right):
        answer[i] = (answer[i] + value) % PRIME
    while len(answer) > 1 and answer[-1] == 0:
        answer.pop()
    return answer


def poly_mul(left, right):
    answer = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            answer[i + j] = (answer[i + j] + x*y) % PRIME
    while len(answer) > 1 and answer[-1] == 0:
        answer.pop()
    return answer


def poly_pow(base, exponent):
    answer = [1]
    while exponent:
        if exponent & 1:
            answer = poly_mul(answer, base)
        base = poly_mul(base, base)
        exponent //= 2
    return answer


def poly_scale(poly, scalar):
    return [scalar * value % PRIME for value in poly]


def poly_eval(poly, x):
    answer = 0
    for coefficient in reversed(poly):
        answer = (answer*x + coefficient) % PRIME
    return answer


def interpolate_prefix(values):
    """Interpolate values at x=0,...,len(values)-1 over F_101."""
    answer = [0]
    for x, value in enumerate(values):
        basis = [1]
        denominator = 1
        for other in range(len(values)):
            if other == x:
                continue
            basis = poly_mul(basis, [(-other) % PRIME, 1])
            denominator = denominator * (x - other) % PRIME
        answer = poly_add(
            answer,
            poly_scale(basis, value * pow(denominator, -1, PRIME)),
        )
    return tuple(answer)


def expected_chart_polynomials():
    first = poly_scale(poly_pow([(-4) % PRIME, 1], 22), -18)
    second = [15]
    for root, multiplicity in (
        (48, 3), (47, 2), (32, 1), (30, 1), (3, 10),
        (-23, 1), (-25, 1), (-37, 3),
    ):
        second = poly_mul(
            second, poly_pow([(-root) % PRIME, 1], multiplicity))
    return tuple(first), tuple(second)


def chart(monomials, rows, boundary, reference):
    contact = dense(contact_columns(monomials, 1, reference, 1), rows)
    assert contact.rank() == 605
    pivot_columns = independent_columns(contact, 605)
    pivot_rows = independent_columns(
        submatrix(contact, tuple(range(contact.nrows())), pivot_columns)
        .transpose(),
        605,
    )
    pivot = submatrix(contact, pivot_rows, pivot_columns)
    assert pivot.det() != 0
    nonpivot = tuple(i for i in range(len(monomials))
                     if i not in set(pivot_columns))
    coefficients = pivot.inv() * submatrix(contact, pivot_rows, nonpivot)
    schur = (
        submatrix(boundary, tuple(range(4)), nonpivot)
        - submatrix(boundary, tuple(range(4)), pivot_columns) * coefficients
    )
    assert schur.rank() == 4
    relative_extras = independent_columns(schur, 4)
    extras = tuple(nonpivot[i] for i in relative_extras)
    augmented_columns = pivot_columns + extras

    # For every contact entry, the u1 degree is output-Z minus source-Z.
    # Boundary Y/R/S rows have grading zero and boundary Z has grading one.
    u1_degree = (
        sum(rows[i][1][-1] for i in pivot_rows) + 1
        - sum(monomials[j][-1] for j in augmented_columns)
    )

    # The passive total-grade identity says that the exponent of the unique
    # nonzero error residual delta is source grade minus output grade.  Give
    # each boundary derivative row artificial grade one, because it lowers a
    # linear source monomial to a scalar without using delta.
    delta_degree = (
        sum(sum(monomials[j][1:]) for j in augmented_columns)
        - sum(sum(rows[i][1][1:]) for i in pivot_rows) - 4
    )
    assert (u1_degree, delta_degree) == (39, 22)
    return {
        "reference": reference,
        "pivot_rows": pivot_rows,
        "pivot_columns": pivot_columns,
        "extras": extras,
        "augmented_columns": augmented_columns,
        "u1_degree": u1_degree,
        "delta_degree": delta_degree,
    }


def raw_bordered_determinant(
        monomials, rows, boundary, chart_data, a, b, delta):
    contact = dense(contact_columns(monomials, a, b, delta), rows)
    top = submatrix(
        contact, chart_data["pivot_rows"], chart_data["augmented_columns"])
    bottom = submatrix(
        boundary, tuple(range(4)), chart_data["augmented_columns"])
    matrix = nmod_mat(
        609, 609,
        [int(top[i, j]) for i in range(605) for j in range(609)]
        + [int(bottom[i, j]) for i in range(4) for j in range(609)],
        PRIME,
    )
    return int(matrix.det()) % PRIME


def homogeneous_formula(normalized, a, b, delta):
    # normalized has total u1 degree 39 and b degree 22, hence a degree 17.
    value = poly_eval(normalized, b * pow(a, -1, PRIME) % PRIME)
    return value * pow(a, 39, PRIME) * pow(delta, 22, PRIME) % PRIME


def digest(values):
    return hashlib.sha256(repr(tuple(values)).encode()).hexdigest()


def main():
    started = time.monotonic()
    monomials = K0.support(PROFILE)
    assert len(monomials) == 815
    assert relaxed_rank_bound(
        PROFILE.m, PROFILE.L, PROFILE.B, PROFILE.s, PROFILE.U) == 121

    base_columns = contact_columns(monomials, 1, 0, 1)
    rows = tuple(sorted(
        set().union(*(set(column) for column in base_columns)), key=repr))
    assert len(rows) == 625
    boundary = boundary_matrix(monomials)
    charts = tuple(
        chart(monomials, rows, boundary, reference)
        for reference in CHART_REFERENCES
    )
    assert tuple(tuple(monomials[i] for i in q["extras"]) for q in charts) == (
        ((1, 3, 0, 0, 1), (0, 4, 0, 0, 0),
         (10, 0, 1, 0, 0), (10, 0, 0, 1, 0)),
        ((0, 3, 0, 0, 1), (0, 4, 0, 0, 0),
         (10, 0, 1, 0, 0), (10, 0, 0, 1, 0)),
    )

    # Degree <=39 follows from the exact u1 grading.  Forty projective values
    # therefore determine each normalized raw determinant; x=40 is an
    # independent replay check.
    values = [[], []]
    for b in range(41):
        for i, chart_data in enumerate(charts):
            values[i].append(raw_bordered_determinant(
                monomials, rows, boundary, chart_data, 1, b, 1))
    interpolated = tuple(
        interpolate_prefix(chart_values[:40]) for chart_values in values)
    expected = expected_chart_polynomials()
    assert interpolated == expected
    assert all(poly_eval(interpolated[i], 40) == values[i][40]
               for i in range(2))

    # The first determinant's only projective root is b=4.  The second one is
    # nonzero there, so their projective zero loci are disjoint.
    assert poly_eval(expected[0], 4) == 0
    assert poly_eval(expected[1], 4) == 66

    # Directly replay several non-normalized points against the bihomogeneous
    # formulas, including both the matched chart and a root of the first.
    direct_points = ((2, 14, 3), (5, 4, 7), (3, 12, 9), (1, 4, 1))
    direct = []
    for a, b, delta in direct_points:
        actual = tuple(raw_bordered_determinant(
            monomials, rows, boundary, chart_data, a, b, delta)
            for chart_data in charts)
        predicted = tuple(homogeneous_formula(poly, a, b, delta)
                          for poly in expected)
        assert actual == predicted
        direct.append((a, b, delta, actual))

    # Lagrange interpolation on 0,1,2 gives q=0.  The unique interpolation of
    # (0,0,0,a) on 0,1,2,3 is a*X(X-1)(X-2)/6, hence Q(4)=4a.
    inverse_six = pow(6, -1, PRIME)
    q_coefficients_at_a_one = (
        0, 2 * inverse_six % PRIME, -3 * inverse_six % PRIME, inverse_six)
    assert q_coefficients_at_a_one == (0, 34, 50, 17)
    assert poly_eval(q_coefficients_at_a_one, 4) == 4

    chart_receipts = []
    for chart_data in charts:
        chart_receipts.append({
            "reference_b_at_a_delta_one": chart_data["reference"],
            "pivot_rows_sha256": digest(chart_data["pivot_rows"]),
            "pivot_columns_sha256": digest(chart_data["pivot_columns"]),
            "augmented_columns_sha256": digest(
                chart_data["augmented_columns"]),
            "extra_source_indices": chart_data["extras"],
            "extra_source_monomials": tuple(
                monomials[i] for i in chart_data["extras"]),
            "u1_homogeneous_degree": chart_data["u1_degree"],
            "error_residual_degree": chart_data["delta_degree"],
        })

    stable = {
        "scope": (
            "exact-g full-cutoff k0 first-Newton two-raw-bordered-minor "
            "algebraic-closure certificate; not a target theorem"
        ),
        "prime": PRIME,
        "profile_n_w_g_m_B_s_U_L_k_n0": tuple(
            getattr(PROFILE, field) for field in (
                "n", "w", "agreements", "m", "B", "s", "U", "L",
                "k", "n0")),
        "normalization": {
            "nodes": NODES,
            "agreement": AGREEMENT,
            "error": ERROR,
            "u0": "(0,0,0,0,delta), delta != 0",
            "u1": "(0,0,0,a,b), a != 0",
            "first_extra_Newton_slot": "a",
            "agreement_interpolant_at_error": "Q(4)=4*a",
            "boundary_specialization_X": BOUNDARY_X,
        },
        "source_columns_contact_rows_local_rank_global_cap": (
            len(monomials), len(rows), 121, 605),
        "charts": tuple(chart_receipts),
        "normalized_determinant_coefficients": interpolated,
        "determinant_factorizations": (
            "-18*delta^22*a^17*(b-4*a)^22",
            "15*delta^22*a^17*(b-48*a)^3*(b-47*a)^2*"
            "(b-32*a)*(b-30*a)*(b-3*a)^10*(b+23*a)*"
            "(b+25*a)*(b+37*a)^3",
        ),
        "second_determinant_at_matched_chart_a_delta_one": 66,
        "direct_non_normalized_replays": tuple(direct),
        "conclusion": (
            "For a*delta != 0, the two fixed raw augmented minors have no "
            "common algebraic zero in b. Since contact rank <=605, the "
            "complete-kernel YRSZ conormal rank is four."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    result = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
