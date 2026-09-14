#!/usr/bin/env python3
"""Two fixed bordered minors in a fully target-gated k=0 chamber.

The profile

    (n,w,A,m,B,s,U,L,k,n0) = (5,2,4,4,2,1,7,7,0,1)

is the minimal one-error/one-Newton-slot promoted-source chamber found with
positive source margin, closed-cap slack, ``U-B >= m+1``, and terminal raw
width strictly exceeding the error count.  After source-safe normalizations
write the one first-extra Newton discrepancy as ``a``, the nonzero error
residual as ``delta``, and the error direction as ``b``.

At X=5, two fixed raw 919-by-919 bordered minors cover every a*delta != 0
over the algebraic closure of F_101.  The first has the exact factorization

    44 delta^44 a^36 (b-4a)^38.

The second is nonzero on its sole projective zero b=4a.  Determinants are
interpolated from the exact grading bound and independently replayed once.
"""

from __future__ import annotations

import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
from higher6810_secondjet_retarget_exact import relaxed_rank_bound  # noqa: E402
import k0_first_newton_two_bordered_cover_6900 as Base  # noqa: E402
import secondjet_candidate_major_function_field_rank_gate_6900 as K0  # noqa: E402


PRIME = 101
PROFILE = K0.Profile(5, 2, 4, 4, 2, 1, 7, 7, 0, 1)
NODES = tuple(range(5))
AGREEMENT = (0, 1, 2, 3)
ERROR = 4
BOUNDARY_X = 5
CHART_REFERENCES = (0, 4)
MONOMIALS = K0.support(PROFILE)

# Populated before forking the interpolation workers.
ROWS = ()
BOUNDARY = None
CHARTS = ()


def coefficient_count() -> int:
    answer = 0
    p = PROFILE
    for sp in range(p.s + 1):
        for rp in range(max(p.B - 2 * sp, 0) + 1):
            budget = (p.m * p.agreements - (p.w - 2) * sp
                      - (p.w - 1) * rp)
            seed_width = p.L + 1 - sp - rp
            ycount = min(max(budget - 1, 0) // p.w + 1,
                         max(p.U + 1 - sp - rp, 0))
            answer += (
                ycount * budget * seed_width
                + p.w * ycount * (ycount - 1) * (2 * ycount - 1) // 6
                - (budget + p.w * seed_width)
                * ycount * (ycount - 1) // 2
            )
    return answer


def contact_columns(a: int, b: int, delta: int):
    u0 = (0, 0, 0, 0, delta % PRIME)
    u1 = (0, 0, 0, a % PRIME, b % PRIME)
    columns = []
    for xp, yp, rp, sp, zp in MONOMIALS:
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


def boundary_matrix():
    return nmod_mat(
        4, len(MONOMIALS),
        [
            pow(BOUNDARY_X, monomial[0], PRIME)
            if sum(monomial[1:]) == 1 and monomial[1:][coordinate] == 1
            else 0
            for coordinate in range(4)
            for monomial in MONOMIALS
        ],
        PRIME,
    )


def chart(reference: int):
    contact = Base.dense(contact_columns(1, reference, 1), ROWS)
    assert contact.rank() == 915
    pivot_columns = Base.independent_columns(contact, 915)
    pivot_rows = Base.independent_columns(
        Base.submatrix(
            contact, tuple(range(contact.nrows())), pivot_columns).transpose(),
        915,
    )
    pivot = Base.submatrix(contact, pivot_rows, pivot_columns)
    assert pivot.det() != 0
    pivot_set = set(pivot_columns)
    nonpivot = tuple(i for i in range(len(MONOMIALS)) if i not in pivot_set)
    coefficients = pivot.inv() * Base.submatrix(contact, pivot_rows, nonpivot)
    schur = (
        Base.submatrix(BOUNDARY, tuple(range(4)), nonpivot)
        - Base.submatrix(BOUNDARY, tuple(range(4)), pivot_columns)
        * coefficients
    )
    assert schur.rank() == 4
    relative_extras = Base.independent_columns(schur, 4)
    extras = tuple(nonpivot[i] for i in relative_extras)
    augmented_columns = pivot_columns + extras

    # Homogeneity in (a,b) follows because every contact coefficient has
    # direction degree output-Z minus source-Z; the Z boundary row has one
    # extra unit of direction degree.  Centered total grade similarly fixes
    # the error-residual degree.
    u1_degree = (
        sum(ROWS[i][1][-1] for i in pivot_rows) + 1
        - sum(MONOMIALS[j][-1] for j in augmented_columns)
    )
    delta_degree = (
        sum(sum(MONOMIALS[j][1:]) for j in augmented_columns)
        - sum(sum(ROWS[i][1][1:]) for i in pivot_rows) - 4
    )
    assert (u1_degree, delta_degree) == (74, 44)
    return {
        "reference": reference,
        "pivot_rows": pivot_rows,
        "pivot_columns": pivot_columns,
        "extras": extras,
        "augmented_columns": augmented_columns,
        "u1_degree": u1_degree,
        "delta_degree": delta_degree,
    }


def raw_bordered_determinant(chart_data, a: int, b: int, delta: int) -> int:
    contact = Base.dense(contact_columns(a, b, delta), ROWS)
    top = Base.submatrix(
        contact, chart_data["pivot_rows"], chart_data["augmented_columns"])
    bottom = Base.submatrix(
        BOUNDARY, tuple(range(4)), chart_data["augmented_columns"])
    size = 919
    matrix = nmod_mat(
        size, size,
        [int(top[i, j]) for i in range(915) for j in range(size)]
        + [int(bottom[i, j]) for i in range(4) for j in range(size)],
        PRIME,
    )
    return int(matrix.det()) % PRIME


def determinant_job(spec):
    chart_index, b = spec
    return chart_index, b, raw_bordered_determinant(
        CHARTS[chart_index], 1, b, 1)


def homogeneous_formula(poly, chart_data, a, b, delta):
    normalized = Base.poly_eval(poly, b * pow(a, -1, PRIME) % PRIME)
    return (normalized * pow(a, chart_data["u1_degree"], PRIME)
            * pow(delta, chart_data["delta_degree"], PRIME)) % PRIME


def digest(values) -> str:
    return hashlib.sha256(repr(tuple(values)).encode()).hexdigest()


def main() -> None:
    global ROWS, BOUNDARY, CHARTS
    started = time.monotonic()
    assert coefficient_count() == len(MONOMIALS) == 1276
    local_rank = relaxed_rank_bound(
        PROFILE.m, PROFILE.L, PROFILE.B, PROFILE.s, PROFILE.U)
    assert (local_rank, PROFILE.n * local_rank) == (183, 915)
    assert len(MONOMIALS) - PROFILE.n * local_rank == 361

    # All target-style profile conditions, including the strict error width.
    assert PROFILE.B == 2 * PROFILE.s
    assert PROFILE.U - PROFILE.B == PROFILE.m + 1
    terminal_width = (PROFILE.m * PROFILE.agreements
                      - PROFILE.w * (PROFILE.B + PROFILE.m + 1))
    assert terminal_width == 2 > PROFILE.n - PROFILE.agreements == 1
    cap_slack = ((PROFILE.m * PROFILE.agreements + PROFILE.B - 1)
                 // PROFILE.w - PROFILE.U)
    assert cap_slack == 1

    base_columns = contact_columns(1, 0, 1)
    ROWS = tuple(sorted(
        set().union(*(set(column) for column in base_columns)), key=repr))
    assert len(ROWS) == 1055
    BOUNDARY = boundary_matrix()
    CHARTS = tuple(chart(reference) for reference in CHART_REFERENCES)
    assert tuple(tuple(MONOMIALS[i] for i in q["extras"])
                 for q in CHARTS) == (
        ((1, 4, 0, 0, 1), (0, 5, 0, 0, 0),
         (10, 1, 1, 0, 0), (15, 0, 0, 1, 0)),
        ((0, 4, 0, 0, 1), (0, 5, 0, 0, 0),
         (10, 1, 1, 0, 0), (15, 0, 0, 1, 0)),
    )

    # Total direction degree is 74, so 75 normalized b-values determine each
    # raw determinant.  Value 75 is an independent replay.
    specs = tuple((i, b) for i in range(2) for b in range(76))
    with mp.get_context("fork").Pool(processes=4) as pool:
        values = tuple(pool.map(determinant_job, specs, chunksize=1))
    grids = [[0] * 76 for _ in range(2)]
    for chart_index, b, value in values:
        grids[chart_index][b] = value
    polynomials = tuple(
        Base.interpolate_prefix(grid[:75]) for grid in grids)
    assert all(Base.poly_eval(polynomials[i], 75) == grids[i][75]
               for i in range(2))

    expected_first = tuple(Base.poly_scale(
        Base.poly_pow([(-4) % PRIME, 1], 38), 44))
    assert polynomials[0] == expected_first
    expected_second = (
        6, 16, 0, 93, 82, 78, 53, 99, 79, 11, 37, 46, 14,
        38, 71, 38, 73, 22, 1, 54, 55, 13, 90, 0, 21, 37,
        63, 63, 72, 8, 0, 26, 31, 7, 36, 61, 58, 4, 39,
    )
    assert polynomials[1] == expected_second
    first_factor = nmod_poly(list(polynomials[0]), PRIME).factor()
    second_factor = nmod_poly(list(polynomials[1]), PRIME).factor()
    assert Base.poly_eval(polynomials[0], 4) == 0
    assert Base.poly_eval(polynomials[1], 4) == 72
    assert nmod_poly(list(polynomials[0]), PRIME).gcd(
        nmod_poly(list(polynomials[1]), PRIME)).degree() == 0

    # Direct non-normalized checks validate both homogeneity exponents rather
    # than relying only on their grading derivation.
    direct_points = ((2, 11, 3), (5, 20, 7), (3, 12, 9))
    direct = []
    for a, b, delta in direct_points:
        actual = tuple(raw_bordered_determinant(q, a, b, delta)
                       for q in CHARTS)
        predicted = tuple(homogeneous_formula(
            polynomials[i], CHARTS[i], a, b, delta) for i in range(2))
        assert actual == predicted
        direct.append((a, b, delta, actual))

    chart_receipts = tuple({
        "reference_b_at_a_delta_one": q["reference"],
        "pivot_rows_sha256": digest(q["pivot_rows"]),
        "pivot_columns_sha256": digest(q["pivot_columns"]),
        "augmented_columns_sha256": digest(q["augmented_columns"]),
        "extra_source_indices": q["extras"],
        "extra_source_monomials": tuple(MONOMIALS[i] for i in q["extras"]),
        "u1_homogeneous_degree": q["u1_degree"],
        "error_residual_degree": q["delta_degree"],
    } for q in CHARTS)

    stable = {
        "scope": (
            "fully target-gated exact-g k0 first-Newton two-bordered-minor "
            "algebraic-closure certificate; not a target theorem"
        ),
        "prime": PRIME,
        "profile_n_w_A_m_B_s_U_L_k_n0": tuple(
            getattr(PROFILE, field) for field in (
                "n", "w", "agreements", "m", "B", "s", "U", "L",
                "k", "n0")),
        "source_columns_localRank_nRank_margin": (
            len(MONOMIALS), local_rank, PROFILE.n * local_rank,
            len(MONOMIALS) - PROFILE.n * local_rank),
        "target_style_gates": {
            "B_equals_2s": True,
            "U_minus_B_equals_m_plus_1": True,
            "terminal_raw_width": terminal_width,
            "errors": PROFILE.n - PROFILE.agreements,
            "closed_cap_slack": cap_slack,
        },
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
            len(MONOMIALS), len(ROWS), local_rank, PROFILE.n * local_rank),
        "charts": chart_receipts,
        "normalized_determinant_coefficients": polynomials,
        "normalized_factorizations": (str(first_factor), str(second_factor)),
        "homogeneous_first_determinant":
            "44*delta^44*a^36*(b-4*a)^38",
        "second_determinant_at_matched_chart_a_delta_one": 72,
        "direct_non_normalized_replays": tuple(direct),
        "conclusion": (
            "For a*delta != 0, D0 can vanish only at b=4*a, where D1 is "
            "nonzero. The two fixed raw minors therefore have no common "
            "algebraic zero. Since contact rank is at most 915, the "
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
            "peak_parent_rss_kib": resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss,
            "peak_child_rss_kib": resource.getrusage(
                resource.RUSAGE_CHILDREN).ru_maxrss,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
