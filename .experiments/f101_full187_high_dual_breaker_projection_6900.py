#!/usr/bin/env python3
"""Exact dual quotient of the Full187 high block in the F101 Xi^2 control.

This is deliberately complementary to the low-group delta minimizer.  Rather
than searching for a primal relay, it isolates the three-dimensional part of
the left nullspace of the boundary-degree-at-least-two block which sees the
three prescribed locator RHS.  It then projects every omitted boundary-zero
or boundary-one literal column through those three functionals.

The result is a small, exact necessary-condition receipt.  It is not a target
theorem and does not claim that the three direct breaker columns solve the
remaining contact equations.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
import resource
import sys

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402


NAMES = ("F0", "F1", "F2")
PRIMARY = (11, 5, 8, 4, 32, 1, 1, 6, 10)


def boundary_degree(monomial):
    return sum(monomial[1:4])


def pair(functional, column):
    return sum(coefficient * column.get(row, 0)
               for row, coefficient in functional.items()) % M.PRIME


def vector_rank(vectors):
    """Rank of a short list of vectors over F_101, with no dense matrix."""
    pivots = {}
    for vector in vectors:
        work = {i: value % M.PRIME for i, value in enumerate(vector)
                if value % M.PRIME}
        while work:
            pivot = min(work)
            old = pivots.get(pivot)
            if old is None:
                inverse = pow(work[pivot], -1, M.PRIME)
                pivots[pivot] = {
                    i: value * inverse % M.PRIME
                    for i, value in work.items()
                    if value * inverse % M.PRIME
                }
                break
            scale = work[pivot]
            for i, value in old.items():
                replacement = (work.get(i, 0) - scale * value) % M.PRIME
                if replacement:
                    work[i] = replacement
                else:
                    work.pop(i, None)
    return len(pivots)


def x_range(source, shape):
    exponents = sorted(monomial[0] for monomial in source
                       if monomial[1:4] == shape)
    return (exponents[0], exponents[-1], len(exponents)) if exponents else None


def contact_summary(literal, source, source_index):
    image = {}
    for monomial, coefficient in source.items():
        for row, value in literal.columns[source_index[monomial]].items():
            if literal.row_keys[row][0] != "C":
                continue
            replacement = (image.get(row, 0) + coefficient * value) % M.PRIME
            if replacement:
                image[row] = replacement
            else:
                image.pop(row, None)
    assert not any(literal.row_keys[row][1] in literal.anchor_agreement
                   for row in image)
    by_node = Counter(literal.row_keys[row][1] for row in image)
    by_seed = Counter(literal.row_keys[row][2][-1] for row in image)
    return {
        "contact_support": len(image),
        "contact_support_by_error_node": tuple(sorted(by_node.items())),
        "contact_output_seed_histogram": tuple(sorted(by_seed.items())),
    }


def normal_low_summary(literal, source, source_index):
    assert all((boundary_degree(monomial), monomial[-1]) in ((0, 1), (1, 0))
               for monomial in source)
    head = {monomial: coefficient for monomial, coefficient in source.items()
            if boundary_degree(monomial) == 1 and monomial[-1] == 0}
    tail = {monomial: coefficient for monomial, coefficient in source.items()
            if boundary_degree(monomial) == 0 and monomial[-1] == 1}
    return {
        "source_support": len(source),
        "forced_J_head_boundary1_seed0_support": len(head),
        "centered_seed1_boundary0_tail_support": len(tail),
        "X_ranges_by_Y_R_S_Z_shape": {
            "Y": x_range(source, (1, 0, 0)),
            "R": x_range(source, (0, 1, 0)),
            "S": x_range(source, (0, 0, 1)),
            "Z": x_range(source, (0, 0, 0)),
        },
        "error_contact_residual_after_agreement_zero": contact_summary(
            literal, source, source_index),
    }


def main():
    M.T.PRIME = M.F.PRIME = M.PRIME
    literal = M.build_case("primary_n11", PRIMARY, 8, 8, 3)
    source_index = {monomial: i for i, monomial in enumerate(literal.monomials)}
    row_index = {row: i for i, row in enumerate(literal.row_keys)}

    # The three rows are deliberately all Y rows.  In ascending X order the
    # locator RHS have the Hasse-valuation triangular block shown below.
    y_rows = tuple(row_index[("J", 0, exponent)] for exponent in (1, 2, 3))
    taylor_block = tuple(
        tuple(target.get(row, 0) for target in literal.targets)
        for row in y_rows)
    assert taylor_block == ((0, 0, 81), (0, 10, 92), (91, 55, 29))

    # Rows of the inverse block: lambda_i(F_j)=delta_ij.  These functionals
    # have no C support at all, hence annihilate every high source column.
    dual_coefficients = ((14, 46, 10), (55, 91, 0), (5, 0, 0))
    duals = tuple({row: coefficient for row, coefficient in zip(y_rows, values)
                   if coefficient}
                  for values in dual_coefficients)
    dual_pairings = tuple(tuple(pair(dual, target) for target in literal.targets)
                          for dual in duals)
    assert dual_pairings == ((1, 0, 0), (0, 1, 0), (0, 0, 1))

    high_indices = [i for i, monomial in enumerate(literal.monomials)
                    if boundary_degree(monomial) >= 2]
    assert all(all(literal.row_keys[row][0] != "J"
                   for row in literal.columns[i])
               for i in high_indices)
    assert all(pair(dual, literal.columns[i]) == 0
               for dual in duals for i in high_indices)

    low_indices = [i for i, monomial in enumerate(literal.monomials)
                   if boundary_degree(monomial) <= 1]
    low_by_boundary = Counter(boundary_degree(literal.monomials[i])
                              for i in low_indices)
    low_by_boundary_seed = Counter(
        (boundary_degree(literal.monomials[i]), literal.monomials[i][-1])
        for i in low_indices)
    projected = {
        literal.monomials[i]: tuple(pair(dual, literal.columns[i])
                                    for dual in duals)
        for i in low_indices
    }
    active = {monomial: value for monomial, value in projected.items()
              if any(value)}
    expected_active = {
        (1, 1, 0, 0, 0): (14, 55, 5),
        (2, 1, 0, 0, 0): (46, 91, 0),
        (3, 1, 0, 0, 0): (10, 0, 0),
    }
    assert active == expected_active
    assert vector_rank(tuple(active.values())) == 3
    assert all(vector_rank(tuple(values)) < 3
               for omitted in active
               for values in (tuple(value for monomial, value in active.items()
                                    if monomial != omitted),))

    # Crucially, this is only a three-coordinate probe of the full normal
    # quotient.  The three active columns do not lower the actual bordered
    # defect: a shifted Y/R/S triangular block is disjoint from their J
    # support and supplies a new identity-pairing dual triple.
    shifted_rows = (
        row_index[("J", 0, 4)],
        row_index[("J", 1, 3)],
        row_index[("J", 2, 3)],
    )
    shifted_block = tuple(
        tuple(target.get(row, 0) for target in literal.targets)
        for row in shifted_rows)
    assert shifted_block == ((85, 94, 55), (0, 91, 9), (0, 0, 91))
    shifted_dual_coefficients = ((82, 84, 62), (0, 10, 9), (0, 0, 10))
    shifted_duals = tuple({row: coefficient
                           for row, coefficient in zip(shifted_rows, values)
                           if coefficient}
                          for values in shifted_dual_coefficients)
    assert tuple(tuple(pair(dual, target) for target in literal.targets)
                 for dual in shifted_duals) == ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    direct_indices = tuple(source_index[monomial] for monomial in active)
    assert all(pair(dual, literal.columns[i]) == 0
               for dual in shifted_duals for i in direct_indices)

    # At J level, each target has a forced, unique boundary-one/seed-zero
    # head: no high column and no seed-positive/degree-zero column has a J
    # coordinate.  The union is a useful exact lower bound for a full relay.
    heads = []
    for source, target in zip(literal.locator_normals, literal.targets):
        head = {monomial: coefficient for monomial, coefficient in source.items()
                if boundary_degree(monomial) == 1 and monomial[-1] == 0}
        rebuilt = {}
        for monomial, coefficient in head.items():
            xp, yp, rp, sp, zp = monomial
            coordinate = ((yp, rp, sp, zp).index(1))
            row = row_index[("J", coordinate, xp)]
            rebuilt[row] = coefficient
        assert rebuilt == target
        heads.append(head)
    assert tuple(map(len, heads)) == (22, 44, 66)
    head_union = set().union(*heads)
    assert len(head_union) == 69

    # The initial terms are predicted directly from Lambda=X*(10+39X+...).
    # F2_Y has order one, F1_Y order two, and F0_Y order three at X=0.
    lambda_initial = literal.locator[:4]
    assert lambda_initial == (0, 10, 39, 99)
    y_valuations = []
    for target in literal.targets:
        exponents = [literal.row_keys[row][2] for row, coefficient in target.items()
                     if coefficient and literal.row_keys[row][:2] == ("J", 0)]
        y_valuations.append(min(exponents))
    assert tuple(y_valuations) == (3, 2, 1)

    payload = {
        "scope": (
            "exact F101 Xi^2 high-block dual quotient and omitted-low-column "
            "projection; complementary to primal relay minimization; not a "
            "target theorem"
        ),
        "field": M.PRIME,
        "parameters_n_w_A_m_D_s_t_J_L": literal.parameters,
        "high_source_predicate": "boundary degree Y+R+S >= 2",
        "source_column_partition": {
            "all": len(literal.monomials),
            "high_boundary_at_least_2": len(high_indices),
            "omitted_boundary_0_or_1": len(low_indices),
            "omitted_by_boundary_degree": tuple(sorted(low_by_boundary.items())),
            "omitted_by_boundary_degree_and_seed": tuple(
                sorted((boundary, seed, count)
                       for (boundary, seed), count in low_by_boundary_seed.items())),
        },
        "locator_polynomial_coefficients_X_0_through_X_3": lambda_initial,
        "Y_coefficient_Hasse_valuations_of_F0_F1_F2": tuple(y_valuations),
        "Y_rows_X_1_X_2_X_3_by_F0_F1_F2": taylor_block,
        "dual_obstructions": tuple({
            "normal": name,
            "support_J_Y_X_coefficients": tuple(
                (exponent, coefficient)
                for exponent, coefficient in zip((1, 2, 3), values)
                if coefficient),
            "pairs_with_F0_F1_F2": dual_pairings[index],
        } for index, (name, values) in enumerate(zip(NAMES, dual_coefficients))),
        "exact_high_only_joint_defect": {
            "value": 3,
            "reason": (
                "three left-null functionals annihilate every high column and "
                "pair identically with F0,F1,F2; three RHS give the matching "
                "upper bound"
            ),
        },
        "omitted_low_projection_to_the_three_duals": {
            "rank": 3,
            "nonzero_columns_exactly": tuple(sorted(
                (monomial, value) for monomial, value in active.items())),
            "minimal_direct_breaker": {
                "columns": tuple(sorted(active)),
                "proof": (
                    "these are the only nonzero projected omitted columns and "
                    "their three vectors have rank three; deleting any one has "
                    "rank at most two"
                ),
            },
            "all_boundary_degree_0_columns_project_to_zero": True,
            "all_boundary_degree_1_columns_except_the_three_listed_project_to_zero": True,
        },
        "the_three_direct_columns_do_not_lower_full_joint_defect": {
            "joint_defect_after_adding_them": 3,
            "replacement_J_rows_Y4_R3_S3_by_F0_F1_F2": shifted_block,
            "replacement_dual_obstructions": tuple({
                "normal": name,
                "support_J_row_coefficients": tuple(
                    (literal.row_keys[row], coefficient)
                    for row, coefficient in zip(shifted_rows, values)
                    if coefficient),
            } for name, values in zip(NAMES, shifted_dual_coefficients)),
            "reason": (
                "the replacement duals annihilate both H and X*Y,X^2*Y,X^3*Y "
                "and pair identically with F0,F1,F2"
            ),
        },
        "forced_exact_J_heads": {
            "support_F0_F1_F2": tuple(map(len, heads)),
            "union_support": len(head_union),
            "reason": (
                "J is carried only by boundary-one, seed-zero source monomials; "
                "the requested J coordinate fixes each such coefficient"
            ),
        },
        "canonical_centered_low_completions": tuple({
            "normal": name,
            **normal_low_summary(literal, source, source_index),
        } for name, source in zip(NAMES, literal.locator_normals)),
        "interpretation": (
            "The three X,Y singleton columns only break the initially chosen "
            "three-coordinate probe; an exact shifted dual triple proves that "
            "the full bordered defect remains three. The full J heads are "
            "forced, and their error contacts then require an indirect "
            "low/high relay. Boundary-zero columns are invisible to every J "
            "coordinate, so any useful such column must operate by cancelling "
            "that residual contact rather than by directly breaking a "
            "locator-normal obstruction."
        ),
        "maximum_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
