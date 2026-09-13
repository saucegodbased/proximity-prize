#!/usr/bin/env python3
"""Exact affine-gauge audit for the n=10 (3,5,7) direction offset.

The earlier countergate inspected the particular lift returned by FLINT's
nullspace basis.  Here we retain the entire contact-kernel affine fibre and
ask the invariant question: is *some* lift of each of F0,F1,F2 in the old
three-carrier centered subspace?  We test both the old center Q=Xi^2 and the
unique all-node direction interpolant P=Q+Lambda*h.

All calculations are over F_101 and use only the fixed matched and offset
chambers declared by the previous receipts.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations
import hashlib
import json
from math import comb
from pathlib import Path

from flint import nmod_mat, nmod_poly

import f101_o2_bordered_filtration_mechanism_6900 as M
import f101_n10_grade7_centered_wronskian_universality_6900 as U


PRIME = 101
CASE = (10, 4, 7, 4, 28, 1, 1, 6, 10)
OFFSETS = (3, 5, 7)


def add_entry(column, row, coefficient):
    coefficient = int(coefficient) % PRIME
    if not coefficient:
        return
    value = (column.get(row, 0) + coefficient) % PRIME
    if value:
        column[row] = value
    else:
        column.pop(row, None)


def add_poly(column, family, poly, scale=1):
    for exponent in range(poly.degree() + 1):
        add_entry(column, (family, exponent), scale * int(poly[exponent]))


def monomial_poly(exponent):
    return nmod_poly([0] * exponent + [1], PRIME)


def all_node_center(literal):
    """P=Q+Lambda*h matching the three prescribed error directions."""
    q = nmod_poly(list(literal.q), PRIME)
    locator = nmod_poly(list(literal.locator), PRIME)
    nodes = tuple(range(7, 10))
    h_values = tuple(
        OFFSETS[index] * pow(int(locator(node)), -1, PRIME) % PRIME
        for index, node in enumerate(nodes))
    h = nmod_poly(list(M.T.interpolate(h_values, nodes)), PRIME)
    p = q + locator * h
    assert all(int(p(node)) % PRIME == int(q(node)) % PRIME
               for node in range(7))
    assert all(int(p(node)) % PRIME == OFFSETS[node - 7]
               for node in nodes)
    return h, p


def contact_kernel(literal, indices):
    contact_rows = tuple(index for index, row in enumerate(literal.row_keys)
                         if row[0] == "C")
    contact = U.matrix_from_columns(contact_rows, literal.columns, indices)
    raw_kernel, nullity = contact.nullspace()
    kernel = nmod_mat(raw_kernel.nrows(), nullity, [
        int(raw_kernel[row, column])
        for row in range(raw_kernel.nrows())
        for column in range(nullity)
    ], PRIME)
    return contact, kernel, nullity


def centered_condition_column(monomial, center):
    """Linear shell conditions for the old three-carrier normal form.

    A and C are added as separate columns below.  A source column contributes
    here to T0,T1,T2,H0,H1,H2,H3 or to a forbidden raw shape.
    """
    xp, y, r, s, z = monomial
    if y + r + s + z != 7:
        return {}
    shape = (y, r, s, z)
    if shape not in U.EXPECTED_SHAPES:
        return {(("forbidden", shape), xp): 1}
    xmon = monomial_poly(xp)
    out = {}
    if r == 1:
        assert s == 0 and z == 6 - y and y <= 2
        for power in range(y + 1):
            contribution = comb(y, power) * xmon * center ** (y - power)
            add_poly(out, "T" + str(power), contribution)
    else:
        assert r == 0 and s == 0 and z == 7 - y and y <= 4
        for power in range(y + 1):
            contribution = comb(y, power) * xmon * center ** (y - power)
            add_poly(out, "H" + str(power), contribution)
    # H4 is the free c-carrier and hence carries no equation.
    return {row: coefficient for row, coefficient in out.items()
            if row[0] != "H4"}


def carrier_columns(literal, center):
    xi = nmod_poly(list(literal.xi), PRIME)
    locator = nmod_poly(list(literal.locator), PRIME)
    lp = locator.derivative()
    cp = center.derivative()
    columns = []
    labels = []
    # Conditions are T2=A Lambda Xi, H2=-A Xi Lambda P', and
    # H3=C Lambda-A Xi Lambda'.  Move their right sides to the left.
    # T2 is the raw Y^2*R*Z^4 coefficient, of degree at most 16, while
    # deg(Lambda*Xi)=10.  Hence deg A <= 6 is sharp, not a search cutoff.
    max_a_degree = 6
    # H3=G3+4*P*G4.  The raw caps are deg G3<=15, deg G4<=11.
    # Division by the degree-seven Lambda gives the following sharp cap.
    max_c_degree = max(15, center.degree() + 11) - 7
    for exponent in range(max_a_degree + 1):
        mon = monomial_poly(exponent)
        column = {}
        add_poly(column, "T2", mon * locator * xi, -1)
        add_poly(column, "H2", mon * xi * locator * cp, 1)
        add_poly(column, "H3", mon * xi * lp, 1)
        columns.append(column)
        labels.append(("A", exponent))
    # H3 + A Xi Lambda' - Lambda C = 0.
    for exponent in range(max_c_degree + 1):
        column = {}
        add_poly(column, "H3", monomial_poly(exponent) * locator, -1)
        columns.append(column)
        labels.append(("C", exponent))
    return columns, labels


def sparse_times_kernel(source_columns, kernel, extra_rows=()):
    row_keys = sorted(
        {row for column in source_columns for row in column} | set(extra_rows),
        key=repr)
    row_index = {row: index for index, row in enumerate(row_keys)}
    dense = nmod_mat(len(row_keys), kernel.nrows(), [
        source_columns[column].get(row, 0)
        for row in row_keys
        for column in range(kernel.nrows())
    ], PRIME)
    return row_keys, dense * kernel


def solve_centered(literal, center):
    indices = U.restricted_indices(literal)
    contact, kernel, nullity = contact_kernel(literal, indices)
    source_conditions = tuple(
        centered_condition_column(literal.monomials[index], center)
        for index in indices)
    extra_columns, extra_labels = carrier_columns(literal, center)
    condition_rows, condition_image = sparse_times_kernel(
        source_conditions, kernel,
        {row for column in extra_columns for row in column})

    j_rows = tuple(sorted(
        {index for source_index in indices
         for index in literal.columns[source_index]
         if literal.row_keys[index][0] == "J"}
        | {index for target in literal.targets[:3] for index in target}))
    j_matrix = U.matrix_from_columns(j_rows, literal.columns, indices)
    j_image = j_matrix * kernel
    j_index = {row: index for index, row in enumerate(j_rows)}
    condition_index = {row: index for index, row in enumerate(condition_rows)}

    # Assemble [J*K,0; conditions*K, carrier parameters].
    rows = len(j_rows) + len(condition_rows)
    variables = nullity + len(extra_columns)
    flat = [0] * (rows * variables)
    for row in range(len(j_rows)):
        for column in range(nullity):
            flat[row * variables + column] = int(j_image[row, column])
    for local_row, key in enumerate(condition_rows):
        row = len(j_rows) + local_row
        for column in range(nullity):
            flat[row * variables + column] = int(
                condition_image[local_row, column])
        for extra, source in enumerate(extra_columns):
            flat[row * variables + nullity + extra] = source.get(key, 0)
    system = nmod_mat(rows, variables, flat, PRIME)
    base_rank = system.rank()

    results = []
    target_columns = []
    for normal, target in zip(("F0", "F1", "F2"), literal.targets[:3]):
        target_column = [0] * rows
        for row, coefficient in target.items():
            target_column[j_index[row]] = (-coefficient) % PRIME
        augmented = nmod_mat(rows, variables + 1, [
            int(system[row, column]) if column < variables
            else target_column[row]
            for row in range(rows)
            for column in range(variables + 1)
        ], PRIME)
        target_columns.append(tuple((-value) % PRIME for value in target_column))
        relations, relation_count = augmented.nullspace()
        relation = next((column for column in range(relation_count)
                         if int(relations[variables, column]) % PRIME), None)
        feasible = relation is not None
        receipt = {
            "normal": normal,
            "augmented_rank_defect": augmented.rank() - base_rank,
            "feasible": feasible,
        }
        if feasible:
            scale = pow(int(relations[variables, relation]) % PRIME,
                        -1, PRIME)
            solution = [int(relations[row, relation]) * scale % PRIME
                        for row in range(variables)]
            alpha = nmod_mat(nullity, 1, solution[:nullity], PRIME)
            source = kernel * alpha
            support = tuple(
                (literal.monomials[index], int(source[row, 0]) % PRIME)
                for row, index in enumerate(indices)
                if int(source[row, 0]) % PRIME)
            parameters = defaultdict(dict)
            for label, value in zip(extra_labels, solution[nullity:]):
                if value:
                    parameters[label[0]][label[1]] = value
            receipt.update({
                "source_support": len(support),
                "A": U.factor_receipt(U.polynomial_from_terms(parameters["A"])),
                "C": U.factor_receipt(U.polynomial_from_terms(parameters["C"])),
            })
        results.append(receipt)
    joint = nmod_mat(rows, variables + len(target_columns), [
        int(system[row, column]) if column < variables
        else target_columns[column - variables][row]
        for row in range(rows)
        for column in range(variables + len(target_columns))
    ], PRIME)
    return {
        "contact_rank_nullity": (contact.rank(), nullity),
        "J_rank_on_contact_kernel": j_image.rank(),
        "homogeneous_C_and_J_fibre_dimension": nullity - j_image.rank(),
        "condition_rows": len(condition_rows),
        "system_rank_columns": (base_rank, variables),
        "joint_augmented_rank_defect": joint.rank() - base_rank,
        "rhs": tuple(results),
    }


def centered_components(literal, indices, source, center):
    """Return the exact fully centered grade-seven coefficient tuple."""
    _support, grouped = U.grouped_grade_seven(literal, indices, source)
    zero = nmod_poly([], PRIME)
    grouped = {shape: grouped.get(shape, zero) for shape in U.EXPECTED_SHAPES}
    r = {}
    pure = {}
    for power in range(3):
        r[power] = sum(
            (comb(higher, power) * center ** (higher - power)
             * grouped[(higher, 1, 0, 6 - higher)]
             for higher in range(power, 3)), zero)
    for power in range(5):
        pure[power] = sum(
            (comb(higher, power) * center ** (higher - power)
             * grouped[(higher, 0, 0, 7 - higher)]
             for higher in range(power, 5)), zero)
    cp = center.derivative()
    # Replace raw R by the fully centered V1=R-P'Z.
    fully_pure = dict(pure)
    fully_pure[0] += cp * r[0]
    fully_pure[1] += cp * r[1]
    fully_pure[2] += cp * r[2]
    return grouped, r, fully_pure


def divide_exact(numerator, denominator):
    quotient, remainder = divmod(numerator, denominator)
    assert remainder == 0, (numerator, denominator, remainder)
    return quotient


def order_four_decomposition(literal, indices, source, center):
    """Unique triangular decomposition in the eight Lambda,V,J1 cycles."""
    grouped, r, h = centered_components(literal, indices, source, center)
    locator = nmod_poly(list(literal.locator), PRIME)
    lp = locator.derivative()
    q1 = center.derivative()

    # In order these multiply
    # V^4, V^2*J1, Lambda*V^3, Lambda*V*J1,
    # Lambda^2*V^2, Lambda^2*J1, Lambda^3*V, Lambda^4.
    p_v4 = h[4]
    p_v2j1 = divide_exact(r[2], locator)
    p_lv3 = divide_exact(h[3] + lp * p_v2j1, locator)
    p_lvj1 = divide_exact(r[1], locator ** 2)
    p_l2v2 = divide_exact(
        h[2] + locator * lp * p_lvj1, locator ** 2)
    p_l2j1 = divide_exact(r[0], locator ** 3)
    p_l3v = divide_exact(
        h[1] + locator ** 2 * lp * p_l2j1, locator ** 3)
    p_l4 = divide_exact(h[0], locator ** 4)
    names = ("V^4", "V^2*J1", "Lambda*V^3", "Lambda*V*J1",
             "Lambda^2*V^2", "Lambda^2*J1", "Lambda^3*V",
             "Lambda^4")
    multipliers = (p_v4, p_v2j1, p_lv3, p_lvj1, p_l2v2,
                   p_l2j1, p_l3v, p_l4)

    # Reconstruct every centered coefficient, not merely the divisibilities.
    assert r[2] == locator * p_v2j1
    assert h[3] == locator * p_lv3 - lp * p_v2j1
    assert r[1] == locator ** 2 * p_lvj1
    assert h[2] == locator ** 2 * p_l2v2 - locator * lp * p_lvj1
    assert r[0] == locator ** 3 * p_l2j1
    assert h[1] == locator ** 3 * p_l3v - locator ** 2 * lp * p_l2j1
    assert h[0] == locator ** 4 * p_l4

    # Invert V=Y-QZ and V1=R-Q'Z and compare all eight raw shapes.
    raw_r = {
        power: sum(
            (comb(higher, power) * (-center) ** (higher - power)
             * r[higher] for higher in range(power, 3)),
            nmod_poly([], PRIME))
        for power in range(3)
    }
    pre_v1 = dict(h)
    for power in range(3):
        pre_v1[power] -= q1 * r[power]
    raw_pure = {
        power: sum(
            (comb(higher, power) * (-center) ** (higher - power)
             * pre_v1[higher] for higher in range(power, 5)),
            nmod_poly([], PRIME))
        for power in range(5)
    }
    assert all(raw_r[power] == grouped[(power, 1, 0, 6 - power)]
               for power in range(3))
    assert all(raw_pure[power] == grouped[(power, 0, 0, 7 - power)]
               for power in range(5))

    raw_caps = {
        "R*Z^6": (raw_r[0].degree(), 24),
        "R*Y*Z^5": (raw_r[1].degree(), 20),
        "R*Y^2*Z^4": (raw_r[2].degree(), 16),
        "Z^7": (raw_pure[0].degree(), 27),
        "Y*Z^6": (raw_pure[1].degree(), 23),
        "Y^2*Z^5": (raw_pure[2].degree(), 19),
        "Y^3*Z^4": (raw_pure[3].degree(), 15),
        "Y^4*Z^3": (raw_pure[4].degree(), 11),
    }
    assert all(degree <= cap for degree, cap in raw_caps.values())

    # Split the raw Z^7 coefficient into the old three-cycle contribution
    # and the five-cycle correction.  High heads cancel in their sum.
    old_boundary = (p_v4 * center ** 4 - h[3] * center ** 3
                    - q1 * r[2] * center ** 2)
    extra_boundary = (h[0] - center * h[1] + center ** 2 * h[2]
                      - q1 * r[0] + center * q1 * r[1])
    assert raw_pure[0] == old_boundary + extra_boundary

    return {
        "multipliers": tuple({
            "family": name,
            "degree": multiplier.degree(),
            "factorization": U.factor_receipt(multiplier),
        } for name, multiplier in zip(names, multipliers)),
        "nonzero_multiplier_count": sum(poly != 0 for poly in multipliers),
        "raw_degree_and_inclusive_cap": raw_caps,
        "Z7_old_three_cycle_degree": old_boundary.degree(),
        "Z7_five_cycle_correction_degree": extra_boundary.degree(),
        "Z7_sum_degree": raw_pure[0].degree(),
        "Z7_five_cycle_correction": U.factor_receipt(extra_boundary),
    }


def canonical_order_four_profile(literal, center):
    indices, _contact, _nullity, _image, lifts = U.solve_restricted(literal)
    return tuple({
        "normal": normal,
        **order_four_decomposition(literal, indices, source, center),
    } for normal, source in lifts)


def canonical_compound_carrier(literal, center):
    """Decompose the particular FLINT lifts and test residual rank one."""
    indices, _contact, _nullity, _image, lifts = U.solve_restricted(literal)
    xi = nmod_poly(list(literal.xi), PRIME)
    locator = nmod_poly(list(literal.locator), PRIME)
    lp = locator.derivative()
    rows = []
    residuals = []
    boundary_residuals = []
    for normal, source in lifts:
        grouped, r, h = centered_components(literal, indices, source, center)
        actuator, rem_a = divmod(r[2], locator * xi)
        cofactor, rem_c = divmod(h[3] + actuator * xi * lp, locator)
        assert rem_a == 0 and rem_c == 0
        residual = (r[0], r[1], h[0], h[1],
                    h[2])
        # The fifth component is already the residual after the A carrier,
        # because h[2]=H2+P'*T2 in the fully centered frame.
        residuals.append(residual)
        c = h[4]
        b = h[3]
        if center == nmod_poly(list(literal.q), PRIME):
            q = center
            # This formula uses Q=Xi^2.  It is the original boundary term.
            b0 = b - c * q + 2 * actuator * locator * xi.derivative()
            boundary = grouped[(0, 0, 0, 7)] - b0 * (-q) ** 3
            reconstructed = (h[0] - q * h[1] + q ** 2 * h[2]
                             - q.derivative() * r[0]
                             + q * q.derivative() * r[1])
            assert boundary == reconstructed
            boundary_residuals.append(boundary)
        rows.append({
            "normal": normal,
            "A": U.factor_receipt(actuator),
            "C": U.factor_receipt(cofactor),
            "c": U.factor_receipt(c),
            "extra_E0_E1_D0_D1_D2": tuple(
                U.factor_receipt(poly) for poly in residual),
        })

    base = residuals[0]
    assert all(poly != 0 for poly in base)
    scales = []
    for residual in residuals:
        scale = int(residual[0][residual[0].degree()]) * pow(
            int(base[0][base[0].degree()]), -1, PRIME) % PRIME
        assert all(right == scale * left
                   for left, right in zip(base, residual))
        scales.append(scale)
    if boundary_residuals:
        assert all(right == scale * boundary_residuals[0]
                   for scale, right in zip(scales, boundary_residuals))
    return {
        "residual_vector_rank": 1,
        "scales_against_F0": tuple(scales),
        "compound_carrier_K_E0_E1_D0_D1_D2": tuple(
            U.factor_receipt(poly) for poly in base),
        "compound_boundary_correction": (
            U.factor_receipt(boundary_residuals[0])
            if boundary_residuals else None),
        "rhs": tuple(rows),
    }


def ablation_scan(literal, center):
    """Find inclusion-minimal extra centered coefficient families."""
    indices = U.restricted_indices(literal)
    _contact, kernel, nullity = contact_kernel(literal, indices)
    source_conditions = tuple(
        centered_condition_column(literal.monomials[index], center)
        for index in indices)
    extra_columns, _extra_labels = carrier_columns(literal, center)
    all_condition_rows, all_condition_image = sparse_times_kernel(
        source_conditions, kernel,
        {row for column in extra_columns for row in column})

    j_rows = tuple(sorted(
        {index for source_index in indices
         for index in literal.columns[source_index]
         if literal.row_keys[index][0] == "J"}
        | {index for target in literal.targets[:3] for index in target}))
    j_matrix = U.matrix_from_columns(j_rows, literal.columns, indices)
    j_image = j_matrix * kernel
    j_index = {row: index for index, row in enumerate(j_rows)}
    targets = []
    for target in literal.targets[:3]:
        targets.append(tuple(target.get(row, 0) % PRIME for row in j_rows))

    optional = ("T0", "T1", "H0", "H1", "H2")
    receipts = []
    maximal_proper = []
    winning_size = None
    for size in range(len(optional) + 1):
        if winning_size is not None and size > winning_size:
            break
        for relaxed_tuple in combinations(optional, size):
            relaxed = set(relaxed_tuple)
            selected = tuple(
                row for row, key in enumerate(all_condition_rows)
                if key[0] not in relaxed)
            rows = len(j_rows) + len(selected)
            variables = nullity + len(extra_columns)
            flat = [0] * (rows * variables)
            for row in range(len(j_rows)):
                for column in range(nullity):
                    flat[row * variables + column] = int(j_image[row, column])
            for selected_row, old_row in enumerate(selected):
                row = len(j_rows) + selected_row
                key = all_condition_rows[old_row]
                for column in range(nullity):
                    flat[row * variables + column] = int(
                        all_condition_image[old_row, column])
                for extra, source in enumerate(extra_columns):
                    flat[row * variables + nullity + extra] = source.get(key, 0)
            system = nmod_mat(rows, variables, flat, PRIME)
            base_rank = system.rank()
            defects = []
            for target in targets:
                augmented = nmod_mat(rows, variables + 1, [
                    int(system[row, column]) if column < variables
                    else (target[row] if row < len(j_rows) else 0)
                    for row in range(rows)
                    for column in range(variables + 1)
                ], PRIME)
                defects.append(augmented.rank() - base_rank)
            if size == len(optional) - 1:
                maximal_proper.append({
                    "relaxed_families": relaxed_tuple,
                    "still_enforced": tuple(
                        family for family in optional if family not in relaxed),
                    "system_rank_columns": (base_rank, variables),
                    "individual_defects": tuple(defects),
                })
            if not any(defects):
                winning_size = size
                receipts.append({
                    "relaxed_families": relaxed_tuple,
                    "system_rank_columns": (base_rank, variables),
                    "individual_defects": tuple(defects),
                })
    return {"minimum_extra_family_count": winning_size,
            "all_maximal_proper_ablations": tuple(maximal_proper),
            "minimum_winners": tuple(receipts)}


def main():
    M.T.PRIME = M.F.PRIME = PRIME
    matched = M.build_case(
        "matched_n10_L10", CASE, actual_agreement_count=7, anchor_count=7,
        normal_coordinates=4)
    offset = M.build_case(
        "matched_n10_L10_error_direction_offsets_3_5_7", CASE,
        actual_agreement_count=7, anchor_count=7, normal_coordinates=4,
        error_direction_offsets=OFFSETS)
    h, p = all_node_center(offset)
    cases = {}
    for label, literal, center in (
            ("matched/Q", matched, nmod_poly(list(matched.q), PRIME)),
            ("offset/Q", offset, nmod_poly(list(offset.q), PRIME)),
            ("offset/P", offset, p)):
        cases[label] = solve_centered(literal, center)
    payload = {
        "scope": (
            "fixed n=10 matched and (3,5,7)-offset chambers; complete "
            "contact-kernel affine fibres and first three literal RHS"
        ),
        "field": PRIME,
        "parameters_n_w_g_m_D_s_t_J_L": CASE,
        "offsets": OFFSETS,
        "all_node_center": {
            "h_in_P_equals_Q_plus_Lambda_h": U.factor_receipt(h),
            "P": U.factor_receipt(p),
        },
        "three_carrier_affine_fibre_tests": cases,
        "offset_Q_five_slot_ablation": ablation_scan(
            offset, nmod_poly(list(offset.q), PRIME)),
        "offset_P_five_slot_ablation": ablation_scan(offset, p),
        "matched_Q_order_four_decomposition": canonical_order_four_profile(
            matched, nmod_poly(list(matched.q), PRIME)),
        "offset_Q_order_four_decomposition": canonical_order_four_profile(
            offset, nmod_poly(list(offset.q), PRIME)),
        "offset_Q_compound_residual": canonical_compound_carrier(
            offset, nmod_poly(list(offset.q), PRIME)),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
