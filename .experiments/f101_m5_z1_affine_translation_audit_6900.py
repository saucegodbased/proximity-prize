#!/usr/bin/env python3
"""Audit whether the m5 constant-Z obstruction is an origin artifact.

The established m5 control uses field points 0,...,9, with 0 among the
agreement points.  Its sparsest Z1 annihilator is consequently just the
constant-coefficient row.  Here we rebuild the *same literal control* after
the affine changes X -> X+1 and X -> X+17.  The monomial source and every
weighted/total cap are unchanged; only the field coordinate assigned to each
logical node is translated.

For each translated control we compute the exact coefficientwise boundary
image of the complete contact kernel at the last legal grade.  We then test
the evaluation and first-derivative functionals at every translated
agreement point.  This is finite F_101 evidence, not a Full187 theorem.
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
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_transposed_four_residue_mapping_cone_gate_6900 as G  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
CASE = G.CASES["m5"]
SHIFTS = (0, 1, 17)


def build_translated_case(shift: int):
    """Run the literal builder with logical node i represented by i+shift."""
    original_locator = F.locator
    original_eval = F.poly_eval
    original_column = M.translated_column

    def shifted_locator(roots):
        return original_locator(tuple((root + shift) % P for root in roots))

    def shifted_eval(poly, logical_node):
        return original_eval(poly, (logical_node + shift) % P)

    def shifted_column(xpow, exps, zpow, logical_node, u0, u1, m, k, p):
        return original_column(
            xpow, exps, zpow, (logical_node + shift) % P,
            u0, u1, m, k, p)

    F.locator = shifted_locator
    F.poly_eval = shifted_eval
    M.translated_column = shifted_column
    try:
        return M.build_case(
            f"m5_affine_shift_{shift}", CASE,
            actual_agreement_count=7,
            anchor_count=7,
            normal_coordinates=3,
            error_direction_offsets=G.OFFSETS,
        )
    finally:
        F.locator = original_locator
        F.poly_eval = original_eval
        M.translated_column = original_column


def coefficient_image(literal, maximum_grade):
    """Exact four-coordinate boundary image on the complete contact kernel."""
    grades = tuple(sum(monomial[1:]) for monomial in literal.monomials)
    terminal = tuple(i for i, grade in enumerate(grades)
                     if grade == maximum_grade)
    prefix = tuple(i for i, grade in enumerate(grades)
                   if grade < maximum_grade)
    source_indices = terminal + prefix
    source_position = {index: position
                       for position, index in enumerate(source_indices)}

    active_rows = {
        row for source_index in source_indices
        for row in literal.columns[source_index]
        if literal.row_keys[row][0] == "C"
    }
    top_rows = tuple(sorted(
        (row for row in active_rows
         if sum(literal.row_keys[row][2][1:]) == maximum_grade),
        key=lambda row: repr(literal.row_keys[row]),
    ))
    lower_rows = tuple(sorted(active_rows - set(top_rows), key=repr))
    contact_rows = top_rows + lower_rows
    contact = G.matrix_from_contact_rows(
        literal, source_indices, contact_rows)
    contact, contact_rank = contact.rref(inplace=True)

    pivots = []
    next_column = 0
    for row in range(contact_rank):
        pivot = G.first_nonzero_in_rref_row(contact, row, next_column)
        pivots.append(pivot)
        next_column = pivot + 1
    pivot_to_row = {pivot: row for row, pivot in enumerate(pivots)}
    free_columns = tuple(column for column in range(len(source_indices))
                         if column not in pivot_to_row)
    free_position = {column: index
                     for index, column in enumerate(free_columns)}

    units = ((1, 0, 0, 0), (0, 1, 0, 0),
             (0, 0, 1, 0), (0, 0, 0, 1))
    monomial_index = {monomial: index
                      for index, monomial in enumerate(literal.monomials)}
    positions = []
    rows = []
    for coordinate, unit in enumerate(units):
        for degree in range(literal.parameters[4]):
            source_index = monomial_index.get((degree,) + unit)
            if source_index is None or source_index not in source_position:
                continue
            positions.append((coordinate, degree))
            column = source_position[source_index]
            values = [0] * len(free_columns)
            if column in free_position:
                values[free_position[column]] = 1
            else:
                pivot_row = pivot_to_row[column]
                for free_index, free_column in enumerate(free_columns):
                    values[free_index] = -int(
                        contact[pivot_row, free_column]) % P
            rows.append(values)
    image = nmod_mat(len(rows), len(free_columns),
                     [entry for row in rows for entry in row], P)
    return positions, image, contact_rank, len(source_indices)


def functional_image(positions, image, coordinate, root, derivative_order):
    """Apply p |-> p(root), or p |-> p'(root), to one boundary coordinate."""
    output = []
    for column in range(image.ncols()):
        value = 0
        for row, (current_coordinate, degree) in enumerate(positions):
            if current_coordinate != coordinate or degree < derivative_order:
                continue
            falling = 1
            for offset in range(derivative_order):
                falling = falling * (degree - offset) % P
            scalar = falling * pow(root, degree - derivative_order, P) % P
            value = (value + scalar * int(image[row, column])) % P
        output.append(value)
    return tuple(output)


def polynomial_vector_from_column(positions, image, column):
    coordinates = []
    for coordinate in range(4):
        entries = {degree: int(image[row, column]) % P
                   for row, (coord, degree) in enumerate(positions)
                   if coord == coordinate and int(image[row, column]) % P}
        coordinates.append(G.trim(tuple(
            entries.get(degree, 0)
            for degree in range(max(entries, default=-1) + 1))))
    return tuple(coordinates)


def one_shift(shift):
    literal = build_translated_case(shift)
    positions, image, contact_rank, source_count = coefficient_image(
        literal, CASE[-1])
    agreements = tuple((logical + shift) % P
                       for logical in literal.actual_agreement)
    locator_square = F.poly_pow(literal.locator, 2)

    # At m=5 and second-jet order, every first-boundary coordinate in this
    # control retains the common agreement factor Lambda^(m-3)=Lambda^2.
    # Exact double-root checks avoid relying on a symbolic factor guess.
    for coordinate in range(4):
        for root in agreements:
            assert all(
                not any(functional_image(
                    positions, image, coordinate, root, order))
                for order in (0, 1))

    z0_row = positions.index((3, 0))
    z0_support = sum(
        int(image[z0_row, column]) % P != 0
        for column in range(image.ncols()))
    z_target = tuple(int(position == (3, 0)) for position in positions)
    image_rank, defects, _joint = G.matrix_target_defects(image, (z_target,))

    vectors = tuple(
        polynomial_vector_from_column(positions, image, column)
        for column in range(image.ncols()))
    localized_rank = G.polynomial_rank(
        tuple(vector for vector in vectors if any(vector)))

    witness_root = agreements[0]
    evaluation_support = tuple(
        (degree, pow(witness_root, degree, P))
        for coordinate, degree in positions
        if coordinate == 3 and pow(witness_root, degree, P)
    )
    assert not any(functional_image(
        positions, image, 3, witness_root, 0))
    assert evaluation_support[0][0] == 0
    assert evaluation_support[0][1] == 1

    # The source box is downward closed in X-degree.  Its translation matrix
    # has unit diagonal, and the same is true for the inverse shift.
    maximum_x_by_shape = {}
    support = set(literal.monomials)
    for xp, y, r, s, z in literal.monomials:
        shape = (y, r, s, z)
        maximum_x_by_shape[shape] = max(
            maximum_x_by_shape.get(shape, -1), xp)
    assert all(all((lower,) + shape in support
                   for lower in range(maximum + 1))
               for shape, maximum in maximum_x_by_shape.items())

    return {
        "shift": shift,
        "field_points": tuple((logical + shift) % P
                              for logical in range(CASE[0])),
        "agreement_points": agreements,
        "agreement_contains_zero": 0 in agreements,
        "locator_coefficients": literal.locator,
        "locator_square_coefficients": locator_square,
        "contact_rank_nullity": (contact_rank, source_count - contact_rank),
        "boundary_rows_columns_rank": (
            image.nrows(), image.ncols(), image_rank),
        "localized_four_rank_over_F101_of_X": localized_rank,
        "pure_constant_z_defect": defects[0],
        "constant_z_row_nonzero_column_count": z0_support,
        "all_four_boundary_coordinates_have_double_zeros_at_all_agreements":
            True,
        "first_agreement_z_evaluation_annihilator_support":
            evaluation_support,
        "first_agreement_z_evaluation_annihilator_support_size":
            len(evaluation_support),
        "evaluation_annihilator_pairs_with_constant_z_as": 1,
        "source_support_downward_closed_in_X_degree": True,
        "affine_X_translation_matrix_unitriangular_shape_by_shape": True,
    }


def main():
    started = time.monotonic()
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = G.P = P
    rows = tuple(one_shift(shift) for shift in SHIFTS)

    assert tuple(row["contact_rank_nullity"] for row in rows) == \
        ((3820, 296),) * len(SHIFTS)
    assert tuple(row["boundary_rows_columns_rank"] for row in rows) == \
        ((131, 296, 12),) * len(SHIFTS)
    assert tuple(row["localized_four_rank_over_F101_of_X"] for row in rows) == \
        (4,) * len(SHIFTS)
    assert tuple(row["pure_constant_z_defect"] for row in rows) == \
        (1,) * len(SHIFTS)
    assert rows[0]["constant_z_row_nonzero_column_count"] == 0
    assert rows[0]["first_agreement_z_evaluation_annihilator_support_size"] == 1
    assert all(row["constant_z_row_nonzero_column_count"] > 0
               for row in rows[1:])
    assert all(row["first_agreement_z_evaluation_annihilator_support_size"] > 1
               for row in rows[1:])

    stable = {
        "scope": (
            "Exact F101 affine-coordinate controls for the literal m5 "
            "coefficientwise boundary image; finite evidence, not Full187."),
        "case_N_w_g_m_D_s_t_J_L": CASE,
        "field": P,
        "rows": rows,
        "decision": "Z1_DEFECT_IS_TRANSLATION_INVARIANT_NOT_A_ZERO_ORIGIN_ARTIFACT",
        "interpretation": (
            "At shift zero, evaluation at the agreement root zero is the "
            "single constant-coefficient Z row.  At nonzero shifts that row "
            "becomes nonzero, but evaluation at the translated agreement "
            "root is still an exact annihilator pairing one with constant Z. "
            "Every boundary coordinate has the common agreement double-zero "
            "condition, while localization can invert that nonconstant factor."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime_receipt": {
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "external_memory_cap_bytes": 4 * 1024**3,
        },
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
