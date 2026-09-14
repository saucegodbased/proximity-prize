#!/usr/bin/env python3
"""Exact affine-fibre audit of the first nonvacuous m=5 top shell.

Canonical lifts in the fixed n=10 arbitrary-direction chamber have seventeen
centered grade-eight shapes.  A canonical lift is gauge-dependent, so merely
printing those shapes does not show that the family is necessary or even that
it is closed under changing the lower-grade correction.

This script computes the complete contact kernel on grades <= 8 once.  It
then maps the grade-eight part of that 71-dimensional kernel into centered
coordinates V=Y-QZ, V1=R-Q'Z, V2=S-Q''Z.  Support restrictions are imposed
*after* this map, while every lower-grade component remains free.  Therefore
each containment/ablation result concerns the whole affine fibre of lifts,
not the particular nullspace basis chosen by a solver.

This is finite exact F101 discovery evidence, not a target theorem.
"""

from __future__ import annotations

from math import comb
from itertools import combinations
import hashlib
import json
from pathlib import Path
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_n10_grade7_centered_wronskian_universality_6900 as U  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
OFFSETS = (3, 5, 7)
M_VALUE = 5
CASE = (10, 4, 7, M_VALUE, 7 * M_VALUE, 1, 1,
        M_VALUE + 2, M_VALUE + 6)
TOP_GRADE = CASE[7] + 1

CANONICAL_SHAPES = frozenset(
    [(y, 0, 0, TOP_GRADE - y) for y in range(7)]
    + [(y, 1, 0, TOP_GRADE - 1 - y) for y in range(5)]
    + [(y, 0, 1, TOP_GRADE - 1 - y) for y in range(5)]
)

# The first one-at-a-time audit marks every V2 shape and the top V1*V^4
# shape individually optional.  Those removals do *not* all compose: the
# exhaustive sweep keeps V1*V^4 when all V2 shapes are removed.  Keep this
# deliberately over-pruned eleven-shape family as the red control which
# catches the otherwise tempting optional-removals fallacy.
CORE11_SHAPES = frozenset(
    [(y, 0, 0, TOP_GRADE - y) for y in range(7)]
    + [(y, 1, 0, TOP_GRADE - 1 - y) for y in range(4)]
)


def poly_shift(poly, amount):
    return (0,) * amount + tuple(poly)


def centered_coordinates_of_raw_monomial(literal, monomial):
    """Expand one raw top monomial after Y=V+QZ, etc."""
    xp, y, r, s, z = monomial
    if y + r + s + z != TOP_GRADE:
        return {}
    result = {}
    q = literal.q
    q1 = F.poly_derivative(q)
    q2 = F.poly_derivative(q, 2)
    for vy in range(y + 1):
        for vr in range(r + 1):
            for vs in range(s + 1):
                polynomial = (1,)
                polynomial = F.poly_mul(polynomial, F.poly_pow(q, y - vy))
                polynomial = F.poly_mul(polynomial, F.poly_pow(q1, r - vr))
                polynomial = F.poly_mul(polynomial, F.poly_pow(q2, s - vs))
                polynomial = poly_shift(polynomial, xp)
                scale = (comb(y, vy) * comb(r, vr) * comb(s, vs)) % P
                shape = (vy, vr, vs,
                         z + (y - vy) + (r - vr) + (s - vs))
                for degree, coefficient in enumerate(polynomial):
                    value = scale * coefficient % P
                    if value:
                        key = (shape, degree)
                        result[key] = (result.get(key, 0) + value) % P
    return {key: value for key, value in result.items() if value}


def matrix_from_columns(row_ids, columns, indices):
    row_index = {row: index for index, row in enumerate(row_ids)}
    flat = [0] * (len(row_ids) * len(indices))
    for column, source_index in enumerate(indices):
        for row, coefficient in columns[source_index].items():
            destination = row_index.get(row)
            if destination is not None:
                flat[destination * len(indices) + column] = coefficient % P
    return nmod_mat(len(row_ids), len(indices), flat, P)


def rank_with_targets(image, target_columns):
    rows = image.nrows()
    columns = image.ncols()
    augmented = nmod_mat(rows, columns + len(target_columns), [
        (int(image[row, column]) % P if column < columns
         else target_columns[column - columns][row])
        for row in range(rows) for column in range(columns + len(target_columns))
    ], P)
    rank = image.rank()
    individual = tuple(
        nmod_mat(rows, columns + 1, [
            (int(image[row, column]) % P if column < columns
             else target[row])
            for row in range(rows) for column in range(columns + 1)
        ], P).rank() - rank
        for target in target_columns
    )
    return rank, individual, augmented.rank() - rank


def projected_centered_rows(literal, indices, contact_kernel):
    """Centered top-coordinate functionals restricted to contact cycles."""
    nullity = contact_kernel.ncols()
    projected = {}
    for source_row, source_index in enumerate(indices):
        monomial = literal.monomials[source_index]
        coordinates = centered_coordinates_of_raw_monomial(literal, monomial)
        if not coordinates:
            continue
        kernel_row = tuple(
            int(contact_kernel[source_row, column]) % P
            for column in range(nullity))
        if not any(kernel_row):
            continue
        for coordinate, coefficient in coordinates.items():
            target = projected.setdefault(coordinate, [0] * nullity)
            for column, value in enumerate(kernel_row):
                target[column] = (target[column] + coefficient * value) % P
    return {
        coordinate: tuple(row)
        for coordinate, row in projected.items() if any(row)
    }


def constrained_image(allowed_shapes, projected, contact_kernel, j_matrix):
    forbidden = tuple(
        row for (shape, _degree), row in sorted(projected.items())
        if shape not in allowed_shapes
    )
    if forbidden:
        constraint = nmod_mat(len(forbidden), contact_kernel.ncols(), [
            value for row in forbidden for value in row
        ], P)
        allowed_coordinates, dimension = constraint.nullspace()
    else:
        dimension = contact_kernel.ncols()
        allowed_coordinates = nmod_mat(dimension, dimension, P)
        for index in range(dimension):
            allowed_coordinates[index, index] = 1
    allowed_coordinates = nmod_mat(
        allowed_coordinates.nrows(), dimension, [
            int(allowed_coordinates[row, column])
            for row in range(allowed_coordinates.nrows())
            for column in range(dimension)
        ], P)
    return j_matrix * contact_kernel * allowed_coordinates, dimension, \
        len(forbidden)


def receipt(name, allowed_shapes, projected, contact_kernel, j_matrix,
            target_columns):
    image, cycle_dimension, constraint_rows = constrained_image(
        allowed_shapes, projected, contact_kernel, j_matrix)
    image_rank, individual, joint = rank_with_targets(image, target_columns)
    return {
        "name": name,
        "allowed_shape_count": len(allowed_shapes),
        "centered_constraint_rows_on_contact_kernel": constraint_rows,
        "constrained_contact_kernel_dimension": cycle_dimension,
        "vertical_image_rank": image_rank,
        "individual_F0_F1_F2_defects": individual,
        "joint_F0_F1_F2_defect": joint,
        "affine_lift_fibre_dimension_when_contained": (
            cycle_dimension - image_rank if joint == 0 else None),
    }


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = U.PRIME = P
    literal = M.build_case(
        "m5_centered_affine_fibre", CASE, 7, 7, 3,
        error_direction_offsets=OFFSETS)
    indices = U.restricted_indices(literal)
    contact_rows = tuple(
        index for index, row in enumerate(literal.row_keys) if row[0] == "C")
    j_rows = tuple(sorted(
        {index for source_index in indices
         for index in literal.columns[source_index]
         if literal.row_keys[index][0] == "J"}
        | {index for target in literal.targets[:3] for index in target}
    ))
    contact = matrix_from_columns(contact_rows, literal.columns, indices)
    contact_kernel, nullity = contact.nullspace()
    contact_kernel = nmod_mat(contact_kernel.nrows(), nullity, [
        int(contact_kernel[row, column])
        for row in range(contact_kernel.nrows()) for column in range(nullity)
    ], P)
    j_matrix = matrix_from_columns(j_rows, literal.columns, indices)
    target_columns = tuple(tuple(
        target.get(row, 0) % P for row in j_rows
    ) for target in literal.targets[:3])

    projected = projected_centered_rows(literal, indices, contact_kernel)
    all_shapes = frozenset(shape for shape, _degree in projected)
    assert CANONICAL_SHAPES <= all_shapes

    tests = [
        receipt("unrestricted_top", all_shapes, projected, contact_kernel,
                j_matrix, target_columns),
        receipt("canonical_17_shapes", CANONICAL_SHAPES, projected,
                contact_kernel, j_matrix, target_columns),
        receipt("pure_0_to_6_plus_V1_0_to_3_core11", CORE11_SHAPES,
                projected, contact_kernel, j_matrix, target_columns),
    ]
    for shape in sorted(CANONICAL_SHAPES):
        tests.append(receipt(
            f"canonical_minus_{shape}", CANONICAL_SHAPES - {shape},
            projected, contact_kernel, j_matrix, target_columns))
    core_ablation_offset = len(tests)
    for shape in sorted(CORE11_SHAPES):
        tests.append(receipt(
            f"core11_minus_{shape}", CORE11_SHAPES - {shape}, projected,
            contact_kernel, j_matrix, target_columns))
    for family, shapes in (
        ("all_pure_V", {shape for shape in CANONICAL_SHAPES
                        if shape[1] == shape[2] == 0}),
        ("all_V1", {shape for shape in CANONICAL_SHAPES if shape[1] == 1}),
        ("all_V2", {shape for shape in CANONICAL_SHAPES if shape[2] == 1}),
    ):
        tests.append(receipt(
            f"canonical_without_{family}", CANONICAL_SHAPES - shapes,
            projected, contact_kernel, j_matrix, target_columns))

    canonical = tests[1]
    assert canonical["joint_F0_F1_F2_defect"] == 0
    core11 = tests[2]
    single_ablation_necessary = tuple(
        (shape, test["joint_F0_F1_F2_defect"])
        for shape, test in zip(sorted(CANONICAL_SHAPES), tests[3:20])
    )
    core11_ablation_defects = tuple(
        (shape, test["joint_F0_F1_F2_defect"])
        for shape, test in zip(
            sorted(CORE11_SHAPES),
            tests[core_ablation_offset:core_ablation_offset
                  + len(CORE11_SHAPES)])
    )
    individually_optional = tuple(
        shape for shape, defect in single_ablation_necessary if defect == 0)
    optional_sweep = []
    for removal_count in range(len(individually_optional) + 1):
        for removed in combinations(individually_optional, removal_count):
            test = receipt(
                "optional_subset_sweep", CANONICAL_SHAPES - set(removed),
                projected, contact_kernel, j_matrix, target_columns)
            optional_sweep.append({
                "removed": removed,
                "remaining_shape_count": 17 - removal_count,
                "cycle_dimension":
                    test["constrained_contact_kernel_dimension"],
                "vertical_image_rank": test["vertical_image_rank"],
                "joint_defect": test["joint_F0_F1_F2_defect"],
            })
    maximum_removal = max(
        len(row["removed"]) for row in optional_sweep
        if row["joint_defect"] == 0)
    maximally_pruned = tuple(
        row for row in optional_sweep
        if row["joint_defect"] == 0
        and len(row["removed"]) == maximum_removal)

    payload = {
        "scope": (
            "exact affine-fibre centered-support audit in the first "
            "nonvacuous m5 n10 chamber; finite F101 evidence only"
        ),
        "field": P,
        "case": CASE,
        "offsets": OFFSETS,
        "restricted_source_columns": len(indices),
        "contact_shape_rank_nullity": (contact.rank(), nullity),
        "centered_top_shapes_visible_on_contact_kernel": tuple(
            sorted(all_shapes)),
        "centered_projected_coordinate_rows": len(projected),
        "canonical_shapes": tuple(sorted(CANONICAL_SHAPES)),
        "core11_shapes": tuple(sorted(CORE11_SHAPES)),
        "tests": tuple(tests),
        "canonical_single_shape_ablation_joint_defects":
            single_ablation_necessary,
        "core11_single_shape_ablation_joint_defects":
            core11_ablation_defects,
        "individually_optional_shapes": individually_optional,
        "maximum_compatible_optional_shape_removals": maximum_removal,
        "maximally_pruned_containing_families": maximally_pruned,
        "honest_interpretation": (
            "support tests range over the complete contact-kernel affine "
            "fibre and leave every lower grade free; they do not confuse "
            "one canonical nullspace lift with a necessity theorem"
        ),
    }
    canonical_json = json.dumps(
        payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical_json.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
