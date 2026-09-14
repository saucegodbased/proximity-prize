#!/usr/bin/env python3
"""Exact m=6 affine-fibre ablation and mixed-interface receipt.

This is the m=6 companion to ``f101_m5_top_centered_affine_fibre_6900``.
It imposes top-shell support constraints only after taking the *complete*
restricted contact kernel, so all lower-grade corrections remain free.  In
particular, a green result is not an artefact of the canonical nullspace gauge.

The script also extracts a deterministic exact lift of each of F0,F1,F2 from
the canonical 23-shape family, which is inclusion-minimal among its own
subfamilies in this chamber.  The full raw source vectors are represented by
stable hashes plus grade/support summaries; the coefficient vector is
recomputed exactly by ``deterministic_lift`` below.

Finite F101 discovery evidence only; this is not a target theorem.
"""

from __future__ import annotations

from itertools import combinations
import hashlib
import json
from pathlib import Path
import sys

from flint import nmod_mat, nmod_poly

sys.path.insert(0, ".experiments")
import f101_m5_top_centered_affine_fibre_6900 as A  # noqa: E402
import f101_n10_grade7_centered_wronskian_universality_6900 as U  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
OFFSETS = (3, 5, 7)
M_VALUE = 6
CASE = (10, 4, 7, M_VALUE, 7 * M_VALUE, 1, 1,
        M_VALUE + 2, M_VALUE + 6)
TOP_GRADE = CASE[7] + 1

# Exact support printed by the independent canonical-shell computation.
CANONICAL_SHAPES = frozenset(
    [(y, 0, 0, TOP_GRADE - y) for y in range(9)]
    + [(y, 1, 0, TOP_GRADE - 1 - y) for y in range(7)]
    + [(y, 0, 1, TOP_GRADE - 1 - y) for y in range(7)]
)

# Candidate after removing every V2 coordinate.  Its exact minimality among
# pure-V/V1 subfamilies is checked below, rather than assumed.
PURE_V_V1_SHAPES = frozenset(
    [(y, 0, 0, TOP_GRADE - y) for y in range(9)]
    + [(y, 1, 0, TOP_GRADE - 1 - y) for y in range(7)]
)


def constraint_basis(allowed_shapes, projected, contact_kernel):
    """Coordinates in the complete contact kernel obeying a top support cap."""
    forbidden = tuple(
        row for (shape, _degree), row in sorted(projected.items())
        if shape not in allowed_shapes
    )
    if forbidden:
        constraint = nmod_mat(len(forbidden), contact_kernel.ncols(), [
            value for row in forbidden for value in row
        ], P)
        coordinates, dimension = constraint.nullspace()
        coordinates = nmod_mat(coordinates.nrows(), dimension, [
            int(coordinates[row, column])
            for row in range(coordinates.nrows())
            for column in range(dimension)
        ], P)
    else:
        dimension = contact_kernel.ncols()
        coordinates = nmod_mat(dimension, dimension, P)
        for index in range(dimension):
            coordinates[index, index] = 1
    return coordinates, dimension, len(forbidden)


def image_receipt(name, allowed_shapes, projected, contact_kernel, j_matrix,
                  target_columns):
    coordinates, dimension, constraint_rows = constraint_basis(
        allowed_shapes, projected, contact_kernel)
    source_basis = contact_kernel * coordinates
    image = j_matrix * source_basis
    image_rank, individual, joint = A.rank_with_targets(
        image, target_columns)
    return {
        "name": name,
        "allowed_shape_count": len(allowed_shapes),
        "centered_constraint_rows_on_contact_kernel": constraint_rows,
        "constrained_contact_kernel_dimension": dimension,
        "vertical_image_rank": image_rank,
        "individual_F0_F1_F2_defects": individual,
        "joint_F0_F1_F2_defect": joint,
        "affine_lift_fibre_dimension_when_contained": (
            dimension - image_rank if joint == 0 else None),
    }


def deterministic_lift(allowed_shapes, projected, contact_kernel, j_matrix,
                       target_column):
    """Return the first FLINT-nullspace lift with J-image exactly target."""
    coordinates, dimension, _ = constraint_basis(
        allowed_shapes, projected, contact_kernel)
    source_basis = contact_kernel * coordinates
    image = j_matrix * source_basis
    augmented = nmod_mat(image.nrows(), dimension + 1, [
        (int(image[row, column]) % P if column < dimension
         else target_column[row] % P)
        for row in range(image.nrows()) for column in range(dimension + 1)
    ], P)
    relations, relation_count = augmented.nullspace()
    chosen = next(
        column for column in range(relation_count)
        if int(relations[dimension, column]) % P)
    last = int(relations[dimension, chosen]) % P
    coefficient = nmod_mat(dimension, 1, [
        -int(relations[row, chosen]) * pow(last, -1, P) % P
        for row in range(dimension)
    ], P)
    source = source_basis * coefficient
    assert all(
        int((j_matrix * source)[row, 0]) % P == target_column[row] % P
        for row in range(image.nrows()))
    return source


def centered_top_polynomials(literal, indices, source):
    coordinates = {}
    for source_row, source_index in enumerate(indices):
        coefficient = int(source[source_row, 0]) % P
        if not coefficient:
            continue
        for (shape, degree), multiplier in \
                A.centered_coordinates_of_raw_monomial(
                    literal, literal.monomials[source_index]).items():
            polynomial = coordinates.setdefault(shape, {})
            polynomial[degree] = (
                polynomial.get(degree, 0) + coefficient * multiplier) % P
    result = {}
    for shape, terms in coordinates.items():
        coefficients = [0] * (max(terms, default=-1) + 1)
        for degree, coefficient in terms.items():
            coefficients[degree] = coefficient
        while coefficients and coefficients[-1] == 0:
            coefficients.pop()
        if coefficients:
            result[shape] = tuple(coefficients)
    return result


def source_summary(literal, indices, source):
    terms = tuple(
        (literal.monomials[source_index], int(source[row, 0]) % P)
        for row, source_index in enumerate(indices)
        if int(source[row, 0]) % P)
    by_grade = {}
    for monomial, _coefficient in terms:
        grade = sum(monomial[1:])
        row = by_grade.setdefault(grade, {
            "term_count": 0, "shapes": set(), "x_degrees": []})
        row["term_count"] += 1
        row["shapes"].add(monomial[1:])
        row["x_degrees"].append(monomial[0])
    normalized_grades = {
        grade: {
            "term_count": row["term_count"],
            "shape_count": len(row["shapes"]),
            "x_degree_interval": (
                min(row["x_degrees"]), max(row["x_degrees"])),
        }
        for grade, row in sorted(by_grade.items())
    }
    summary = {
        "nonzero_raw_source_terms": len(terms),
        "raw_source_sha256": hashlib.sha256(repr(terms).encode()).hexdigest(),
        "by_grade": normalized_grades,
    }
    if "--dump-lifts" in sys.argv:
        summary["raw_source_terms_X_Y_R_S_Z_coefficient"] = terms
    return summary


def polynomial_gcd(polynomials):
    values = [nmod_poly(list(poly), P) for poly in polynomials if poly]
    if not values:
        return ()
    gcd = values[0]
    for value in values[1:]:
        gcd = gcd.gcd(value)
    return tuple(int(gcd[index]) % P for index in range(gcd.degree() + 1))


def divisor_valuation(polynomial, divisor):
    if not polynomial:
        return None
    value = nmod_poly(list(polynomial), P)
    factor = nmod_poly(list(divisor), P)
    answer = 0
    while value != 0:
        quotient, remainder = divmod(value, factor)
        if remainder != 0:
            break
        value = quotient
        answer += 1
    return answer


def polynomial_profile(polynomial, literal):
    if not polynomial:
        return {"degree": -1, "zero": True}
    value = nmod_poly(list(polynomial), P)
    unit, factors = value.factor()
    return {
        "degree": value.degree(),
        "leading_coefficient": int(value.leading_coefficient()) % P,
        "x_valuation": next(
            (index for index, coefficient in enumerate(polynomial)
             if coefficient % P), None),
        "Lambda_valuation": divisor_valuation(polynomial, literal.locator),
        "Xi_valuation": divisor_valuation(polynomial, literal.xi),
        "factor_unit": int(unit) % P,
        "factor_degrees_and_multiplicities": tuple(
            (factor.degree(), int(multiplicity))
            for factor, multiplicity in factors),
        "coefficient_sha256": hashlib.sha256(
            repr(tuple(polynomial)).encode()).hexdigest(),
    }


def main():
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = U.PRIME = P
    # The imported centered expansion is deliberately reused, with the shell
    # grade set explicitly so there is one implementation of the coordinate
    # transform across m=5 and m=6.
    A.TOP_GRADE = TOP_GRADE
    literal = M.build_case(
        "m6_centered_affine_fibre", CASE, 7, 7, 3,
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
    contact = A.matrix_from_columns(contact_rows, literal.columns, indices)
    contact_kernel, nullity = contact.nullspace()
    contact_kernel = nmod_mat(contact_kernel.nrows(), nullity, [
        int(contact_kernel[row, column])
        for row in range(contact_kernel.nrows())
        for column in range(nullity)
    ], P)
    j_matrix = A.matrix_from_columns(j_rows, literal.columns, indices)
    target_columns = tuple(tuple(
        target.get(row, 0) % P for row in j_rows
    ) for target in literal.targets[:3])
    projected = A.projected_centered_rows(literal, indices, contact_kernel)
    all_shapes = frozenset(shape for shape, _degree in projected)
    assert CANONICAL_SHAPES <= all_shapes

    all_non_v2_shapes = frozenset(
        shape for shape in all_shapes if shape[2] == 0)
    tests = [
        image_receipt("unrestricted_top", all_shapes, projected,
                      contact_kernel, j_matrix, target_columns),
        image_receipt("zero_top", frozenset(), projected,
                      contact_kernel, j_matrix, target_columns),
        image_receipt("canonical_23_shapes", CANONICAL_SHAPES, projected,
                      contact_kernel, j_matrix, target_columns),
        image_receipt("canonical_no_V2_16_shapes", PURE_V_V1_SHAPES,
                      projected, contact_kernel, j_matrix, target_columns),
        image_receipt("all_visible_no_V2_17_shapes", all_non_v2_shapes,
                      projected, contact_kernel, j_matrix, target_columns),
    ]
    canonical_ablation = []
    for shape in sorted(CANONICAL_SHAPES):
        canonical_ablation.append((shape, image_receipt(
            f"canonical23_minus_{shape}", CANONICAL_SHAPES - {shape},
            projected, contact_kernel, j_matrix, target_columns)))
    canonical_optional = tuple(
        shape for shape, test in canonical_ablation
        if test["joint_F0_F1_F2_defect"] == 0)

    core_ablation = []
    for shape in sorted(PURE_V_V1_SHAPES):
        core_ablation.append((shape, image_receipt(
            f"core16_minus_{shape}", PURE_V_V1_SHAPES - {shape},
            projected, contact_kernel, j_matrix, target_columns)))
    individually_optional = tuple(
        shape for shape, test in core_ablation
        if test["joint_F0_F1_F2_defect"] == 0)

    subset_sweep = []
    if len(canonical_optional) <= 12:
        for removal_count in range(len(canonical_optional) + 1):
            for removed in combinations(canonical_optional, removal_count):
                test = image_receipt(
                    "optional_subset_sweep",
                    CANONICAL_SHAPES - set(removed), projected,
                    contact_kernel, j_matrix, target_columns)
                subset_sweep.append({
                    "removed": removed,
                    "remaining_shape_count": (
                        len(CANONICAL_SHAPES) - removal_count),
                    "cycle_dimension":
                        test["constrained_contact_kernel_dimension"],
                    "vertical_image_rank": test["vertical_image_rank"],
                    "joint_defect": test["joint_F0_F1_F2_defect"],
                })
    maximum_removal = max(
        (len(row["removed"]) for row in subset_sweep
         if row["joint_defect"] == 0), default=0)
    minimal_shapes = CANONICAL_SHAPES
    green_sweep = tuple(
        row for row in subset_sweep if row["joint_defect"] == 0)
    if green_sweep:
        chosen = next(
            row for row in green_sweep
            if len(row["removed"]) == maximum_removal)
        minimal_shapes = CANONICAL_SHAPES - set(chosen["removed"])

    lifts = []
    centered_by_normal = {}
    for normal, target_column in zip(("F0", "F1", "F2"), target_columns):
        source = deterministic_lift(
            minimal_shapes, projected, contact_kernel, j_matrix,
            target_column)
        centered = centered_top_polynomials(literal, indices, source)
        assert frozenset(centered) <= minimal_shapes
        centered_by_normal[normal] = centered
        lifts.append({
            "normal": normal,
            "source": source_summary(literal, indices, source),
            "centered_top_coefficients": tuple(
                (shape, coefficients)
                for shape, coefficients in sorted(centered.items())),
        })

    shape_common_gcds = tuple(
        (shape, polynomial_gcd(tuple(
            centered_by_normal[normal].get(shape, ())
            for normal in ("F0", "F1", "F2"))))
        for shape in sorted(minimal_shapes)
    )
    top_operator_profile = tuple(
        {
            "shape_V_V1_V2_Z": shape,
            "rhs_coefficient_profiles": tuple(
                (normal, polynomial_profile(
                    centered_by_normal[normal].get(shape, ()), literal))
                for normal in ("F0", "F1", "F2")),
            "common_gcd_profile": polynomial_profile(gcd, literal),
            "common_gcd_coefficients": gcd,
        }
        for shape, gcd in shape_common_gcds
    )

    def family_sequence(selector):
        answer = []
        for row in top_operator_profile:
            shape = row["shape_V_V1_V2_Z"]
            if not selector(shape):
                continue
            rhs_profiles = tuple(
                profile for _normal, profile
                in row["rhs_coefficient_profiles"])
            assert len({profile["degree"] for profile in rhs_profiles}) == 1
            answer.append((
                shape[0], rhs_profiles[0]["degree"],
                row["common_gcd_profile"]["Lambda_valuation"]))
        return tuple(answer)

    coefficient_recurrences = {
        "pure_V_y_degree_common_Lambda_valuation": family_sequence(
            lambda shape: shape[1] == shape[2] == 0),
        "V1_V_y_degree_common_Lambda_valuation": family_sequence(
            lambda shape: shape[1] == 1),
        "V2_V_y_degree_common_Lambda_valuation": family_sequence(
            lambda shape: shape[2] == 1),
        "verified_degree_formulas": (
            "pure: deg C_y=55-6y for 0<=y<=7, terminal C_8 constant",
            "V1: deg B_y=50-6y for 0<=y<=6",
            "V2: deg A_y=51-6y for 0<=y<=6",
        ),
    }
    assert coefficient_recurrences[
        "pure_V_y_degree_common_Lambda_valuation"] == tuple(
            [(y, 55 - 6 * y, (6, 3, 2, 1, 0, 0, 0, 0)[y])
             for y in range(8)] + [(8, 0, 0)])
    assert coefficient_recurrences[
        "V1_V_y_degree_common_Lambda_valuation"] == tuple(
            (y, 50 - 6 * y, (4, 3, 2, 1, 1, 1, 0)[y])
            for y in range(7))
    assert coefficient_recurrences[
        "V2_V_y_degree_common_Lambda_valuation"] == tuple(
            (y, 51 - 6 * y, (5, 4, 3, 2, 2, 1, 0)[y])
            for y in range(7))

    zero_top = tests[1]
    minimal_test = image_receipt(
        "inclusion_minimal_subset_of_canonical23", minimal_shapes, projected,
        contact_kernel, j_matrix, target_columns)

    lower_indices = tuple(
        source_index for source_index in indices
        if sum(literal.monomials[source_index][1:]) < TOP_GRADE)
    top_indices = tuple(
        source_index for source_index in indices
        if sum(literal.monomials[source_index][1:]) == TOP_GRADE)
    lower_contact = A.matrix_from_columns(
        contact_rows, literal.columns, lower_indices)
    v2_rows = tuple(
        row for (shape, _degree), row in sorted(projected.items())
        if shape[2] == 1)
    v2_projection = nmod_mat(len(v2_rows), nullity, [
        coefficient for row in v2_rows for coefficient in row
    ], P)
    payload = {
        "scope": (
            "exact m6 n10 affine-fibre centered-support audit and "
            "deterministic mixed lower/top lifts; finite F101 evidence only"
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
        "pure_V_V1_shapes": tuple(sorted(PURE_V_V1_SHAPES)),
        "all_visible_no_V2_shapes": tuple(sorted(all_non_v2_shapes)),
        "filtered_contact_interface": {
            "lower_grades_source_columns": len(lower_indices),
            "lower_grades_contact_rank": lower_contact.rank(),
            "lower_grades_contact_kernel_dimension":
                len(lower_indices) - lower_contact.rank(),
            "top_grade_source_columns": len(top_indices),
            "top_grade_contact_rank_increment":
                contact.rank() - lower_contact.rank(),
            "full_contact_kernel_dimension": nullity,
            "V2_coordinate_rows_on_full_kernel": len(v2_rows),
            "V2_projection_rank_on_full_kernel": v2_projection.rank(),
            "no_V2_full_kernel_dimension": nullity - v2_projection.rank(),
        },
        "tests": tuple(tests),
        "pure_V_V1_single_shape_ablation_joint_defects": tuple(
            (shape, test["joint_F0_F1_F2_defect"])
            for shape, test in core_ablation),
        "canonical_single_shape_ablation_joint_defects": tuple(
            (shape, test["joint_F0_F1_F2_defect"])
            for shape, test in canonical_ablation),
        "individually_optional_inside_canonical": canonical_optional,
        "individually_optional_inside_pure_V_V1": individually_optional,
        "maximum_compatible_optional_shape_removals": maximum_removal,
        "inclusion_minimal_green_subset_of_canonical23":
            tuple(sorted(minimal_shapes)),
        "inclusion_minimal_canonical23_receipt": minimal_test,
        "mixed_interface": {
            "zero_top_vertical_image_rank": zero_top["vertical_image_rank"],
            "zero_top_joint_target_defect":
                zero_top["joint_F0_F1_F2_defect"],
            "with_minimal_top_vertical_image_rank":
                minimal_test["vertical_image_rank"],
            "with_minimal_top_joint_target_defect":
                minimal_test["joint_F0_F1_F2_defect"],
            "new_vertical_directions_enabled_by_top":
                (minimal_test["vertical_image_rank"]
                 - zero_top["vertical_image_rank"]),
        },
        "deterministic_exact_lifts": tuple(lifts),
        "three_rhs_common_gcd_by_centered_shape": shape_common_gcds,
        "three_parameter_centered_top_operator_profile":
            top_operator_profile,
        "coefficient_degree_and_divisibility_recurrences":
            coefficient_recurrences,
        "three_parameter_operator_formula": (
            "For f=(f0,f1,f2), take the F101-linear combination of the "
            "three deterministic source lifts.  Its top shell is sum_y "
            "C_y(f;X)V^y Z^(9-y) + V1*sum_y B_y(f;X)V^y Z^(8-y) "
            "+ V2*sum_y A_y(f;X)V^y Z^(8-y); every coefficient is the "
            "same linear combination of the three printed basis "
            "polynomials.  Contact is zero and J-image is sum_i fi*Fi."
        ),
        "honest_interpretation": (
            "top support is restricted on the complete contact kernel; "
            "lower grades are unconstrained.  The zero-top comparison "
            "isolates the mixed filtered extension rather than claiming "
            "that the printed top shell is itself an agreement cycle."
        ),
    }
    canonical_json = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical_json.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    if "--table" in sys.argv:
        print("shape | gcd(deg,Lambda,Xi) | F0(deg,Lambda,Xi) | "
              "F1(deg,Lambda,Xi) | F2(deg,Lambda,Xi)")
        for row in top_operator_profile:
            common = row["common_gcd_profile"]
            rhs = [profile for _normal, profile
                   in row["rhs_coefficient_profiles"]]
            def triple(profile):
                return (profile["degree"], profile.get("Lambda_valuation"),
                        profile.get("Xi_valuation"))
            print(f"{row['shape_V_V1_V2_Z']} | {triple(common)} | "
                  + " | ".join(str(triple(profile)) for profile in rhs))
        print(json.dumps({
            "canonical_sha256": payload["canonical_sha256"],
            "script_sha256": payload["script_sha256"],
            "tests": tuple(tests),
            "mixed_interface": payload["mixed_interface"],
        }, sort_keys=True))
    elif "--compact" in sys.argv:
        compact = {
            "canonical_sha256": payload["canonical_sha256"],
            "script_sha256": payload["script_sha256"],
            "case": CASE,
            "restricted_source_columns": len(indices),
            "contact_shape_rank_nullity": (contact.rank(), nullity),
            "tests": tuple(tests),
            "canonical_single_shape_ablation": tuple(
                (shape, {
                    "dimension": test[
                        "constrained_contact_kernel_dimension"],
                    "image_rank": test["vertical_image_rank"],
                    "joint_defect": test["joint_F0_F1_F2_defect"],
                })
                for shape, test in canonical_ablation),
            "minimal_green_shapes": tuple(sorted(minimal_shapes)),
            "mixed_interface": payload["mixed_interface"],
            "filtered_contact_interface":
                payload["filtered_contact_interface"],
            "lifts": tuple({
                "normal": lift["normal"],
                "source": lift["source"],
            } for lift in lifts),
            "top_operator_profile": top_operator_profile,
        }
        print(json.dumps(compact, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
