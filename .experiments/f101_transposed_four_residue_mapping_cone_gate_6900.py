#!/usr/bin/env python3
"""Exact target-only transpose gate for the filtered Full187 analogue.

The contact matrix is never replaced by an ambient cokernel or by a selected
carrier family.  For a centered-grade prefix ``V_<=q`` we row-reduce the
literal complete contact map, with the grade-q source columns first.  We then
reduce only the four polynomial boundary covectors Y/R/S/Z modulo the
transpose contact image.  Their four residues represent

    (V_<=q)^* / range(C_<=q^*).

After packing coefficient rows as polynomials, their rank over F_101(X) is
exactly the rank of the *localized* four-boundary image of the complete
contact kernel.  Three locator-normal target columns and the pure Z target are
tested against this localized residue image.  The script also retains the
coefficientwise F_101 residue matrix long enough to test the three prescribed
Y/R/S columns and the pure constant Z column in the filtered source exactly.
Thus a fraction-field rank is never mistaken for a degree-bounded lift.

The grade-q-first pivot convention is the transpose of the exact filtered
mapping cone: top contact rows see only grade-q columns, while lower rows
perform the connecting correction.  The output also records the mapping-cone
nullity/rank identity between the two consecutive prefixes.

This is finite F101 discovery evidence, not a target theorem.
"""

from __future__ import annotations

import argparse
from itertools import combinations, permutations
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
OFFSETS = (3, 5, 7)
CASES = {
    # The complete grade-J source has the three fixed coefficientwise RHS
    # obstructed, while the first shell is the known m5 positive control.
    "m5": (10, 4, 7, 5, 35, 1, 1, 7, 11),
    # This is the first chamber where the coefficientwise J+1 extrapolation
    # is currently suspected to fail.  It is intentionally opt-in because
    # its dense exact row reduction is materially larger.
    "m7": (10, 4, 7, 7, 49, 1, 1, 9, 13),
}


def contact_transition_guard(case):
    """Receipt for the exact contact-order truncation on every matrix edge.

    In the pure-Y expansion, an origin with X-shift q, retained normal power
    f, error choices aE and curvature choices cS survives exactly when

        q + f + 2*aE + cS < m.

    The literal translator records the resulting local monomial with
    T exponent q+f-aE+cS and E exponent aE, whose stored weight is the same
    integer: T+3E=q+f+2*aE+cS.  For a same-grade pure edge this forces
    f<=m-1; the remaining passive exponent supplies the grade refund.
    """
    n, w, _g, multiplicity, degree, _slope, _curvature, active, _seed = case
    maximum_f = min(active, multiplicity - 1)
    passive_refund = active - maximum_f
    width = degree - w * maximum_f
    assert maximum_f < multiplicity
    assert maximum_f + passive_refund == active
    return {
        "exact_edge_guard_pure_Y_notation": "q+f+2*aE+cS<m",
        "stored_local_weight_identity": (
            "(q+f-aE+cS)+3*aE=q+f+2*aE+cS"
        ),
        "same_grade_active_f_h": (active, maximum_f, passive_refund),
        "surviving_same_grade_source_width": width,
        "width_exceeds_all_nodes": width > n,
        "all_node_width_surplus": width - n,
        "stale_Y_active_to_Y_active_minus_1_Z_edge_survives": (
            active - 1 < multiplicity
        ),
    }


def target_transition_guard():
    n, w, g, multiplicity, active = 262_144, 131_071, 180_413, 60, 82
    degree = multiplicity * g
    maximum_f = multiplicity - 1
    passive_refund = active - maximum_f
    width = degree - w * maximum_f
    assert (maximum_f, passive_refund, width) == (59, 23, 3_091_591)
    assert width > n
    assert active - 1 >= multiplicity  # Y^82 -> Y^81 Z is truncated.
    return {
        "parameters_n_w_g_m_D_active": (
            n, w, g, multiplicity, degree, active
        ),
        "same_grade_guard_for_aE_cS_q_zero": "f<60",
        "maximum_surviving_f_minimum_h": (
            maximum_f, passive_refund
        ),
        "width_D_minus_59w": width,
        "width_exceeds_n_by": width - n,
        "Y82_to_Y81Z_survives": False,
    }


def raw_diagonal_extension_receipt(
        n, w, multiplicity, degree, active, slope, curvature):
    """Enumerate the exact q=aE=0 raw-diagonal confluence sector."""
    surviving = 0
    easy = 0
    hard_two_c_gt_r = 0
    hard_curvature_overflow = 0
    easy_minimum_width = None
    for s in range(curvature + 1):
        for r in range(slope - s + 1):
            for f in range(active - r - s + 1):
                for c_s in range(f + 1):
                    # q=aE=0 specialization of q+f+2*aE+cS<m.
                    if f + c_s >= multiplicity:
                        continue
                    surviving += 1
                    if 2 * c_s > r:
                        hard_two_c_gt_r += 1
                        continue
                    if s + c_s > curvature:
                        hard_curvature_overflow += 1
                        continue
                    easy += 1
                    parent = (f + c_s, r - 2 * c_s, s + c_s)
                    target_row = (f + c_s, f - c_s + r, s + c_s)
                    parent_charge = (
                        w * parent[0]
                        + (w - 1) * parent[1]
                        + (w - 2) * parent[2]
                    )
                    origin_charge = (
                        w * f + (w - 1) * r + (w - 2) * s
                    )
                    assert parent_charge == origin_charge
                    assert parent[0] + parent[1] + parent[2] == f + r + s
                    assert parent[1] + parent[2] == r + s - c_s <= slope
                    assert 0 <= parent[2] <= curvature
                    assert target_row[1] >= target_row[0]
                    width = degree - parent_charge
                    assert width > 0
                    easy_minimum_width = (
                        width if easy_minimum_width is None
                        else min(easy_minimum_width, width)
                    )
    assert easy + hard_two_c_gt_r + hard_curvature_overflow == surviving
    return {
        "specialization": "q=0,aE=0",
        "raw_target_T_R_S": "(f+cS,f-cS+r,s+cS)",
        "raw_diagonal_parent_y_r_s": "(f+cS,r-2cS,s+cS)",
        "easy_conditions": "2*cS<=r and s+cS<=curvatureCap",
        "weighted_charge_identity": (
            "w(f+c)+(w-1)(r-2c)+(w-2)(s+c)="
            "wf+(w-1)r+(w-2)s"
        ),
        "surviving_q0_aE0_terms": surviving,
        "easy_raw_diagonal_terms": easy,
        "hard_2cS_gt_r_terms": hard_two_c_gt_r,
        "hard_curvature_overflow_terms_after_2cS_guard":
            hard_curvature_overflow,
        "easy_minimum_source_width": easy_minimum_width,
        "easy_minimum_width_exceeds_all_nodes": easy_minimum_width > n,
        "remaining_genuine_sectors": (
            "aE>0", "2*cS>r", "s+cS>curvatureCap"
        ),
    }


def trim(poly):
    answer = [coefficient % P for coefficient in poly]
    while answer and answer[-1] == 0:
        answer.pop()
    return tuple(answer)


def poly_add(left, right):
    answer = [0] * max(len(left), len(right))
    for index, coefficient in enumerate(left):
        answer[index] = (answer[index] + coefficient) % P
    for index, coefficient in enumerate(right):
        answer[index] = (answer[index] + coefficient) % P
    return trim(answer)


def poly_scale(poly, scalar):
    return trim(tuple(scalar * coefficient % P for coefficient in poly))


def poly_mul(left, right):
    if not left or not right:
        return ()
    answer = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            answer[i + j] = (answer[i + j] + x * y) % P
    return trim(answer)


def polynomial_determinant(matrix):
    size = len(matrix)
    answer = ()
    for permutation in permutations(range(size)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(size) for j in range(i + 1, size)
        )
        term = (1,)
        for row, column in enumerate(permutation):
            term = poly_mul(term, matrix[row][column])
        answer = poly_add(
            answer, poly_scale(term, -1 if inversions % 2 else 1)
        )
    return answer


def polynomial_vector_basis(vectors, coordinates=4):
    """Greedy exact column basis over F_101(X), in the supplied order."""
    chosen = []
    witnesses = []
    for vector in vectors:
        trial = chosen + [vector]
        size = len(trial)
        if size > coordinates:
            break
        witness = None
        for rows in combinations(range(coordinates), size):
            determinant = polynomial_determinant([
                [trial[column][row] for column in range(size)]
                for row in rows
            ])
            if determinant:
                witness = (rows, determinant)
                break
        if witness is not None:
            chosen.append(vector)
            witnesses.append(witness)
            if len(chosen) == coordinates:
                break
    return tuple(chosen), tuple(witnesses)


def polynomial_rank(vectors, coordinates=4):
    return len(polynomial_vector_basis(vectors, coordinates)[0])


def matrix_target_defects(image, target_columns):
    """Exact F_101 column-containment defects without a kernel basis."""
    base_rank = image.rank()
    rows = image.nrows()
    columns = image.ncols()
    individual = []
    for target in target_columns:
        augmented = nmod_mat(rows, columns + 1, [
            (int(image[row, column]) % P if column < columns
             else target[row] % P)
            for row in range(rows) for column in range(columns + 1)
        ], P)
        individual.append(augmented.rank() - base_rank)
    joint = nmod_mat(rows, columns + len(target_columns), [
        (int(image[row, column]) % P if column < columns
         else target_columns[column - columns][row] % P)
        for row in range(rows)
        for column in range(columns + len(target_columns))
    ], P).rank() - base_rank
    return base_rank, tuple(individual), joint


def boundary_vector(source):
    """The four polynomial boundary coordinates of a sparse raw source."""
    units = (
        (1, 0, 0, 0),
        (0, 1, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    )
    vector = []
    for unit in units:
        coefficients = {}
        for (x, y, r, s, z), coefficient in source.items():
            if (y, r, s, z) == unit and coefficient % P:
                coefficients[x] = coefficient % P
        vector.append(trim(tuple(
            coefficients.get(degree, 0)
            for degree in range(max(coefficients, default=-1) + 1)
        )))
    return tuple(vector)


def matrix_from_contact_rows(literal, source_indices, contact_rows):
    """Dense exact contact matrix; J rows are deliberately excluded."""
    return nmod_mat(len(contact_rows), len(source_indices), [
        literal.columns[source_index].get(row, 0) % P
        for row in contact_rows for source_index in source_indices
    ], P)


def first_nonzero_in_rref_row(matrix, row, start):
    column = start
    while column < matrix.ncols() and int(matrix[row, column]) % P == 0:
        column += 1
    assert column < matrix.ncols()
    return column


def transposed_boundary_residues(literal, maximum_grade):
    """Reduce only Y/R/S/Z dual rows modulo the literal contact row space."""
    grades = tuple(sum(monomial[1:]) for monomial in literal.monomials)
    terminal = tuple(
        index for index, grade in enumerate(grades)
        if grade == maximum_grade
    )
    prefix = tuple(
        index for index, grade in enumerate(grades)
        if grade < maximum_grade
    )
    source_indices = terminal + prefix
    source_position = {
        source_index: position
        for position, source_index in enumerate(source_indices)
    }

    active_contact_rows = {
        row
        for source_index in source_indices
        for row in literal.columns[source_index]
        if literal.row_keys[row][0] == "C"
    }
    # This assertion is the literal form of the corrected dependency-graph
    # guard.  It rejects every stale edge at construction time, before any
    # transpose pivot or target test is performed.
    assert all(
        literal.row_keys[row][2][0]
        + 3 * literal.row_keys[row][2][1] < literal.parameters[3]
        for row in active_contact_rows
    )
    top_rows = tuple(sorted(
        (row for row in active_contact_rows
         if sum(literal.row_keys[row][2][1:]) == maximum_grade),
        key=lambda row: repr(literal.row_keys[row]),
    ))
    lower_rows = tuple(sorted(
        active_contact_rows - set(top_rows),
        key=lambda row: repr(literal.row_keys[row]),
    ))
    contact_rows = top_rows + lower_rows
    assert all(
        literal.columns[source_index].get(row, 0) % P == 0
        for row in top_rows for source_index in prefix
    )

    contact = matrix_from_contact_rows(
        literal, source_indices, contact_rows
    )
    contact, contact_rank = contact.rref(inplace=True)

    pivots = []
    next_column = 0
    for row in range(contact_rank):
        pivot = first_nonzero_in_rref_row(contact, row, next_column)
        assert int(contact[row, pivot]) % P == 1
        pivots.append(pivot)
        next_column = pivot + 1
    pivot_to_row = {pivot: row for row, pivot in enumerate(pivots)}
    free_columns = tuple(
        column for column in range(len(source_indices))
        if column not in pivot_to_row
    )
    free_position = {
        column: index for index, column in enumerate(free_columns)
    }

    # For each free source-dual coordinate, accumulate the four polynomial
    # entries of the reduced boundary covectors.  A boundary coefficient row
    # is a standard basis vector, so its RREF remainder is read directly from
    # one pivot row; no ambient quotient basis is generated.
    residue_coefficients = [
        [dict() for _coordinate in range(4)]
        for _free in free_columns
    ]
    units = (
        (1, 0, 0, 0),
        (0, 1, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    )
    monomial_index = {
        monomial: index for index, monomial in enumerate(literal.monomials)
    }
    boundary_positions = []
    for coordinate, unit in enumerate(units):
        for degree in range(literal.parameters[4]):
            monomial = (degree,) + unit
            source_index = monomial_index.get(monomial)
            if source_index is None or source_index not in source_position:
                continue
            boundary_positions.append((coordinate, degree))
            column = source_position[source_index]
            if column in free_position:
                residue_coefficients[free_position[column]][coordinate][
                    degree
                ] = 1
                continue
            row = pivot_to_row[column]
            for free_index, free_column in enumerate(free_columns):
                coefficient = -int(contact[row, free_column]) % P
                if coefficient:
                    residue_coefficients[free_index][coordinate][
                        degree
                    ] = coefficient

    residue_vectors = []
    for entries in residue_coefficients:
        vector = []
        for coefficients in entries:
            vector.append(trim(tuple(
                coefficients.get(degree, 0)
                for degree in range(max(coefficients, default=-1) + 1)
            )))
        vector = tuple(vector)
        if any(vector):
            residue_vectors.append(vector)

    basis, witnesses = polynomial_vector_basis(residue_vectors)
    basis_hash = hashlib.sha256(repr(basis).encode()).hexdigest()
    all_residue_hash = hashlib.sha256(
        repr(tuple(residue_vectors)).encode()
    ).hexdigest()
    witness_receipts = tuple({
        "rows": rows,
        "determinant_degree": len(determinant) - 1,
        "determinant_sha256": hashlib.sha256(
            repr(determinant).encode()
        ).hexdigest(),
    } for rows, determinant in witnesses)

    # The terminal diagonal is the top-row/top-column block.  The transpose
    # RREF used above is the full two-block cone, while this rank permits the
    # exact connecting-rank identity to be checked between consecutive q's.
    top_diagonal = matrix_from_contact_rows(literal, terminal, top_rows)
    top_rank = top_diagonal.rank()

    # An independent, stricter target receipt over F_101 itself.  Rows are
    # the legal coefficient positions of Y/R/S/Z and columns are precisely
    # the free coordinates left by the transposed contact RREF.  This is the
    # boundary image on the complete contact kernel, obtained without asking
    # FLINT for a kernel or ambient-cokernel basis.
    coefficient_image = nmod_mat(
        len(boundary_positions), len(free_columns), [
            residue_coefficients[free_index][coordinate].get(degree, 0)
            for coordinate, degree in boundary_positions
            for free_index in range(len(free_columns))
        ], P)
    yrs_row_indices = tuple(
        row for row, (coordinate, _degree) in enumerate(boundary_positions)
        if coordinate < 3)
    yrs_image = nmod_mat(len(yrs_row_indices), len(free_columns), [
        int(coefficient_image[row, column]) % P
        for row in yrs_row_indices for column in range(len(free_columns))
    ], P)
    normal_vectors = tuple(
        boundary_vector(normal) for normal in literal.locator_normals[:3])
    assert (3, 0) in boundary_positions
    assert all(
        (coordinate, degree) in boundary_positions
        for vector in normal_vectors
        for coordinate in range(3)
        for degree, coefficient in enumerate(vector[coordinate])
        if coefficient
    )
    yrs_targets = tuple(tuple(
        normal_vectors[target][coordinate][degree]
        if degree < len(normal_vectors[target][coordinate]) else 0
        for row in yrs_row_indices
        for coordinate, degree in (boundary_positions[row],)
    ) for target in range(3))
    yrs_rank, yrs_individual, yrs_joint = matrix_target_defects(
        yrs_image, yrs_targets)
    z1 = tuple(
        int(coordinate == 3 and degree == 0)
        for coordinate, degree in boundary_positions)
    full_rank, z1_individual, _z1_joint = matrix_target_defects(
        coefficient_image, (z1,))
    z1_defect = z1_individual[0]

    return {
        "maximum_centered_grade": maximum_grade,
        "source_prefix_terminal_full_dimensions": (
            len(prefix), len(terminal), len(source_indices)
        ),
        "contact_lower_top_full_rows": (
            len(lower_rows), len(top_rows), len(contact_rows)
        ),
        "contact_rank_nullity": (
            contact_rank, len(source_indices) - contact_rank
        ),
        "top_diagonal_rank_nullity": (
            top_rank, len(terminal) - top_rank
        ),
        "boundary_coefficient_rows_reduced": len(boundary_positions),
        "every_literal_contact_edge_obeys_T_plus_3E_lt_m": True,
        "top_contact_rows_vanish_on_lower_prefix_source": True,
        "nonzero_four_residue_columns": len(residue_vectors),
        "four_boundary_rank_over_F101_of_X": len(basis),
        "four_residue_basis_sha256": basis_hash,
        "all_four_residue_columns_sha256": all_residue_hash,
        "successive_minor_witnesses": witness_receipts,
        "coefficientwise_F101_target_gate": {
            "YRS_rows_image_rank": (len(yrs_row_indices), yrs_rank),
            "individual_locator_F0_F1_F2_defects": yrs_individual,
            "joint_locator_F0_F1_F2_defect": yrs_joint,
            "YRSZ_rows_image_rank": (len(boundary_positions), full_rank),
            "pure_constant_Z1_defect": z1_defect,
            "three_rhs_plus_z1": yrs_joint == 0 and z1_defect == 0,
            "ambient_kernel_or_cokernel_generated": False,
        },
        "_basis": basis,
    }


def target_frame(literal):
    locator_targets = []
    for normal in literal.locator_normals[:3]:
        vector = boundary_vector(normal)
        locator_targets.append(vector[:3] + ((),))
    z1 = ((), (), (), (1,))
    targets = tuple(locator_targets) + (z1,)
    target_basis, witnesses = polynomial_vector_basis(targets)
    assert len(target_basis) == 4
    determinant = witnesses[-1][1]
    return targets, {
        "target_names": ("locator_F0", "locator_F1", "locator_F2", "Z1"),
        "frame_rank_over_F101_of_X": 4,
        "frame_determinant_degree": len(determinant) - 1,
        "frame_determinant_sha256": hashlib.sha256(
            repr(determinant).encode()
        ).hexdigest(),
        "target_vectors_sha256": hashlib.sha256(
            repr(targets).encode()
        ).hexdigest(),
    }


def target_defects(residue_basis, targets):
    base_rank = len(residue_basis)
    individual = tuple(
        polynomial_rank(tuple(residue_basis) + (target,)) - base_rank
        for target in targets
    )
    joint = polynomial_rank(tuple(residue_basis) + tuple(targets)) - base_rank
    return individual, joint


def one_case(label):
    case = CASES[label]
    M.PRIME = M.T.PRIME = M.F.PRIME = F.PRIME = P
    literal = M.build_case(
        f"transposed_four_residue_{label}", case,
        actual_agreement_count=7, anchor_count=7, normal_coordinates=3,
        error_direction_offsets=OFFSETS,
    )
    targets, frame_receipt = target_frame(literal)
    before = transposed_boundary_residues(literal, case[7])
    after = transposed_boundary_residues(literal, case[7] + 1)

    for receipt in (before, after):
        individual, joint = target_defects(receipt["_basis"], targets)
        receipt[
            "localized_individual_locator_F0_F1_F2_Z1_defects"
        ] = individual
        receipt["localized_joint_four_target_defect"] = joint
        receipt["localized_four_target_frame_contained"] = joint == 0

    prefix_rank, prefix_nullity = before["contact_rank_nullity"]
    full_rank, full_nullity = after["contact_rank_nullity"]
    top_rank, top_nullity = after["top_diagonal_rank_nullity"]
    prefix_columns = before["source_prefix_terminal_full_dimensions"][2]
    full_columns = after["source_prefix_terminal_full_dimensions"][2]
    assert prefix_columns == after["source_prefix_terminal_full_dimensions"][0]
    assert prefix_columns + after["source_prefix_terminal_full_dimensions"][1] == full_columns
    assert prefix_columns - prefix_rank == prefix_nullity
    assert full_columns - full_rank == full_nullity
    connecting_kernel = full_nullity - prefix_nullity
    connecting_rank = top_nullity - connecting_kernel
    assert connecting_kernel >= 0 and connecting_rank >= 0
    assert top_nullity == connecting_rank + connecting_kernel

    for receipt in (before, after):
        receipt.pop("_basis")
    return {
        "label": label,
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "field": P,
        "error_direction_offsets": OFFSETS,
        "finite_contact_transition_guard": contact_transition_guard(case),
        "target_contact_transition_guard": target_transition_guard(),
        "finite_raw_diagonal_extension": raw_diagonal_extension_receipt(
            case[0], case[1], case[3], case[4], case[7], case[5], case[6]
        ),
        "target_raw_diagonal_extension": raw_diagonal_extension_receipt(
            262_144, 131_071, 60, 60 * 180_413, 82, 21, 10
        ),
        "literal_source_columns": len(literal.monomials),
        "target_frame": frame_receipt,
        "filtered_prefix_receipts": (before, after),
        "J_to_J_plus_1_mapping_cone": {
            "prefix_contact_rank_nullity": (prefix_rank, prefix_nullity),
            "terminal_diagonal_rank_nullity": (top_rank, top_nullity),
            "full_contact_rank_nullity": (full_rank, full_nullity),
            "connecting_rank_kernel": (
                connecting_rank, connecting_kernel
            ),
            "exact_nullity_identity": (
                full_nullity == prefix_nullity + connecting_kernel
                and top_nullity == connecting_rank + connecting_kernel
            ),
        },
        "decision": (
            "GREEN_EXACT_FILTERED_THREE_RHS_PLUS_Z1_AT_J_PLUS_1"
            if after["coefficientwise_F101_target_gate"]
                    ["three_rhs_plus_z1"]
            else (
                "RED_EXACT_FILTERED_DESPITE_LOCALIZED_FOUR_RANK"
                if after["localized_four_target_frame_contained"]
                else "RED_EXACT_FILTERED_AND_LOCALIZED_AT_J_PLUS_1"
            )
        ),
        "scope_guard": (
            "Exact coefficientwise filtered target gate plus an F101(X) "
            "localization diagnostic for one finite chamber; neither a "
            "target theorem nor a counterexample to literal Full187."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=tuple(CASES), default="m5")
    args = parser.parse_args()
    started = time.monotonic()
    payload = one_case(args.case)
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(
        canonical.encode()
    ).hexdigest()
    payload["runtime_receipt"] = {
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "external_memory_cap_bytes": 6 * 1024**3,
        "ambient_kernel_or_cokernel_generated": False,
    }
    payload["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()
    ).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
