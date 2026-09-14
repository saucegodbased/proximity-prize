#!/usr/bin/env python3
"""Coefficientwise Z1 filtration in the smallest cap-rich positive control.

Unlike the older polynomial-boundary rank receipt, this asks whether the
literal contact kernel contains the exact boundary vector with every Y/R/S
coefficient zero, constant Z coefficient one, and every other Z coefficient
zero.  It records this at every centered total-grade prefix.  This is a
finite-control discriminator, not a target theorem.
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
import full187_anchor_zero_boundary_degree_audit_6900 as A  # noqa: E402
import full187_anchor_zero_yrs_z_split_audit_6900 as Z  # noqa: E402
import full187_total_degree_mapping_cone_gate_6900 as K  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as S  # noqa: E402


P = 7
CASE = (6, 2, 4, 3, 12, 2, 1, 5, 5)


def horizontal_concat(left: nmod_mat, right: nmod_mat) -> nmod_mat:
    assert left.nrows() == right.nrows()
    return nmod_mat(left.nrows(), left.ncols() + right.ncols(), [
        int(left[i, j]) if j < left.ncols()
        else int(right[i, j - left.ncols()])
        for i in range(left.nrows())
        for j in range(left.ncols() + right.ncols())
    ], P)


def target_defect(image: nmod_mat, target: tuple[int, ...]) -> int:
    vector = nmod_mat(len(target), 1, target, P)
    return horizontal_concat(image, vector).rank() - image.rank()


def vertical_concat(top: nmod_mat, bottom: nmod_mat) -> nmod_mat:
    assert top.ncols() == bottom.ncols()
    return nmod_mat(top.nrows() + bottom.nrows(), top.ncols(), [
        int(top[i, j]) if i < top.nrows()
        else int(bottom[i - top.nrows(), j])
        for i in range(top.nrows() + bottom.nrows())
        for j in range(top.ncols())
    ], P)


def locator_on(nodes: tuple[int, ...]) -> tuple[int, ...]:
    polynomial = (1,)
    for node in nodes:
        polynomial = A.poly_mul(polynomial, ((-node) % P, 1), P)
    return polynomial


def full_shifted_target_gate(node_values: tuple[int, ...]) -> dict:
    """Exact full-grade gate on a supplied six-node affine domain."""
    n, w, g, multiplicity, degree, slope, curvature, active, combined = CASE
    assert len(node_values) == n and len(set(node_values)) == n
    agreements = node_values[:g]
    anchors = agreements[:w + 1]
    anchor_locator = locator_on(anchors)
    agreement_locator = locator_on(agreements)
    u1 = tuple(A.poly_eval(anchor_locator, node, P) for node in node_values)
    u0 = (0,) * g + (1,) * (n - g)
    monomials = S.support(w, degree, slope, curvature, active, combined)
    columns = []
    for xpower, value, first, second, seed in monomials:
        column = {}
        for node_index, node in enumerate(node_values):
            for local, coefficient in translated_column(
                    xpower, (value, first, second), seed, node,
                    u0[node_index], u1[node_index], multiplicity, 2, P).items():
                if coefficient:
                    column[(node_index, local)] = coefficient
        columns.append(column)
    contact_rows = tuple(sorted(
        {row for column in columns for row in column}, key=repr))
    contact = nmod_mat(len(contact_rows), len(columns), [
        column.get(row, 0) for row in contact_rows for column in columns
    ], P)
    kernel, nullity = K.compact_nullspace(contact)
    units = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 1, 0), (0, 0, 0, 1),
    )
    monomial_set = set(monomials)
    boundary_positions = tuple(
        (coordinate, xpower)
        for coordinate, unit in enumerate(units)
        for xpower in range(degree)
        if (xpower,) + unit in monomial_set)
    monomial_index = {monomial: i for i, monomial in enumerate(monomials)}
    boundary = nmod_mat(len(boundary_positions), len(monomials), [
        int(column == monomial_index[(xpower,) + units[coordinate]])
        for coordinate, xpower in boundary_positions
        for column in range(len(monomials))
    ], P)
    image = boundary * kernel
    pure_z1 = tuple(
        int(coordinate == 3 and xpower == 0)
        for coordinate, xpower in boundary_positions)
    locator_at_zero = A.poly_eval(agreement_locator, 0, P)
    normalized_locator = (
        A.poly_scale(agreement_locator, pow(locator_at_zero, -1, P), P)
        if locator_at_zero else None)
    normalized_locator_z = (
        tuple(
            (normalized_locator[xpower]
             if coordinate == 3 and xpower < len(normalized_locator) else 0)
            for coordinate, xpower in boundary_positions)
        if normalized_locator is not None else None)
    stacked = vertical_concat(contact, boundary)

    def both_defects(target):
        kernel_defect = target_defect(image, target)
        direct_defect = target_defect(
            stacked, (0,) * len(contact_rows) + target)
        assert kernel_defect == direct_defect
        return kernel_defect, direct_defect

    # Exact four agreement rows.  The first three are the centered locator
    # normals.  For the fourth, H is the w+1 anchor set, q_H interpolates u1
    # there (zero in this control), and
    # B=Lambda_H^(m-1)*Lambda_(G\H)^m.
    F.PRIME = P
    F.GAMMA = 0
    F.MULTIPLICITY = multiplicity
    first_three = F.centered_locator_normals(
        agreement_locator, (0,), anchor_locator)
    remaining_locator = locator_on(agreements[w + 1:])
    factor = F.poly_mul(
        F.poly_pow(anchor_locator, multiplicity - 1),
        F.poly_pow(remaining_locator, multiplicity))
    q_h = (0,)
    fourth = F.sparse_mul(F.sparse_embed_x(factor), F.Y)
    exact_normals = first_three + (fourth,)

    def source_legal(source):
        return all(
            y + r + s <= active
            and r + s <= slope
            and s <= curvature
            and z + y + r + s <= combined
            and xpower + w * y + (w - 1) * r + (w - 2) * s < degree
            for (xpower, y, r, s, z) in source)

    assert all(source_legal(normal) for normal in exact_normals)
    exact_targets = tuple(tuple(
        normal.get((xpower,) + units[coordinate], 0) % P
        for coordinate, xpower in boundary_positions)
        for normal in exact_normals)
    exact_defects = tuple(both_defects(target)[0] for target in exact_targets)
    exact_target_matrix = nmod_mat(
        len(boundary_positions), len(exact_targets), [
            exact_targets[column][row]
            for row in range(len(boundary_positions))
            for column in range(len(exact_targets))
        ], P)
    exact_joint_defect = (
        horizontal_concat(image, exact_target_matrix).rank() - image.rank())
    padded_exact_target_matrix = nmod_mat(
        len(contact_rows) + len(boundary_positions), len(exact_targets), [
            (0 if row < len(contact_rows)
             else exact_targets[column][row - len(contact_rows)])
            for row in range(len(contact_rows) + len(boundary_positions))
            for column in range(len(exact_targets))
        ], P)
    exact_joint_direct_defect = (
        horizontal_concat(stacked, padded_exact_target_matrix).rank()
        - stacked.rank())
    assert exact_joint_direct_defect == exact_joint_defect

    monomial_index = {monomial: i for i, monomial in enumerate(monomials)}
    normal_contact_supports = []
    for normal in exact_normals:
        contact_image = {}
        for monomial, scalar in normal.items():
            for row, coefficient in columns[monomial_index[monomial]].items():
                value = (contact_image.get(row, 0) + scalar * coefficient) % P
                if value:
                    contact_image[row] = value
                else:
                    contact_image.pop(row, None)
        assert not any(row[0] < g for row in contact_image)
        normal_contact_supports.append(len(contact_image))
    assert normal_contact_supports[3] > 0

    return {
        "domain_nodes": node_values,
        "agreement_nodes": agreements,
        "anchor_nodes": anchors,
        "zero_is_in_domain": 0 in node_values,
        "agreement_locator_coefficients": agreement_locator,
        "agreement_locator_at_zero": locator_at_zero,
        "normalized_locator_coefficients": normalized_locator,
        "contact_rank_nullity": (contact.rank(), nullity),
        "coefficient_boundary_image_rank": image.rank(),
        "pure_constant_Z_kernel_direct_defects": both_defects(pure_z1),
        "normalized_agreement_locator_Z_kernel_direct_defects": (
            both_defects(normalized_locator_z)
            if normalized_locator_z is not None else None),
        "exact_F0_F1_F2_F3": {
            "q_H_coefficients": q_h,
            "B_coefficients": factor,
            "individual_coefficientwise_defects": exact_defects,
            "joint_coefficientwise_defect": exact_joint_defect,
            "joint_direct_stacked_defect": exact_joint_direct_defect,
            "contact_supports_F0_F1_F2_F3": tuple(normal_contact_supports),
            "all_agreement_contacts_zero": True,
            "F3_error_syndrome_nonzero": True,
            "all_source_legal": True,
        },
    }


def main() -> None:
    started = time.monotonic()
    n, w, g, multiplicity, degree, slope, curvature, active, combined = CASE
    S.PRIME = P
    A.M.P = P
    K.P = P
    locator = A.locator(w, P)
    u1 = tuple(A.poly_eval(locator, node, P) for node in range(n))
    u0 = (0,) * g + (1,) * (n - g)
    all_monomials = S.support(
        w, degree, slope, curvature, active, combined)

    all_columns = []
    for xpower, value, first, second, seed in all_monomials:
        column = {}
        for node in range(n):
            for local, coefficient in translated_column(
                    xpower, (value, first, second), seed, node,
                    u0[node], u1[node], multiplicity, 2, P).items():
                if coefficient:
                    column[(node, local)] = coefficient
        all_columns.append(column)

    rows = []
    units = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 1, 0), (0, 0, 0, 1),
    )
    for maximum_grade in range(1, combined + 1):
        selected = tuple(
            index for index, monomial in enumerate(all_monomials)
            if sum(monomial[1:]) <= maximum_grade)
        monomials = tuple(all_monomials[index] for index in selected)
        columns = tuple(all_columns[index] for index in selected)
        contact_rows = tuple(sorted(
            {row for column in columns for row in column}, key=repr))
        contact = nmod_mat(len(contact_rows), len(columns), [
            column.get(row, 0)
            for row in contact_rows for column in columns
        ], P)
        kernel, nullity = K.compact_nullspace(contact)

        boundary_positions = tuple(
            (coordinate, xpower)
            for coordinate, unit in enumerate(units)
            for xpower in range(degree)
            if (xpower,) + unit in set(monomials)
        )
        monomial_index = {monomial: i for i, monomial in enumerate(monomials)}
        boundary = nmod_mat(
            len(boundary_positions), len(monomials), [
                int(column == monomial_index[(xpower,) + units[coordinate]])
                for coordinate, xpower in boundary_positions
                for column in range(len(monomials))
            ], P)
        image = boundary * kernel
        yrs_indices = tuple(
            i for i, (coordinate, _xpower) in enumerate(boundary_positions)
            if coordinate < 3)
        yrs = nmod_mat(len(yrs_indices), nullity, [
            int(image[i, column])
            for i in yrs_indices for column in range(nullity)
        ], P)
        z1 = tuple(
            int(coordinate == 3 and xpower == 0)
            for coordinate, xpower in boundary_positions)
        z1_defect = target_defect(image, z1)
        # Independent direct system: solve C*x=0 and B*x=Z1 at once, rather
        # than first generating ker C.  This catches orientation mistakes in
        # the kernel-boundary calculation.
        stacked = vertical_concat(contact, boundary)
        stacked_target = (0,) * len(contact_rows) + z1
        direct_z1_defect = target_defect(stacked, stacked_target)
        assert direct_z1_defect == z1_defect

        polynomial_vectors = A.polynomial_boundary_vectors(
            monomials, kernel, P)
        localized_yrs_rank = Z.polynomial_vector_rank(
            tuple(vector[:3] for vector in polynomial_vectors), 3, P)
        localized_full_rank = Z.polynomial_vector_rank(
            polynomial_vectors, 4, P)
        rows.append({
            "maximum_centered_total_grade": maximum_grade,
            "source_columns": len(monomials),
            "contact_rank_nullity": (contact.rank(), nullity),
            "boundary_coefficient_rows_image_rank": (
                len(boundary_positions), image.rank()),
            "YRS_coefficient_image_rank": yrs.rank(),
            "residual_Z_image_dimension": image.rank() - yrs.rank(),
            "pure_constant_Z1_defect": z1_defect,
            "direct_stacked_contact_boundary_Z1_defect": direct_z1_defect,
            "localized_F7_of_X_YRS_full_ranks": (
                localized_yrs_rank, localized_full_rank),
        })

    signatures = tuple(
        (row["maximum_centered_total_grade"], row["source_columns"],
         row["contact_rank_nullity"],
         row["boundary_coefficient_rows_image_rank"],
         row["YRS_coefficient_image_rank"],
         row["pure_constant_Z1_defect"],
         row["localized_F7_of_X_YRS_full_ranks"])
        for row in rows)
    assert signatures == (
        (1, 57, (57, 0), (45, 0), 0, 1, (0, 0)),
        (2, 150, (150, 0), (45, 0), 0, 1, (0, 0)),
        (3, 281, (275, 6), (45, 4), 4, 1, (3, 3)),
        (4, 440, (412, 28), (45, 9), 9, 1, (3, 4)),
        (5, 617, (545, 72), (45, 9), 9, 1, (3, 4)),
    )

    # The original toy domain contains zero.  The actual multiplicative NTT
    # domain does not, so run the affine-translated six-point domain F_7^* and
    # test the normalized agreement-locator Z target explicitly.
    shifted_gate = full_shifted_target_gate((1, 2, 3, 4, 5, 6))
    assert shifted_gate["agreement_locator_at_zero"] != 0

    stable = {
        "scope": (
            "complete literal F7 cap-rich coefficientwise contact/boundary "
            "filtration; finite control, not target theorem"
        ),
        "parameters_N_w_g_m_D_s_t_J_L": CASE,
        "received_direction": "Lambda_{0,1,2}",
        "rows": tuple(rows),
        "shifted_nonzero_domain_full_grade_gate": shifted_gate,
        "decision": (
            "GREEN_EXACT_FOUR_PACKET_SHIFTED_CONTROL_AND_STOP_NAIVE_Z_TARGETS"
        ),
        "scope_guard": (
            "This corrects the interpretation of one finite positive "
            "control.  It does not imply target Z1 failure."
        ),
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
