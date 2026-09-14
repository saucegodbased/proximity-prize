#!/usr/bin/env python3
"""Target-faithful nonzero-q_H test of the safe terminal packet gate.

This is deliberately a separate executable from
``safe_terminal_subsource_surjectivity_audit_6900.py``.  Its finite chamber,
direction, and safe/unsafe deletion are declared below before any rank is
computed.  In particular, unlike the earlier controls, q_H is nonzero (and
nonconstant), so F3 contains the literal hard term ``-B Z q_H``.

The output tests both:

* rank four of the boundary map on the complete-contact kernel over F_p(X);
* direct coefficientwise containment of all four exact packet columns.

It is a structural falsifier/control, not a proof of the Full187 target.
"""

from __future__ import annotations

import gc
import hashlib
import json
from pathlib import Path
import resource
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
import safe_terminal_subsource_surjectivity_audit_6900 as A  # noqa: E402
import asymmetric_second_jet_6900 as H  # noqa: E402
import prime_o2_conormal_threshold_falsifier as S  # noqa: E402
from higher_jet_literal_matrix import translated_column  # noqa: E402


# Predeclared from the nearly dimension-tight chamber in the parent audit.
# Its safe/unsafe split depends only on this ledger, not on the rank answer.
CONTROL = {
    "prime": 1009,
    "n": 18,
    "w": 8,
    "g": 14,
    "m": 6,
    "D": 84,
    "q": 4,
    "t": 1,
    "J": 5,
    "L": 5,
}

# q_H = 1 + X is fixed independently of the rank computation.  The retained
# direction is Q_G = q_H + Lambda_H, so Q_G-q_H has degree w+1 > w.
Q_H = (1, 1)

# Optional replay changes no source parameter, agreement value, packet, or
# safe/unsafe shape.  It perturbs only the four error-node U1 values, thereby
# removing the accidental hypothesis that all U1 values come from one global
# polynomial.  These offsets are fixed before the replay rank is computed.
ERROR_U1_OFFSETS = (37, 74, 111, 148)


def horizontal_concat(left: nmod_mat, right: nmod_mat,
                      prime: int) -> nmod_mat:
    assert left.nrows() == right.nrows()
    return nmod_mat(left.nrows(), left.ncols() + right.ncols(), [
        int(left[i, j]) if j < left.ncols()
        else int(right[i, j - left.ncols()])
        for i in range(left.nrows())
        for j in range(left.ncols() + right.ncols())
    ], prime)


def compact_nullspace(matrix: nmod_mat, prime: int):
    raw, nullity = matrix.nullspace()
    compact = nmod_mat(matrix.ncols(), nullity, [
        int(raw[i, j]) % prime
        for i in range(matrix.ncols()) for j in range(nullity)
    ], prime)
    assert matrix * compact == nmod_mat(matrix.nrows(), nullity, prime)
    return compact, nullity


def pivot_columns_of_rref(matrix: nmod_mat):
    reduced, rank = matrix.rref()
    pivots = []
    for row in range(rank):
        pivot = next(column for column in range(reduced.ncols())
                     if int(reduced[row, column]))
        assert int(reduced[row, pivot]) == 1
        pivots.append(pivot)
    assert len(set(pivots)) == rank
    return tuple(pivots), rank


def add_scaled(target, source, scalar, prime):
    for row, value in source.items():
        new = (target.get(row, 0) + scalar * value) % prime
        if new:
            target[row] = new
        else:
            target.pop(row, None)


def run_control(perturb_error_values: bool = False):
    case = CONTROL
    prime = case["prime"]
    S.PRIME = prime
    n, w, g = case["n"], case["w"], case["g"]
    m, D = case["m"], case["D"]
    q, t, J, L = case["q"], case["t"], case["J"], case["L"]
    required_margin = n - g

    ledger = A.dimension_ledger(case, required_margin)
    safe, unsafe, _ = A.safe_polytope(case, required_margin)
    assert ledger["terminal_shape_count_safe_unsafe"] == (9, 8, 1)
    assert safe == (
        (0, 0), (1, 0), (2, 0), (3, 0), (4, 0),
        (0, 1), (1, 1), (2, 1),
    )
    assert unsafe == ((3, 1),)
    assert ledger["full_euler_surplus"] == 54
    assert ledger["restricted_euler_surplus"] == 5
    assert ledger["restricted_surplus_after_four_boundary_rows"] == 1

    all_monomials = S.support(w, D, q, t, J, L)

    def retained(monomial):
        _xp, y, r, s, z = monomial
        terminal_last_shell = y + r + s == J and y + r + s + z == L
        return not (terminal_last_shell and (r, s) in unsafe)

    monomials = tuple(x for x in all_monomials if retained(x))
    assert len(all_monomials) - len(monomials) == ledger[
        "safe_unsafe_terminal_width"][1]

    # Nonzero nodes mirror the target NTT domain's exclusion of X=0.
    nodes = tuple(range(1, n + 1))
    agreement = nodes[:g]
    errors = nodes[g:]
    anchors = nodes[:w + 1]
    u0 = (0,) * g + (1,) * (n - g)

    lambda_h = A.locator(anchors, prime)
    direction_polynomial = A.poly_add(Q_H, lambda_h, prime)
    relative = A.poly_add(
        direction_polynomial, A.poly_scale(Q_H, -1, prime), prime)
    assert relative == lambda_h
    assert len(direction_polynomial) - 1 == w + 1
    assert len(relative) - 1 == w + 1 > w
    polynomial_values = tuple(
        A.poly_eval(direction_polynomial, node, prime) for node in nodes)
    offsets = ((0,) * g + ERROR_U1_OFFSETS
               if perturb_error_values else (0,) * n)
    assert len(offsets) == n
    values = tuple((value + offset) % prime
                   for value, offset in zip(polynomial_values, offsets))
    qh_values = tuple(A.poly_eval(Q_H, node, prime) for node in nodes)
    assert all(values)
    assert all(qh_values)
    assert values[:g] == polynomial_values[:g]
    assert all(values[i] == qh_values[i] for i in range(w + 1))
    assert any(values[i] != qh_values[i] for i in range(w + 1, n))
    if perturb_error_values:
        assert all(offsets[g:])
        assert values[g:] != polynomial_values[g:]

    all_columns_by_monomial = {}
    for monomial in all_monomials:
        xp, y, r, s, z = monomial
        column = {}
        for node_index, node in enumerate(nodes):
            expansion = translated_column(
                xp, (y, r, s), z, node, u0[node_index], values[node_index],
                m, 2, prime)
            for local, coefficient in expansion.items():
                if coefficient:
                    column[(node, local)] = coefficient
        all_columns_by_monomial[monomial] = column

    local_rows = tuple(sorted({
        local for column in all_columns_by_monomial.values()
        for node, local in column if node == nodes[0]
    }, key=repr))
    local_at_first = nmod_mat(len(local_rows), len(all_monomials), [
        all_columns_by_monomial[monomial].get((nodes[0], local), 0)
        for local in local_rows for monomial in all_monomials
    ], prime)
    pivot_indices, local_rank = pivot_columns_of_rref(
        local_at_first.transpose())
    expected_local_rank = ledger[
        "full_source_one_node_contact_all_node_contact"][1]
    assert local_rank == expected_local_rank
    pivot_locals = tuple(local_rows[index] for index in pivot_indices)
    for node in nodes:
        projection = nmod_mat(len(pivot_locals), len(all_monomials), [
            all_columns_by_monomial[monomial].get((node, local), 0)
            for local in pivot_locals for monomial in all_monomials
        ], prime)
        assert projection.rank() == expected_local_rank

    rows = tuple((node, local) for node in nodes for local in pivot_locals)
    columns = tuple(all_columns_by_monomial[x] for x in monomials)
    contact = nmod_mat(len(rows), len(columns), [
        column.get(row, 0) for row in rows for column in columns
    ], prime)
    contact_rank = contact.rank()
    kernel, nullity = compact_nullspace(contact, prime)

    # The weaker CS4 gate over F_p(X).
    kernel_boundary_vectors = A.boundary_vectors(
        monomials, kernel, prime)
    kernel_boundary_rank = A.polynomial_vector_rank(
        kernel_boundary_vectors, 4, prime)
    identity = nmod_mat(len(monomials), len(monomials), prime)
    for index in range(len(monomials)):
        identity[index, index] = 1
    full_boundary_rank = A.polynomial_vector_rank(
        A.boundary_vectors(monomials, identity, prime), 4, prime)
    assert full_boundary_rank == 4

    # Exact F0..F3.  Recompute q_H inside the production helper and assert it
    # is exactly our fixed nonconstant Q_H.
    normals, normal_data = A.exact_four_normals(
        case, agreement, anchors, direction_polynomial)
    assert tuple(normal_data["anchor_interpolant_q_H_coefficients"]) == Q_H
    assert normal_data["relative_direction_Q_G_minus_q_H_degree"] == w + 1
    monomial_index = {monomial: index
                      for index, monomial in enumerate(monomials)}
    assert all(all(x in monomial_index for x in normal) for normal in normals)

    normal_contact_supports = []
    for normal in normals:
        image = {}
        for monomial, scalar in normal.items():
            add_scaled(image, all_columns_by_monomial[monomial],
                       scalar, prime)
        assert not any(node in agreement for node, _local in image)
        assert any(node in errors for node, _local in image)
        normal_contact_supports.append(len(image))

    units = (
        (1, 0, 0, 0), (0, 1, 0, 0),
        (0, 0, 1, 0), (0, 0, 0, 1),
    )
    boundary_positions = tuple(
        (coordinate, xp)
        for coordinate, unit in enumerate(units)
        for xp in range(D)
        if (xp,) + unit in monomial_index)
    boundary = nmod_mat(len(boundary_positions), len(monomials), [
        int(column == monomial_index[(xp,) + units[coordinate]])
        for coordinate, xp in boundary_positions
        for column in range(len(monomials))
    ], prime)
    coefficient_image = boundary * kernel
    targets = tuple(tuple(
        normal.get((xp,) + units[coordinate], 0) % prime
        for coordinate, xp in boundary_positions)
        for normal in normals)
    target_matrix = nmod_mat(len(boundary_positions), 4, [
        targets[column][row]
        for row in range(len(boundary_positions))
        for column in range(4)
    ], prime)
    image_rank = coefficient_image.rank()
    individual_defects = tuple(
        horizontal_concat(
            coefficient_image,
            nmod_mat(len(boundary_positions), 1, target, prime),
            prime,
        ).rank() - image_rank
        for target in targets)
    joint_defect = horizontal_concat(
        coefficient_image, target_matrix, prime).rank() - image_rank

    del all_columns_by_monomial, contact, kernel, identity
    gc.collect()

    return {
        "predeclared_parameters": case,
        "nodes_are_nonzero": all(nodes),
        "nodes_agreements_errors_anchors": (
            nodes, agreement, errors, anchors),
        "safe_terminal_shapes": safe,
        "unsafe_terminal_shapes": unsafe,
        "unsafe_terminal_width": ledger["safe_unsafe_terminal_width"][1],
        "full_restricted_after_four_surpluses": (
            ledger["full_euler_surplus"],
            ledger["restricted_euler_surplus"],
            ledger["restricted_surplus_after_four_boundary_rows"],
        ),
        "q_H_coefficients": Q_H,
        "q_H_is_nonzero_and_nonconstant": Q_H != () and len(Q_H) > 1,
        "Q_G_coefficients": direction_polynomial,
        "agreement_U1_values_equal_Q_G": (
            values[:g] == polynomial_values[:g]),
        "error_U1_offsets": offsets[g:],
        "error_U1_values": values[g:],
        "error_U1_values_differ_from_global_Q_G": (
            values[g:] != polynomial_values[g:]),
        "all_actual_U1_values_are_nonzero": all(values),
        "Q_G_minus_q_H_equals_Lambda_H": relative == lambda_h,
        "Q_G_minus_q_H_degree_and_exceeds_w": (
            len(relative) - 1, len(relative) - 1 > w),
        "source_and_contact_dimensions": (len(monomials), len(rows)),
        "restricted_contact_rank_nullity_defect": (
            contact_rank, nullity, len(rows) - contact_rank),
        "fraction_field_boundary_rank_full_and_kernel": (
            full_boundary_rank, kernel_boundary_rank),
        "fraction_field_CS4_green": kernel_boundary_rank == 4,
        "boundary_coefficient_positions_and_image_rank": (
            len(boundary_positions), image_rank),
        "normal_contact_supports_F0_F1_F2_F3": tuple(
            normal_contact_supports),
        "all_four_source_legal_and_agreement_contact_zero": True,
        "individual_coefficientwise_defects_F0_F1_F2_F3": (
            individual_defects),
        "joint_coefficientwise_defect": joint_defect,
        "direct_coefficientwise_four_packet_green": joint_defect == 0,
        "F3_contains_nonzero_hard_minus_BZq_H": bool(Q_H),
        "normal_metadata": normal_data,
    }


def main():
    perturb = "--offset-errors" in sys.argv
    result = run_control(perturb_error_values=perturb)
    result["decision"] = (
        "GREEN" if result["fraction_field_CS4_green"]
        and result["direct_coefficientwise_four_packet_green"] else "RED")
    result["scope"] = (
        "predeclared finite structural discriminator; not the Full187 "
        "uniform recurrence theorem")
    result["peak_rss_kib"] = resource.getrusage(
        resource.RUSAGE_SELF).ru_maxrss
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    result["canonical_sha256"] = hashlib.sha256(
        canonical.encode()).hexdigest()
    result["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
