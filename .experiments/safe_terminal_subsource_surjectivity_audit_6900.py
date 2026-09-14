#!/usr/bin/env python3
"""Audit the proposed Full187 safe-terminal subsource surjectivity step.

The target q=0 corner calculation singles out 105 terminal derivative shapes
and proposes deleting the other 82 shapes from the last passive shell.  This
script keeps that operation logically separate from the rank conclusion it
would need: surjectivity of contact after imposing zero boundary.

It provides:

* an independently recomputed exact target dimension ledger; and
* literal finite controls with the analogous safe polytope computed from the
  same inequalities, not selected by hand; and
* direct coefficientwise containment of the exact F0,F1,F2,F3 packets in the
  boundary image of the restricted complete-contact kernel.

For a contact matrix C and a four-row boundary matrix B(x),

  rank(C restricted to ker B(x)) = rank([C; B(x)]) - rank(B(x)).

Thus the claimed surjectivity requires this difference to equal every
canonical contact row.  The controls use the complete literal order-two
translation matrix and retain the same bad direction used throughout the
Full187 audits: u1 has w+1 forced anchor zeros and is therefore not the
restriction of a degree-at-most-w polynomial.

This is a finite structural discriminator, not a target theorem.
"""

from __future__ import annotations

import gc
import hashlib
from itertools import combinations, permutations
import json
from pathlib import Path
import resource
import sys

from flint import nmod_mat

sys.path.insert(0, ".experiments")
from higher_jet_literal_matrix import translated_column  # noqa: E402
import asymmetric_second_jet_6900 as H  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402
import prime_o2_conormal_threshold_falsifier as S  # noqa: E402


TARGET = {
    "n": 262_144,
    "w": 131_071,
    "g": 180_413,
    "m": 60,
    "D": 10_824_780,
    "q": 21,
    "t": 10,
    "J": 82,
    "L": 2703,
}
TARGET_FULL_SURPLUS = 9_757_693

# This is the smallest convenient N=2w+2 control found with all of:
# positive strict widths, a nontrivial safe/unsafe split, and positive Euler
# room after the unsafe terminal face and four boundary rows are removed.
CONTROL = {
    "prime": 1009,
    "n": 22,
    "w": 10,
    "g": 17,
    "m": 4,
    "D": 68,
    "q": 3,
    "t": 1,
    "J": 5,
    "L": 5,
}

SECONDARY_CONTROL = {
    "prime": 211,
    "n": 10,
    "w": 4,
    "g": 7,
    "m": 5,
    "D": 35,
    "q": 4,
    "t": 1,
    "J": 7,
    "L": 7,
}

# Chosen by ledger alone, before constructing its contact matrix.  It leaves
# only five source coordinates beyond the canonical contact target and hence
# only one after reserving all four named packet rows.
TIGHT_CONTROL = {
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


def derivative_shapes(q: int, t: int) -> tuple[tuple[int, int], ...]:
    return tuple((r, s) for s in range(t + 1)
                 for r in range(q - s + 1))


def coefficient_width(D: int, w: int, y: int, r: int, s: int) -> int:
    return D - w * y - (w - 1) * r - (w - 2) * s


def safe_polytope(case: dict[str, int], required_margin: int = 0):
    """Classify terminal shapes by the exact q=0 low-T corner condition."""
    D, w, g = case["D"], case["w"], case["g"]
    m, q, t, J = case["m"], case["q"], case["t"], case["J"]
    safe = []
    unsafe = []
    corner_occurrences = {}
    for r, s in derivative_shapes(q, t):
        y = J - r - s
        assert y >= 0
        bad = []
        for f in range(min(m - 1, y) + 1):
            lower_width = coefficient_width(D, w, f, r, s)
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    contact_weight = f + 2 * a_e + c_s
                    if contact_weight >= m:
                        continue
                    depth = m - contact_weight
                    if lower_width - g * depth >= required_margin:
                        continue
                    T = f - a_e + c_s
                    E = a_e
                    R = f - a_e - c_s + r
                    SS = s + c_s
                    d = E + R + SS
                    residual = max(E + SS - t, 0)
                    minimum_a0 = max(0, d - q)
                    maximum_a0 = min(R, T - 2 * residual)
                    if minimum_a0 > maximum_a0:
                        bad.append((f, a_e, c_s))
        corner_occurrences[(r, s)] = tuple(bad)
        (unsafe if bad else safe).append((r, s))
    return tuple(safe), tuple(unsafe), corner_occurrences


def derivative_count(q: int, t: int) -> int:
    return sum(q - s + 1 for s in range(min(q, t) + 1))


def derivative_moment(q: int, t: int) -> int:
    return sum((q - s) * (q - s + 1) // 2
               + 2 * s * (q - s + 1)
               for s in range(min(q, t) + 1))


def source_layer(case: dict[str, int], d: int) -> int:
    qd = min(d, case["q"])
    return (derivative_count(qd, case["t"])
            * (case["D"] - case["w"] * d)
            + derivative_moment(qd, case["t"]))


def local_layer(case: dict[str, int], d: int) -> int:
    return H.local_rank_layer(case["m"], d, case["q"], case["t"])


def dimension_ledger(case: dict[str, int], required_margin: int = 0):
    safe, unsafe, origins = safe_polytope(case, required_margin)
    J, L = case["J"], case["L"]
    source = sum((L - d + 1) * source_layer(case, d)
                 for d in range(J + 1))
    one_node = sum((L - d + 1) * local_layer(case, d)
                   for d in range(J + 1))
    target = case["n"] * one_node
    unsafe_width = sum(coefficient_width(
        case["D"], case["w"], J - r - s, r, s)
        for r, s in unsafe)
    safe_width = sum(coefficient_width(
        case["D"], case["w"], J - r - s, r, s)
        for r, s in safe)
    return {
        "required_capacity_margin": required_margin,
        "terminal_shape_count_safe_unsafe": (
            len(safe) + len(unsafe), len(safe), len(unsafe)),
        "safe_terminal_shapes": safe,
        "unsafe_terminal_shapes": unsafe,
        "corner_occurrence_count_by_shape": tuple(
            (shape, len(origins[shape]))
            for shape in derivative_shapes(case["q"], case["t"])),
        "safe_unsafe_terminal_width": (safe_width, unsafe_width),
        "full_source_one_node_contact_all_node_contact": (
            source, one_node, target),
        "full_euler_surplus": source - target,
        "restricted_source_dimension": source - unsafe_width,
        "restricted_euler_surplus": source - unsafe_width - target,
        "restricted_surplus_after_four_boundary_rows": (
            source - unsafe_width - target - 4),
    }


def poly_mul(left, right, prime):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % prime
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


def poly_eval(polynomial, x, prime):
    value = 0
    for coefficient in reversed(polynomial):
        value = (value * x + coefficient) % prime
    return value


def poly_add(left, right, prime):
    out = [0] * max(len(left), len(right))
    for i in range(len(out)):
        out[i] = ((left[i] if i < len(left) else 0)
                  + (right[i] if i < len(right) else 0)) % prime
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


def poly_scale(polynomial, scalar, prime):
    out = [scalar * value % prime for value in polynomial]
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


def locator(nodes, prime):
    out = (1,)
    for node in nodes:
        out = poly_mul(out, ((-node) % prime, 1), prime)
    return out


def determinant(matrix, prime):
    size = len(matrix)
    answer = ()
    for permutation in permutations(range(size)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(size)
                         for j in range(i + 1, size))
        term = (1,)
        for row, column in enumerate(permutation):
            term = poly_mul(term, matrix[row][column], prime)
        answer = poly_add(answer, poly_scale(
            term, -1 if inversions % 2 else 1, prime), prime)
    return answer


def polynomial_vector_rank(vectors, coordinates, prime):
    """Exact greedy rank over F_p(X), with at most four coordinates."""
    chosen = []
    for vector in vectors:
        trial = chosen + [vector]
        size = len(trial)
        if size > coordinates:
            break
        independent = any(
            determinant([[trial[column][row] for column in range(size)]
                         for row in rows], prime)
            for rows in combinations(range(coordinates), size))
        if independent:
            chosen.append(vector)
            if len(chosen) == coordinates:
                break
    return len(chosen)


def compact_nullspace(matrix: nmod_mat, prime: int):
    raw, nullity = matrix.nullspace()
    compact = nmod_mat(matrix.ncols(), nullity, [
        int(raw[i, j]) % prime
        for i in range(matrix.ncols()) for j in range(nullity)
    ], prime)
    assert matrix * compact == nmod_mat(matrix.nrows(), nullity, prime)
    return compact, nullity


def horizontal_concat(left: nmod_mat, right: nmod_mat,
                      prime: int) -> nmod_mat:
    assert left.nrows() == right.nrows()
    return nmod_mat(left.nrows(), left.ncols() + right.ncols(), [
        int(left[i, j]) if j < left.ncols()
        else int(right[i, j - left.ncols()])
        for i in range(left.nrows())
        for j in range(left.ncols() + right.ncols())
    ], prime)


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


def boundary_vectors(monomials, coefficients, prime):
    """Four polynomial boundary coordinates of each coefficient column."""
    units = ((1, 0, 0, 0), (0, 1, 0, 0),
             (0, 0, 1, 0), (0, 0, 0, 1))
    vectors = []
    for relation in range(coefficients.ncols()):
        vector = []
        for unit in units:
            polynomial = {}
            for row, (xp, y, r, s, z) in enumerate(monomials):
                if (y, r, s, z) != unit:
                    continue
                value = int(coefficients[row, relation]) % prime
                if value:
                    polynomial[xp] = value
            vector.append(tuple(polynomial.get(i, 0)
                                for i in range(max(polynomial, default=-1) + 1)))
        vectors.append(tuple(vector))
    return tuple(vectors)


def add_scaled(target, source, scalar, prime):
    for row, value in source.items():
        new = (target.get(row, 0) + scalar * value) % prime
        if new:
            target[row] = new
        else:
            target.pop(row, None)


def exact_four_normals(case, agreement, anchors, direction):
    """Build the exact-cardinality F0,F1,F2,F3 packet."""
    prime, m = case["prime"], case["m"]
    F.PRIME = prime
    F.MULTIPLICITY = m
    F.GAMMA = 0
    locator_g = F.locator(agreement)
    first_three = F.centered_locator_normals(locator_g, (0,), direction)
    q_h_raw = S.interpolate(
        tuple(poly_eval(direction, node, prime) for node in anchors),
        anchors)
    q_h = F.poly_trim(q_h_raw)
    assert len(q_h) - 1 <= case["w"]
    assert all(F.poly_eval(q_h, node) == F.poly_eval(direction, node)
               for node in anchors)
    complement = tuple(node for node in agreement if node not in anchors)
    lambda_h = F.locator(anchors)
    lambda_b = F.locator(complement)
    factor = F.poly_mul(
        F.poly_pow(lambda_h, m - 1), F.poly_pow(lambda_b, m))
    bracket = F.sparse_add(
        F.Y, F.sparse_mul(F.Z, F.sparse_embed_x(q_h)), -1)
    fourth = F.sparse_mul(F.sparse_embed_x(factor), bracket)
    return first_three + (fourth,), {
        "agreement_locator_degree": len(locator_g) - 1,
        "anchor_interpolant_q_H_coefficients": q_h,
        "partial_locator_factor_degree": len(factor) - 1,
        "relative_direction_Q_G_minus_q_H_degree": len(
            F.poly_add(direction, q_h, -1)) - 1,
    }


def literal_control(direction: str, case=None):
    case = CONTROL if case is None else case
    prime = case["prime"]
    S.PRIME = prime
    n, w, g = case["n"], case["w"], case["g"]
    m, D = case["m"], case["D"]
    q, t, J, L = case["q"], case["t"], case["J"], case["L"]
    required_margin = n - g
    safe, unsafe, _origins = safe_polytope(case, required_margin)
    all_monomials = S.support(w, D, q, t, J, L)
    assert len(all_monomials) == dimension_ledger(case, required_margin)[
        "full_source_one_node_contact_all_node_contact"][0]

    def retained(monomial):
        _xp, y, r, s, z = monomial
        terminal_last_shell = y + r + s == J and y + r + s + z == L
        return not (terminal_last_shell and (r, s) in unsafe)

    monomials = tuple(monomial for monomial in all_monomials
                      if retained(monomial))
    assert len(all_monomials) - len(monomials) == dimension_ledger(
        case, required_margin)[
        "safe_unsafe_terminal_width"][1]

    # Mirror the target NTT domain's crucial exclusion of X=0.
    nodes = tuple(range(1, n + 1))
    agreement = nodes[:g]
    errors = nodes[g:]
    u0 = (0,) * g + (1,) * (n - g)
    anchors = nodes[:w + 1]
    bad_polynomial = locator(anchors, prime)
    assert len(bad_polynomial) - 1 == w + 1
    bad_values = tuple(poly_eval(bad_polynomial, node, prime)
                       for node in nodes)
    assert all(bad_values[index] == 0
               for index in range(w + 1))
    assert all(bad_values[index] != 0
               for index in range(w + 1, n))
    values = (0,) * n if direction == "matched" else bad_values

    # Construct columns for the full row universe first.  Deleted columns
    # stay deleted, but rows which lose all support remain target rows.
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
                    row = (node, local)
                    column[row] = coefficient
        all_columns_by_monomial[monomial] = column

    # The raw translated quotient has more coordinate rows than the image of
    # the capped one-node source.  Choose pivot coordinate rows of that local
    # image, and verify that the same coordinates are faithful at every node.
    # This realizes exactly `local_rank`, rather than silently asking for
    # surjectivity onto unreachable ambient quotient monomials.
    local_rows = tuple(sorted({
        local for column in all_columns_by_monomial.values()
        for node, local in column if node == nodes[0]
    }, key=repr))
    local_at_zero = nmod_mat(len(local_rows), len(all_monomials), [
        all_columns_by_monomial[monomial].get((nodes[0], local), 0)
        for local in local_rows for monomial in all_monomials
    ], prime)
    pivot_indices, local_rank = pivot_columns_of_rref(
        local_at_zero.transpose())
    expected_local_rank = dimension_ledger(case, required_margin)[
        "full_source_one_node_contact_all_node_contact"][1]
    assert local_rank == expected_local_rank
    pivot_locals = tuple(local_rows[index] for index in pivot_indices)
    for node in nodes:
        local_projection = nmod_mat(len(pivot_locals), len(all_monomials), [
            all_columns_by_monomial[monomial].get((node, local), 0)
            for local in pivot_locals for monomial in all_monomials
        ], prime)
        assert local_projection.rank() == expected_local_rank

    rows = tuple((node, local) for node in nodes for local in pivot_locals)
    assert len(rows) == dimension_ledger(case, required_margin)[
        "full_source_one_node_contact_all_node_contact"][2]
    columns = tuple(all_columns_by_monomial[monomial]
                    for monomial in monomials)
    full_columns = tuple(all_columns_by_monomial[monomial]
                         for monomial in all_monomials)
    unrestricted_contact = nmod_mat(len(rows), len(full_columns), [
        column.get(row, 0) for row in rows for column in full_columns
    ], prime)
    unrestricted_contact_rank = unrestricted_contact.rank()
    del unrestricted_contact
    gc.collect()
    contact = nmod_mat(len(rows), len(columns), [
        column.get(row, 0) for row in rows for column in columns
    ], prime)
    contact_rank = contact.rank()

    kernel, nullity = compact_nullspace(contact, prime)
    kernel_vectors = boundary_vectors(monomials, kernel, prime)
    kernel_boundary_rank = polynomial_vector_rank(kernel_vectors, 4, prime)
    identity = nmod_mat(len(monomials), len(monomials), prime)
    for index in range(len(monomials)):
        identity[index, index] = 1
    full_boundary_rank = polynomial_vector_rank(
        boundary_vectors(monomials, identity, prime), 4, prime)
    restricted_contact_rank = (
        contact_rank + kernel_boundary_rank - full_boundary_rank)

    coefficientwise_packet_gate = None
    if direction == "retained_bad":
        normals, normal_data = exact_four_normals(
            case, agreement, anchors, bad_polynomial)
        monomial_index = {monomial: index
                          for index, monomial in enumerate(monomials)}
        assert all(all(monomial in monomial_index for monomial in normal)
                   for normal in normals)

        # Literal agreement-contact check for each named row.  Their contact
        # images may be nonzero only on error nodes.
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
        individual_defects = []
        for target in targets:
            vector = nmod_mat(len(boundary_positions), 1, target, prime)
            individual_defects.append(
                horizontal_concat(coefficient_image, vector, prime).rank()
                - image_rank)
        joint_defect = horizontal_concat(
            coefficient_image, target_matrix, prime).rank() - image_rank
        coefficientwise_packet_gate = {
            **normal_data,
            "boundary_coefficient_position_count": len(boundary_positions),
            "complete_kernel_coefficient_boundary_image_rank": image_rank,
            "normal_contact_supports_F0_F1_F2_F3": tuple(
                normal_contact_supports),
            "all_four_source_legal_and_agreement_contact_zero": True,
            "individual_coefficientwise_defects_F0_F1_F2_F3": tuple(
                individual_defects),
            "joint_coefficientwise_defect": joint_defect,
            "all_four_coefficientwise_contained": joint_defect == 0,
        }

    return {
        "direction": direction,
        "nodes_agreements_errors_anchors": (
            nodes, agreement, errors, anchors),
        "u0_values": u0,
        "u1_polynomial_degree_and_values": (
            (0 if direction == "matched" else len(bad_polynomial) - 1),
            values),
        "retained_bad_degree_exceeds_w": (
            direction == "retained_bad" and len(bad_polynomial) - 1 > w),
        "source_and_contact_dimensions": (len(monomials), len(rows)),
        "unrestricted_contact_rank_defect": (
            unrestricted_contact_rank, len(rows) - unrestricted_contact_rank),
        "contact_rank_nullity_defect": (
            contact_rank, nullity, len(rows) - contact_rank),
        "boundary_rank_full_source_and_contact_kernel": (
            full_boundary_rank, kernel_boundary_rank),
        "contact_rank_on_zero_boundary_and_defect": (
            restricted_contact_rank, len(rows) - restricted_contact_rank),
        "zero_boundary_contact_surjective": restricted_contact_rank == len(rows),
        "exact_four_packet_coefficientwise_gate": coefficientwise_packet_gate,
    }


def target_ledger():
    agreement = dimension_ledger(TARGET, required_margin=0)
    safe = agreement["safe_terminal_shapes"]
    unsafe = agreement["unsafe_terminal_shapes"]
    assert len(safe) == 105
    assert len(unsafe) == 82
    assert all(r + s <= 16 and r + 4 * s <= 33 for r, s in safe)
    assert all(not (r + s <= 16 and r + 4 * s <= 33)
               for r, s in unsafe)
    assert agreement["full_euler_surplus"] == TARGET_FULL_SURPLUS
    assert agreement["safe_unsafe_terminal_width"] == (8_081_883, 6_312_464)
    assert agreement["restricted_euler_surplus"] == 3_445_229
    assert agreement["restricted_surplus_after_four_boundary_rows"] == 3_445_225

    affine = dimension_ledger(
        TARGET, required_margin=TARGET["n"] - TARGET["g"])
    assert affine["required_capacity_margin"] == 81_731
    assert affine["terminal_shape_count_safe_unsafe"] == (187, 103, 84)
    assert set(safe) - set(affine["safe_terminal_shapes"]) == {
        (5, 7), (1, 8)}
    assert affine["safe_unsafe_terminal_width"] == (7_927_931, 6_466_416)
    assert affine["restricted_euler_surplus"] == 3_291_277
    assert affine["restricted_surplus_after_four_boundary_rows"] == 3_291_273
    return {
        "agreement_Hermite_105_shape_ledger": agreement,
        "affine_error_CRT_103_shape_ledger": affine,
        "lost_when_retaining_arbitrary_error_values": ((1, 8), (5, 7)),
    }


def main() -> None:
    target = target_ledger()
    control_ledger = dimension_ledger(
        CONTROL, required_margin=CONTROL["n"] - CONTROL["g"])
    assert control_ledger["terminal_shape_count_safe_unsafe"] == (7, 6, 1)
    assert control_ledger["safe_terminal_shapes"] == (
        (0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1))
    assert control_ledger["unsafe_terminal_shapes"] == ((2, 1),)
    assert control_ledger["full_euler_surplus"] == 83
    assert control_ledger["restricted_euler_surplus"] == 61
    assert control_ledger["restricted_surplus_after_four_boundary_rows"] == 57

    secondary_ledger = dimension_ledger(
        SECONDARY_CONTROL,
        required_margin=SECONDARY_CONTROL["n"] - SECONDARY_CONTROL["g"])
    assert secondary_ledger["terminal_shape_count_safe_unsafe"] == (9, 8, 1)
    assert secondary_ledger["unsafe_terminal_shapes"] == ((3, 1),)
    assert secondary_ledger["restricted_surplus_after_four_boundary_rows"] == 174

    tight_ledger = dimension_ledger(
        TIGHT_CONTROL,
        required_margin=TIGHT_CONTROL["n"] - TIGHT_CONTROL["g"])
    assert tight_ledger["terminal_shape_count_safe_unsafe"] == (9, 8, 1)
    assert tight_ledger["unsafe_terminal_shapes"] == ((3, 1),)
    assert tight_ledger["full_euler_surplus"] == 54
    assert tight_ledger["restricted_euler_surplus"] == 5
    assert tight_ledger["restricted_surplus_after_four_boundary_rows"] == 1

    controls = (
        literal_control("retained_bad"),
        literal_control("retained_bad", SECONDARY_CONTROL),
        literal_control("retained_bad", TIGHT_CONTROL),
        literal_control("matched"),
    )
    result = {
        "scope": (
            "exact target dimension ledger plus literal finite structural "
            "controls for safe-terminal subsource; not a target rank proof"),
        "target_parameters": TARGET,
        "target_ledger": target,
        "control_parameters": CONTROL,
        "control_ledger": control_ledger,
        "secondary_control_parameters": SECONDARY_CONTROL,
        "secondary_control_ledger": secondary_ledger,
        "tight_control_parameters": TIGHT_CONTROL,
        "tight_control_ledger": tight_ledger,
        "literal_controls": controls,
        "decision": (
            "STOP blanket contact-on-zero-boundary surjectivity: the exact "
            "retained-bad controls have defects 156, 73, and 194 despite "
            "positive Euler room. In particular, blanket defect 194 persists "
            "in the tight chamber with only one dimension left after its "
            "four-row reservation, so packet specificity is essential. "
            "GREEN for both weaker relevant gates: the restricted "
            "complete-contact kernel has boundary rank 4 over F_1009(X), "
            "and its coefficientwise boundary image jointly contains the "
            "four exact F0,F1,F2,F3 packet columns in every control. This is "
            "finite evidence, not the target recurrence theorem."),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":"))
    result["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    result["script_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    if "--compact" in sys.argv:
        compact_target = {}
        for label, ledger in target.items():
            if not isinstance(ledger, dict):
                compact_target[label] = ledger
                continue
            compact_target[label] = {
                key: value for key, value in ledger.items()
                if key not in {
                    "safe_terminal_shapes", "unsafe_terminal_shapes",
                    "corner_occurrence_count_by_shape"}}
        compact_control = {
            key: value for key, value in control_ledger.items()
            if key != "corner_occurrence_count_by_shape"}
        printable = dict(result)
        printable["target_ledger"] = compact_target
        printable["control_ledger"] = compact_control
        printable["secondary_control_ledger"] = {
            key: value for key, value in secondary_ledger.items()
            if key != "corner_occurrence_count_by_shape"}
        printable["tight_control_ledger"] = {
            key: value for key, value in tight_ledger.items()
            if key != "corner_occurrence_count_by_shape"}
    else:
        printable = result
    print(json.dumps(printable, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
