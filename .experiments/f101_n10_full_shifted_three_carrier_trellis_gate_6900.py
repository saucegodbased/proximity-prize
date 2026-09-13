#!/usr/bin/env python3
"""Exact full-space gate for the shifted three-carrier seed trellis.

This tests the literal n=10 F101 chamber at the same filtered interface as
the proposed Full187 construction.  The source consists of every column of
total source grade at most J, plus *the whole legal coefficient space* of

  Z^k V^(m-2) Z^b (c V^2 + B V Z + A Lambda Xi V1 Z),

for every shift 0 <= k <= L-(J+1).  We parameterize the agreement
congruence without guessing B:

  r = (c Q + A Xi Lambda') mod Lambda,
  B0 = -r + Lambda H,
  B = B0 + c Q - 2 A Lambda Xi'.

For (n,w,g,m,D,J,L)=(10,4,7,4,28,6,10), literal source legality gives
deg A <= 2, deg c <= 5, deg H <= 2, hence 12 independent generators per
shift.  We compare the matched direction against the fixed error offsets
(3,5,7), using all-node contact rows and the exact F0/F1/F2 polynomial J
right-hand sides.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path
import sys

from flint import nmod_poly

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_n10_grade7_centered_wronskian_universality_6900 as U  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as S  # noqa: E402


P = 101
CASE = (10, 4, 7, 4, 28, 1, 1, 6, 10)
OFFSETS = (3, 5, 7)


def rank(columns):
    return M.modular_rank_sparse(columns)


def dot(functional, column):
    return sum(functional.get(row, 0) * coefficient
               for row, coefficient in column.items()) % P


def left_witness(columns, targets, row_keys):
    """Return a deterministic dual witness when target zero is excluded.

    ``ColumnEchelon`` stores a normalized upper-echelon column for every
    pivot.  Choosing one nonpivot row of the reduced target and solving the
    pivot equations backwards produces an explicit functional annihilating
    the whole source span.
    """
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    remainder = echelon.reduce(targets[0])
    assert remainder
    free_row = min(remainder)
    functional = {free_row: 1}
    for pivot in reversed(sorted(echelon.pivots)):
        value = -sum(
            coefficient * functional.get(row, 0)
            for row, coefficient in echelon.pivots[pivot].items()
            if row != pivot) % P
        if value:
            functional[pivot] = value

    assert all(dot(functional, column) == 0 for column in columns)
    target_values = tuple(dot(functional, target) for target in targets)
    assert target_values[0] == remainder[free_row] != 0

    support_payload = tuple(sorted(
        ((row_keys[row], coefficient) for row, coefficient in functional.items()),
        key=repr))
    categories = Counter(row_keys[row][0] for row in functional)
    contact_nodes = Counter(
        row_keys[row][1] for row in functional if row_keys[row][0] == "C")
    contact_seed_exponents = Counter(
        row_keys[row][2][-1]
        for row in functional if row_keys[row][0] == "C")
    j_coordinates = Counter(
        row_keys[row][1] for row in functional if row_keys[row][0] == "J")
    return {
        "construction": (
            "one free row of the normalized upper-column-echelon remainder, "
            "then exact backward substitution over F101"
        ),
        "source_columns_annihilated": len(columns),
        "source_rank": echelon.rank,
        "functional_support": len(functional),
        "functional_sha256": hashlib.sha256(
            repr(support_payload).encode()).hexdigest(),
        "support_by_C_or_J": tuple(sorted(categories.items())),
        "contact_support_by_node": tuple(sorted(contact_nodes.items())),
        "contact_support_by_seed_exponent": tuple(
            sorted(contact_seed_exponents.items())),
        "J_support_by_normal_coordinate": tuple(sorted(j_coordinates.items())),
        "values_on_F0_F1_F2": target_values,
        "all_source_columns_evaluate_to_zero": True,
    }


def omitted_grade_seven_shape_gate(columns, literal):
    """Locate the smallest literal shape directions that cross the STOP."""
    echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        echelon.add(column, index)
    target_remainders = tuple(echelon.reduce(target)
                              for target in literal.targets)
    assert rank(target_remainders) == 1

    groups = {}
    for index, monomial in enumerate(literal.monomials):
        if sum(monomial[1:]) != CASE[7] + 1:
            continue
        shape = monomial[1:]
        groups.setdefault(shape, []).append((monomial, literal.columns[index]))

    closing_groups = []
    closing_single_columns = []
    group_defect_histogram = Counter()
    for shape, entries in sorted(groups.items()):
        remainders = tuple(echelon.reduce(column) for _monomial, column in entries)
        group_rank = rank(remainders)
        defect = rank(remainders + target_remainders) - group_rank
        group_defect_histogram[defect] += 1
        if defect == 0:
            closing_groups.append({
                "shape_y_r_s_z": shape,
                "literal_columns": len(entries),
                "quotient_rank": group_rank,
            })
        for monomial, column in entries:
            remainder = echelon.reduce(column)
            column_rank = rank((remainder,))
            column_defect = rank((remainder,) + target_remainders) - column_rank
            if column_defect == 0:
                closing_single_columns.append(monomial)

    return {
        "candidate_grade": CASE[7] + 1,
        "shape_groups_tested": len(groups),
        "single_literal_columns_tested": sum(len(entries)
                                              for entries in groups.values()),
        "group_joint_defect_histogram": tuple(
            sorted(group_defect_histogram.items())),
        "closing_shape_groups": tuple(closing_groups),
        "closing_single_literal_columns_x_y_r_s_z": tuple(
            closing_single_columns),
    }


def compound_order_four_shift_gate(literal, base):
    """Test the newly found coupled order-four correction and all shifts."""
    indices, _contact, _nullity, _image, lifts = U.solve_restricted(literal)
    terminal_sources = []
    for _name, vector in lifts:
        source = {
            literal.monomials[source_index]: int(vector[row, 0]) % P
            for row, source_index in enumerate(indices)
            if int(vector[row, 0]) % P
            and sum(literal.monomials[source_index][1:]) == CASE[7] + 1
        }
        assert source_legal(source, CASE)
        terminal_sources.append(source)

    pivot = next(iter(terminal_sources[0]))
    scales = []
    for source in terminal_sources:
        scale = (source[pivot]
                 * pow(terminal_sources[0][pivot], -1, P)) % P
        assert source == {
            monomial: coefficient * scale % P
            for monomial, coefficient in terminal_sources[0].items()
            if coefficient * scale % P
        }
        scales.append(scale)
    assert tuple(scales) == (1, 11, 46)

    source_index = {monomial: index
                    for index, monomial in enumerate(literal.monomials)}
    compound = terminal_sources[0]
    image = S.indexed_image(literal, compound, source_index)
    assert not any(
        literal.row_keys[row][0] == "C"
        and literal.row_keys[row][1] in literal.actual_agreement
        for row in image)
    contact_rows = tuple(
        (literal.row_keys[row], coefficient)
        for row, coefficient in image.items()
        if literal.row_keys[row][0] == "C")
    seed_support = Counter(row[2][-1] for row, _coefficient in contact_rows)
    min_seed = min(seed_support)
    leading = tuple(sorted(
        ((row, coefficient) for row, coefficient in contact_rows
         if row[2][-1] == min_seed), key=repr))
    assert leading

    accumulated = list(base)
    previous_rank = rank(accumulated)
    rows = []
    for shift in range(CASE[8] - CASE[7]):
        shifted_source = shifted(compound, shift)
        assert source_legal(shifted_source, CASE)
        shifted_image = S.indexed_image(literal, shifted_source, source_index)
        accumulated.append(shifted_image)
        current_rank = rank(accumulated)
        individual = tuple(
            rank(accumulated + [target]) - current_rank
            for target in literal.targets)
        joint = rank(accumulated + list(literal.targets)) - current_rank
        rows.append({
            "shift": shift,
            "source_grade": CASE[7] + 1 + shift,
            "rank_increment": current_rank - previous_rank,
            "individual_F0_F1_F2_defects": individual,
            "joint_defect": joint,
        })
        previous_rank = current_rank
    assert all(row["rank_increment"] == 1 for row in rows)
    assert rows[0]["joint_defect"] == 0

    return {
        "construction": (
            "canonical exact grade-seven correction; independently "
            "decomposed into eight Lambda/V/J1 order-four carriers"
        ),
        "F0_F1_F2_compound_scales": tuple(scales),
        "compound_source_support": len(compound),
        "compound_source_sha256": S.source_hash(compound),
        "contact_seed_support": tuple(sorted(seed_support.items())),
        "lowest_seed": min_seed,
        "lowest_seed_block_support": len(leading),
        "lowest_seed_pivot_row_and_value": leading[0],
        "lowest_seed_block_sha256": hashlib.sha256(
            repr(leading).encode()).hexdigest(),
        "cumulative_shift_receipts": tuple(rows),
    }


def monomial_poly(power):
    return nmod_poly([0] * power + [1], P)


def shifted(source, amount):
    return {
        (xp, yp, rp, sp, zp + amount): coefficient
        for (xp, yp, rp, sp, zp), coefficient in source.items()
    }


def source_legal(source, parameters):
    _n, w, _g, _m, degree, slope, curvature, jet, seed = parameters
    return all(
        rp + sp <= slope
        and sp <= curvature
        and yp + rp + sp <= jet
        and yp + rp + sp + zp <= seed
        and xp + w * yp + (w - 1) * rp + (w - 2) * sp < degree
        for xp, yp, rp, sp, zp in source
    )


def carrier_source(literal, A, c, H):
    xi = nmod_poly(list(literal.xi), P)
    q = nmod_poly(list(literal.q), P)
    locator = nmod_poly(list(literal.locator), P)
    xi1 = xi.derivative()
    locator1 = locator.derivative()
    _quotient, remainder = divmod(c * q + A * xi * locator1, locator)
    B0 = -remainder + locator * H
    B = B0 + c * q - 2 * A * locator * xi1
    source = S.terminal_source(
        S.poly_tuple(A), S.poly_tuple(B), S.poly_tuple(c),
        literal.xi, literal.q, literal.locator, CASE[3], CASE[7])
    return source, B0, B


def carrier_generators(literal):
    zero = nmod_poly([], P)

    # The exact literal caps, not extrapolated target caps.
    parameters = []
    parameters += [("A", i, monomial_poly(i), zero, zero)
                   for i in range(3)]
    parameters += [("c", i, zero, monomial_poly(i), zero)
                   for i in range(6)]
    parameters += [("H", i, zero, zero, monomial_poly(i))
                   for i in range(3)]

    generators = []
    receipts = []
    for kind, power, A, c, H in parameters:
        source, B0, B = carrier_source(literal, A, c, H)
        assert source
        assert source_legal(source, CASE), (kind, power)
        assert all(sum(monomial[1:]) == CASE[7] + 1
                   for monomial in source)
        generators.append(source)
        receipts.append({
            "parameter": (kind, power),
            "degrees_A_c_H_B0_B": (
                A.degree(), c.degree(), H.degree(), B0.degree(), B.degree()),
            "source_support": len(source),
            "source_sha256": S.source_hash(source),
        })
    return tuple(generators), tuple(receipts)


def maximal_legal_parameter_space_receipt(literal):
    """Prove the 12 displayed generators exhaust the legal family.

    Unique raw endpoints first bound A by 2, c by 11, and H by 2.  On that
    18-dimensional enclosing box, the forbidden-source-coordinate map has
    rank six.  The explicit A<=2,c<=5,H<=2 coordinate subspace has dimension
    12 and maps to zero, so it is exactly the legal kernel.
    """
    zero = nmod_poly([], P)
    enclosing = []
    enclosing += [("A", i, monomial_poly(i), zero, zero)
                  for i in range(3)]
    enclosing += [("c", i, zero, monomial_poly(i), zero)
                  for i in range(12)]
    enclosing += [("H", i, zero, zero, monomial_poly(i))
                  for i in range(3)]
    forbidden_columns = []
    for _kind, _power, A, c, H in enclosing:
        source, _B0, _B = carrier_source(literal, A, c, H)
        forbidden_columns.append({
            monomial: coefficient
            for monomial, coefficient in source.items()
            if not source_legal({monomial: coefficient}, CASE)
        })
    forbidden_rank = M.modular_rank_sparse(forbidden_columns)
    low_indices = tuple(
        index for index, (kind, power, _A, _c, _H) in enumerate(enclosing)
        if kind != "c" or power <= 5)
    low_dimension = 3 + 6 + 3
    assert len(enclosing) == 18
    assert len(low_indices) == low_dimension
    assert all(not forbidden_columns[index] for index in low_indices)
    assert forbidden_rank == 6
    assert len(enclosing) - forbidden_rank == low_dimension
    return {
        "endpoint_enclosing_degree_caps_A_c_H": (2, 11, 2),
        "enclosing_parameter_dimension": len(enclosing),
        "forbidden_source_coordinate_rank": forbidden_rank,
        "legal_kernel_dimension": len(enclosing) - forbidden_rank,
        "explicit_legal_coordinate_dimension_A_c_H": (3, 6, 3),
        "explicit_legal_coordinates_exhaust_kernel": True,
    }


def one_case(offsets):
    label = "matched" if offsets is None else "offsets_3_5_7"
    literal = M.build_case(
        label, CASE, actual_agreement_count=7, anchor_count=7,
        normal_coordinates=3, error_direction_offsets=offsets)
    source_index = {monomial: index
                    for index, monomial in enumerate(literal.monomials)}

    base_indices = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= CASE[7])
    base = tuple(literal.columns[index] for index in base_indices)
    base_rank = rank(base)
    generators, generator_receipts = carrier_generators(literal)

    rows = []
    accumulated = list(base)
    previous_rank = base_rank
    for shift in range(CASE[8] - CASE[7]):
        layer_sources = tuple(shifted(source, shift) for source in generators)
        assert all(source_legal(source, CASE) for source in layer_sources)
        layer_columns = tuple(
            S.indexed_image(literal, source, source_index)
            for source in layer_sources)
        # Agreement cycles remain exact even with error-direction offsets.
        assert all(not any(
            literal.row_keys[row][0] == "C"
            and literal.row_keys[row][1] in literal.actual_agreement
            for row in column)
            for column in layer_columns)
        accumulated.extend(layer_columns)
        current_rank = rank(accumulated)
        individual = tuple(
            rank(accumulated + [target]) - current_rank
            for target in literal.targets)
        joint = rank(accumulated + list(literal.targets)) - current_rank
        rows.append({
            "shift": shift,
            "source_grade": CASE[7] + 1 + shift,
            "generators_added": len(layer_columns),
            "rank_increment": current_rank - previous_rank,
            "rank": current_rank,
            "individual_F0_F1_F2_defects": individual,
            "joint_defect": joint,
        })
        previous_rank = current_rank

    result = {
        "case": label,
        "error_direction_offsets": offsets,
        "base_grade_at_most": CASE[7],
        "base_columns_rank": (len(base), base_rank),
        "carrier_parameter_dimensions_A_c_H": (3, 6, 3),
        "maximal_legal_parameter_space":
            maximal_legal_parameter_space_receipt(literal),
        "carrier_generators": generator_receipts,
        "cumulative_shift_receipts": tuple(rows),
    }
    if offsets is not None:
        result["final_exact_dual_witness"] = left_witness(
            accumulated, literal.targets, literal.row_keys)
        result["omitted_grade_seven_shape_gate"] = (
            omitted_grade_seven_shape_gate(accumulated, literal))
        result["compound_order_four_shift_gate"] = (
            compound_order_four_shift_gate(literal, base))
    return result


def main():
    M.T.PRIME = M.F.PRIME = S.T.PRIME = S.F.PRIME = P
    payload = {
        "scope": (
            "Whole legal n=10 three-carrier parameter space in every "
            "available seed shift; literal all-node C and exact F0/F1/F2 J"
        ),
        "field": P,
        "parameters_n_w_g_m_D_s_t_J_L": CASE,
        "cases": (one_case(None), one_case(OFFSETS)),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
