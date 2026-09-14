#!/usr/bin/env python3
"""Exact endpoint interaction gate for the complete-depth projection.

The Full187 complete-depth Pascal/Hermite projection uses final-grade raw
source blocks

    X^d Y^f R^r S^s Z^(L-f-r-s),  0 <= f < m,

with a canonical all-node Hermite prefix of length ``(qmax+1)n``.  This
script asks whether adjoining the exact analogue of those endpoint blocks
changes the authoritative F101 arbitrary-direction STOP for the shifted
three-carrier trellis.

The test is deliberately stronger than merely replaying the prescribed
Pascal recurrence: it adjoins every individual monomial column in every
complete correction prefix and every terminal-origin coefficient column,
all independently.  It also tests whether a separator can be supported only
below the smallest correction seed; that tempting stronger claim is false.
The actual augmented separator necessarily couples passive seeds.

The final section audits the literal Full187 raw support intersection with
the three- and eight-carrier terminal layers.  It is a coordinate/interface
receipt, not an assertion that overlapping affine prescriptions are
compatible.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, ".experiments")
import f101_n10_full_shifted_three_carrier_trellis_gate_6900 as T  # noqa: E402
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as S  # noqa: E402
import full187_packet_vs_deep_slide_filtration_separator_6900 as PS  # noqa: E402
import full187_target_charge13_transposed_four_residue_gate_6900 as FT  # noqa: E402


P = 101
CASE = T.CASE
OFFSETS = T.OFFSETS


def rank(columns):
    return M.modular_rank_sparse(columns)


def dot(functional, column):
    return sum(functional.get(row, 0) * value
               for row, value in column.items()) % P


def defects(columns, targets):
    base_rank = rank(columns)
    return (
        tuple(rank(tuple(columns) + (target,)) - base_rank
              for target in targets),
        rank(tuple(columns) + tuple(targets)) - base_rank,
    )


def defects_mod_echelon(echelon, targets):
    remainders = tuple(echelon.reduce(target) for target in targets)
    return (tuple(int(bool(remainder)) for remainder in remainders),
            rank(remainders))


def all_shapes(slope, curvature):
    return tuple((r, s) for s in range(curvature + 1)
                 for r in range(slope - s + 1))


def complete_qmax(case, r, s, f):
    n, w, _g, m, degree, _slope, _curvature, _jet, _seed = case
    width = degree - w * f - (w - 1) * r - (w - 2) * s
    depth = width // n
    assert depth >= 1
    return min(depth - 1, m - f - 1)


def endpoint_blocks(literal):
    n, w, _g, m, degree, slope, curvature, jet, seed = CASE
    monomial_index = {monomial: index
                      for index, monomial in enumerate(literal.monomials)}
    blocks = []
    for r, s in all_shapes(slope, curvature):
        for f in range(m):
            qmax = complete_qmax(CASE, r, s, f)
            prefix = (qmax + 1) * n
            width = degree - w * f - (w - 1) * r - (w - 2) * s
            z = seed - f - r - s
            assert f + r + s <= jet
            assert 0 < prefix <= width
            monomials = tuple((x, f, r, s, z) for x in range(prefix))
            assert all(monomial in monomial_index for monomial in monomials)
            blocks.append({
                "label": (r, s, f),
                "qmax": qmax,
                "width": width,
                "prefix": prefix,
                "minimum_seed": z,
                "indices": tuple(monomial_index[monomial]
                                 for monomial in monomials),
                "full_indices": tuple(
                    monomial_index[(x, f, r, s, z)] for x in range(width)),
            })
    return tuple(blocks)


def terminal_origin_columns(literal):
    """Every literal coefficient column of the final-grade terminal streams."""
    n, w, _g, _m, degree, slope, curvature, jet, seed = CASE
    del n
    monomial_index = {monomial: index
                      for index, monomial in enumerate(literal.monomials)}
    receipts = []
    indices = []
    for r, s in all_shapes(slope, curvature):
        y = jet - r - s
        z = seed - jet
        width = degree - w * y - (w - 1) * r - (w - 2) * s
        block = tuple(monomial_index[(x, y, r, s, z)]
                      for x in range(width))
        indices.extend(block)
        receipts.append({
            "r_s": (r, s),
            "y_z": (y, z),
            "literal_coefficient_columns": width,
        })
    return tuple(indices), tuple(receipts)


def restrict(column, allowed_rows):
    return {row: value for row, value in column.items()
            if row in allowed_rows}


def separating_functional(columns, targets, allowed_rows, row_keys):
    """Deterministic exact dual supported on ``allowed_rows``."""
    restricted_columns = tuple(restrict(column, allowed_rows)
                               for column in columns)
    restricted_targets = tuple(restrict(target, allowed_rows)
                               for target in targets)
    echelon = M.ColumnEchelon()
    for index, column in enumerate(restricted_columns):
        echelon.add(column, index)
    remainders = tuple(echelon.reduce(target)
                       for target in restricted_targets)
    pivot_target = next((index for index, remainder in enumerate(remainders)
                         if remainder), None)
    if pivot_target is None:
        return None, {
            "allowed_row_count": len(allowed_rows),
            "restricted_source_rank": echelon.rank,
            "restricted_individual_and_joint_defects":
                defects(restricted_columns, restricted_targets),
            "separating_functional_exists": False,
        }
    free_row = min(remainders[pivot_target])
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
    assert target_values[pivot_target]
    support = tuple(sorted(
        ((row_keys[row], coefficient)
         for row, coefficient in functional.items()), key=repr))
    seed_histogram = Counter(
        row_keys[row][2][-1] for row in functional
        if row_keys[row][0] == "C")
    categories = Counter(row_keys[row][0] for row in functional)
    contact_nodes = Counter(row_keys[row][1] for row in functional
                            if row_keys[row][0] == "C")
    boundary_coordinates = Counter(row_keys[row][1] for row in functional
                                   if row_keys[row][0] == "J")
    return functional, {
        "allowed_row_count": len(allowed_rows),
        "restricted_source_rank": echelon.rank,
        "functional_support": len(functional),
        "support_sha256": hashlib.sha256(repr(support).encode()).hexdigest(),
        "support_by_C_or_J": tuple(sorted(categories.items())),
        "contact_support_by_node": tuple(sorted(contact_nodes.items())),
        "contact_seed_histogram": tuple(sorted(seed_histogram.items())),
        "boundary_support_by_normal_coordinate":
            tuple(sorted(boundary_coordinates.items())),
        "values_on_F0_F1_F2": target_values,
    }


def f101_endpoint_gate():
    M.T.PRIME = M.F.PRIME = S.T.PRIME = S.F.PRIME = P
    literal = M.build_case(
        "complete_projection_endpoint_offsets_3_5_7", CASE,
        actual_agreement_count=7, anchor_count=7, normal_coordinates=3,
        error_direction_offsets=OFFSETS)
    base_indices = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= CASE[7])
    columns = [literal.columns[index] for index in base_indices]
    generators, _receipts = T.carrier_generators(literal)
    for shift in range(CASE[8] - CASE[7]):
        for source in generators:
            shifted = T.shifted(source, shift)
            columns.append(S.indexed_image(
                literal, shifted,
                {monomial: index for index, monomial
                 in enumerate(literal.monomials)}))
    assert len(columns) == 1399
    before = defects(tuple(columns), literal.targets)
    assert before == ((1, 1, 1), 1)

    blocks = endpoint_blocks(literal)
    endpoint_indices = tuple(dict.fromkeys(
        index for block in blocks for index in block["indices"]))
    endpoint_columns = tuple(literal.columns[index]
                             for index in endpoint_indices)
    full_endpoint_indices = tuple(dict.fromkeys(
        index for block in blocks for index in block["full_indices"]))
    full_endpoint_columns = tuple(literal.columns[index]
                                  for index in full_endpoint_indices)
    minimum_endpoint_seed = min(block["minimum_seed"] for block in blocks)
    assert minimum_endpoint_seed == 6
    assert all(not any(
        literal.row_keys[row][0] == "C"
        and literal.row_keys[row][2][-1] < minimum_endpoint_seed
        for row in column)
        for column in endpoint_columns)
    assert all(not any(literal.row_keys[row][0] == "J" for row in column)
               for column in endpoint_columns)

    assert all(not any(
        literal.row_keys[row][0] == "C"
        and literal.row_keys[row][2][-1] < minimum_endpoint_seed
        for row in column)
        for column in full_endpoint_columns)
    assert all(not any(literal.row_keys[row][0] == "J" for row in column)
               for column in full_endpoint_columns)

    allowed_rows = frozenset(
        row for row, key in enumerate(literal.row_keys)
        if key[0] == "J"
        or (key[0] == "C" and key[2][-1] < minimum_endpoint_seed))
    functional, witness = separating_functional(
        tuple(columns), literal.targets, allowed_rows, literal.row_keys)
    if functional is not None:
        assert all(dot(functional, column) == 0
                   for column in endpoint_columns)

    after_corrections = defects(
        tuple(columns) + endpoint_columns, literal.targets)
    assert after_corrections == before
    after_full_correction_strips = defects(
        tuple(columns) + full_endpoint_columns, literal.targets)
    assert after_full_correction_strips == before
    origin_indices, origin_receipts = terminal_origin_columns(literal)
    origin_columns = tuple(literal.columns[index] for index in origin_indices)
    assert len(origin_columns) == 15
    augmented = tuple(columns) + full_endpoint_columns + origin_columns
    after_whole_endpoint_superspace = defects(augmented, literal.targets)
    assert after_whole_endpoint_superspace == before
    augmented_functional, augmented_witness = separating_functional(
        augmented, literal.targets, frozenset(range(len(literal.row_keys))),
        literal.row_keys)
    assert augmented_functional is not None
    assert all(dot(augmented_functional, column) == 0
               for column in augmented)

    running_echelon = M.ColumnEchelon()
    for index, column in enumerate(columns):
        running_echelon.add(column, index)
    block_receipts = []
    for block in sorted(blocks,
                        key=lambda item: (-item["minimum_seed"], item["label"])):
        old_rank = running_echelon.rank
        for index in block["indices"]:
            running_echelon.add(literal.columns[index], index)
        new_rank = running_echelon.rank
        block_receipts.append({
            "r_s_f": block["label"],
            "qmax": block["qmax"],
            "canonical_prefix_columns": block["prefix"],
            "minimum_seed": block["minimum_seed"],
            "rank_increment": new_rank - old_rank,
            "defects_after_block": defects_mod_echelon(
                running_echelon, literal.targets),
        })

    return {
        "parameters_n_w_g_m_D_s_t_J_L": CASE,
        "arbitrary_error_direction_offsets": OFFSETS,
        "base_plus_all_three_carrier_shift_columns": len(columns),
        "defects_before_endpoint_space": before,
        "complete_projection_endpoint_blocks": len(blocks),
        "complete_projection_endpoint_monomial_columns": len(endpoint_columns),
        "full_legal_correction_strip_monomial_columns":
            len(full_endpoint_columns),
        "minimum_endpoint_contact_seed": minimum_endpoint_seed,
        "defects_after_adjoining_all_correction_prefixes": after_corrections,
        "defects_after_adjoining_all_full_correction_strips":
            after_full_correction_strips,
        "terminal_origin_columns": len(origin_columns),
        "terminal_origin_block_receipts": origin_receipts,
        "defects_after_adjoining_origin_plus_correction_superspace":
            after_whole_endpoint_superspace,
        "low_seed_only_separator_audit": witness,
        "low_seed_only_separator_exists": functional is not None,
        "augmented_endpoint_separating_functional": augmented_witness,
        "augmented_columns_annihilated": len(augmented),
        "per_block_rank_receipts": tuple(block_receipts),
    }


def full187_literal_f3_endpoint_separator():
    """Extend the literal F3 separator to every 2d678e8 endpoint block."""
    p, n, g, m, jet, seed = (
        2_130_706_433, 262_144, 180_413, 60, 82, 2_703)
    instance = FT.build_target_instance()
    f3_scalar = instance.f3_selected_error_syndrome[0]
    assert f3_scalar == 1_307_960_934
    inverse = pow(f3_scalar, -1, p)
    assert inverse == 1_664_439_266
    assert f3_scalar * inverse % p == 1
    assert instance.hashes["F3_selected_error_syndrome_on_E_u32_le"] == (
        "44284a2ae31b90315699b3f0a14947ea2007114bbd7460485287f2543d5de332")

    _shapes, packets = PS.packet_shape_rows()
    assert all(z <= 1 for row in packets["F3"] for z in (row[-1],))
    correction_outer_seeds = tuple(
        seed - f - r - s
        for s in range(11) for r in range(22 - s) for f in range(m))
    assert len(correction_outer_seeds) == 11_220
    assert min(correction_outer_seeds) == 2_623
    terminal_origin_outer_seed = seed - jet
    assert terminal_origin_outer_seed == 2_621
    # Local substitution never lowers an already present outer Z exponent.
    assert min(terminal_origin_outer_seed, min(correction_outer_seeds)) > 0
    return {
        "literal_F3": "B*(Y-P-(Z-gamma)*q_H); frozen P=gamma=0",
        "pure_Z_replacement_rejected": True,
        "error_node": g,
        "normalized_scalar_coordinate_node_T_E_R_S_Z":
            (g, 0, 0, 0, 0, 0),
        "coordinate_weight": inverse,
        "boundary_covector": (0, 0, 0, 0),
        "F3_pairing": 1,
        "F3_unscaled_coordinate": f3_scalar,
        "F3_syndrome_sha256": instance.hashes[
            "F3_selected_error_syndrome_on_E_u32_le"],
        "complete_depth_correction_blocks": len(correction_outer_seeds),
        "complete_depth_minimum_outer_Z": min(correction_outer_seeds),
        "terminal_origin_minimum_outer_Z": terminal_origin_outer_seed,
        "annihilates_all_2d678e8_endpoint_contact_tails": True,
        "whole_source_dual": False,
    }


def support_of_v_power(power):
    return {(y, 0, 0) for y in range(power + 1)}


def support_of_j1_times_v(power):
    # J1 = Lambda R - Lambda'Y + (Lambda'Q-Lambda Q')Z.
    out = {(y, 1, 0) for y in range(power + 1)}
    out.update((y + 1, 0, 0) for y in range(power + 1))
    out.update((y, 0, 0) for y in range(power + 1))
    return out


def full187_support_gate():
    n, w, g, m, degree, jet, seed = (
        262_144, 131_071, 180_413, 60, 10_824_780, 82, 2_703)

    def qmax(r, s, f):
        width = degree - w * f - (w - 1) * r - (w - 2) * s
        return min(width // n - 1, m - f - 1)

    projection_blocks = {
        (f, r, s) for s in range(11) for r in range(22 - s)
        for f in range(m)
    }
    three_support = (
        {(y, 1, 0) for y in range(m - 1)}
        | {(y, 0, 0) for y in range(m + 1)})
    three_overlap = three_support & projection_blocks
    three_outside = three_support - projection_blocks
    assert three_outside == {(m, 0, 0)}

    pairs = ((0, 0), (0, 1), (1, 0), (1, 1),
             (2, 0), (2, 1), (3, 0), (4, 0))
    eight = {}
    for a, c in pairs:
        power = m - a - 2 * c
        support = (support_of_v_power(power) if c == 0
                   else support_of_j1_times_v(power))
        eight[(a, c)] = support
    eight_union = set().union(*eight.values())
    eight_outside = eight_union - projection_blocks
    assert eight_outside == {(m, 0, 0)}
    fully_inside = tuple(pair for pair, support in eight.items()
                         if support <= projection_blocks)
    assert fully_inside == tuple(pair for pair in pairs if pair != (0, 0))

    low_three_jet_slots = {
        (f, r, s, q) for f, r, s in three_overlap
        for q in range(min(2, qmax(r, s, f)) + 1)
    }
    qmax_histogram = Counter(qmax(r, s, f)
                             for f, r, s in three_overlap)

    # The endpoint layer is shift L-(J+1)=2620.  Every carrier raw monomial
    # has total grade J+1 before the shift and L after it.
    assert seed - (jet + 1) == 2_620
    assert all(f + r + s <= m <= jet
               for f, r, s in eight_union)
    return {
        "parameters_N_w_g_m_D_J_L":
            (n, w, g, m, degree, jet, seed),
        "terminal_shift": 2_620,
        "projection_physical_r_s_f_blocks": len(projection_blocks),
        "three_carrier_distinct_raw_f_r_s_blocks": len(three_support),
        "three_carrier_blocks_inside_projection": len(three_overlap),
        "three_carrier_blocks_outside_projection": tuple(sorted(three_outside)),
        "three_carrier_overlap_qmax_histogram":
            tuple(sorted(qmax_histogram.items())),
        "three_carrier_overlap_slots_through_q2": len(low_three_jet_slots),
        "eight_carrier_distinct_raw_f_r_s_blocks": len(eight_union),
        "eight_carrier_union_outside_projection":
            tuple(sorted(eight_outside)),
        "eight_carriers_whose_entire_raw_support_is_inside_projection":
            fully_inside,
        "interpretation": (
            "At the final shift the complete-depth projection and carrier "
            "tail reuse the same physical blocks.  This overlap is a coupled "
            "affine compatibility obligation, not an extra independent "
            "endpoint control space."
        ),
    }


def tight_first_fringe_lowz_shift_gate():
    """Test whether b535ccc's tight X-window unit is a packet precycle."""
    w, degree, jet, seed = 131_071, 10_824_780, 82, 2_703
    r, s = 11, 10
    f58, f59 = 58, 59
    z58 = seed - f58 - r - s
    z59 = seed - f59 - r - s
    width58 = degree - w * f58 - (w - 1) * r - (w - 2) * s
    width59 = degree - w * f59 - (w - 1) * r - (w - 2) * s
    assert (z58, z59) == (2_624, 2_623)
    assert (width58, width59) == (470_202, 339_131)

    # Maximal legal downward shift puts P59 at Z^0 and P58 at Z^1.
    downshift = z59
    shifted_z58, shifted_z59 = z58 - downshift, z59 - downshift
    assert (shifted_z58, shifted_z59) == (1, 0)
    assert r + s <= 21 and s <= 10
    assert f58 + r + s <= jet and f59 + r + s <= jet
    assert f58 + r + s + shifted_z58 == 80
    assert f59 + r + s + shifted_z59 == 80

    # The shared f=58 output is at passive seed one: P58 retains its outer
    # Z, while P59 selects one u1*Z and 58 contactY factors.  In either case
    # the immutable outer R^11*S^10 gives derivative degree at least 21.
    shared_output_seed = shifted_z58
    assert shifted_z59 + 1 == shared_output_seed == 1
    packet_rows = set().union(*PS.packet_shape_rows()[1].values())
    assert all(row[2] + row[3] <= 1 for row in packet_rows)
    confluence_envelope_intersection = tuple(
        row for row in packet_rows if row[2] >= r and row[3] >= s)
    assert not confluence_envelope_intersection

    # At P=gamma=0 every first boundary partial of either shifted source is
    # zero: both raw monomials have total non-X degree 80.  In particular the
    # pair also misses the normalized F3 scalar coordinate at R=S=Z=0.
    assert min(f58 + r + s + shifted_z58,
               f59 + r + s + shifted_z59) > 1
    return {
        "upstream_certificate_commit": "b535ccc",
        "upstream_certificate_canonical_sha256":
            "a285518b5274462dcaa1a4fc77af24be7a04f7896be87b84ea92a35243fe6df9",
        "tight_pair_r_s_f": ((r, s, f58), (r, s, f59)),
        "endpoint_outer_Z_P58_P59": (z58, z59),
        "coefficient_windows_P58_P59": (width58, width59),
        "literal_source_caps_active_slope_curvature_total":
            ((79, 21, 10, 80), (80, 21, 10, 80)),
        "certified_high_quotient_rank": 54_086,
        "maximal_legal_downshift": downshift,
        "downshifted_outer_Z_P58_P59": (shifted_z58, shifted_z59),
        "downshifted_source_total_grades": (80, 80),
        "shared_confluence_output_seed": shared_output_seed,
        "minimum_output_R_plus_S": r + s,
        "packet_maximum_R_plus_S": 1,
        "raw_packet_row_intersection": len(confluence_envelope_intersection),
        "first_boundary_map_at_frozen_zero_graph": "zero",
        "pairs_literal_F3_scalar_coordinate": 0,
        "decision": "GREEN_ENDPOINT_X_CONFLUENCE__RED_AS_PACKET_PRELIFT",
        "interpretation": (
            "The 54086-rank minor is an X-coefficient unit inside one "
            "fixed passive/derivative block.  Even after the largest legal "
            "downshift, it acts at Z=1 with R+S>=21 and has zero first "
            "boundary map, so it cannot initiate any literal F0..F3 lift."
        ),
    }


def main():
    stable = {
        "scope": (
            "Exact F101 covector against the whole three-carrier trellis "
            "plus the complete-depth endpoint superspace; literal Full187 "
            "F3 separator, final carrier overlap, and tight first-fringe "
            "maximal-downshift packet-prelift test"
        ),
        "f101_endpoint_gate": f101_endpoint_gate(),
        "literal_F3_vs_complete_depth_endpoint":
            full187_literal_f3_endpoint_separator(),
        "full187_support_gate": full187_support_gate(),
        "tight_first_fringe_lowz_shift_gate":
            tight_first_fringe_lowz_shift_gate(),
        "decision": "STOP_ENDPOINT_PROJECTION_DOES_NOT_REPAIR_LOW_SEED_TRELLIS",
        "remaining_gate": (
            "Use an arbitrary-direction complete-state carrier (at least the "
            "order-four module) for the low-seed recurrence, and solve its "
            "last-layer coefficients jointly with—not in addition to—the "
            "complete-depth Pascal/Hermite prescriptions on the shared raw "
            "blocks.  Commit b535ccc makes the tightest first X-fringe "
            "compatible, but supplies no low-passive packet prelift."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
