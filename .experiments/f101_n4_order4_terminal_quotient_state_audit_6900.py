#!/usr/bin/env python3
"""Exact quotient-state audit for the eight order-four terminal carriers.

The tiny one-error controls keep (n,w,g,e)=(4,1,3,1) fixed and vary the
contact multiplicity.  At each m we compare:

* all source columns through grade J=m+2;
* the complete next raw source shell at grade J+1;
* the eight Lambda/V/J1 order-four carriers, with coefficient degree <3e;
* every available Z-shift of those carriers through L=m+6.

The selected 24-by-24 local block is checked independently by the companion
literal expansion.  The purpose is to detect a hidden quotient state in the
nonselected local rows, not to extrapolate a target theorem from a count.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, ".experiments")
import f101_o2_bordered_filtration_mechanism_6900 as M  # noqa: E402
import f101_order4_eight_carrier_local_jet_block_6900 as LB  # noqa: E402
import f101_order4_osculating_covariant_basis_gate_6900 as G  # noqa: E402
import f101_terminal_seed_trellis_three_carrier_6900 as TT  # noqa: E402
import o2_m60_five_pivot_locator_rhs_falsifier_6900 as F  # noqa: E402


P = 101
MULTIPLICITIES = (4, 5, 6, 8)


def rank(columns):
    return M.modular_rank_sparse(columns)


def shifted_z(source, amount):
    return {
        (x, y, r, s, z + amount): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def shifted_x(source, amount):
    return {
        (x + amount, y, r, s, z): coefficient
        for (x, y, r, s, z), coefficient in source.items()
    }


def add_v_prefactor(literal, source, exponent):
    q = F.sparse_embed_x(literal.q)
    v = F.sparse_add(F.Y, F.sparse_mul(F.Z, q), -1)
    return F.sparse_mul(source, F.sparse_pow(v, exponent))


def eight_carrier_sources(literal, m):
    families = G.weighted_order_four_families(literal)
    selected = []
    for label, exponents, _active, _seed, source in families:
        a_lambda, _a_v, a_j1, a_j2 = exponents
        if a_j2 != 0 or a_j1 > 1:
            continue
        source = add_v_prefactor(literal, source, m - 4)
        selected.append((label, a_lambda, a_j1, source))
    assert len(selected) == 8
    return tuple(selected)


def one_multiplicity(m):
    case = (4, 1, 3, m, 3 * m, 1, 1, m + 2, m + 6)
    literal = M.build_case(
        f"n4_m{m}", case, actual_agreement_count=3, anchor_count=3,
        normal_coordinates=3, error_direction_offsets=(3,))
    source_index = {monomial: index
                    for index, monomial in enumerate(literal.monomials)}
    J, L = case[7], case[8]
    base_indices = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) <= J)
    terminal_indices = tuple(
        index for index, monomial in enumerate(literal.monomials)
        if sum(monomial[1:]) == J + 1)
    base = [literal.columns[index] for index in base_indices]
    terminal = [literal.columns[index] for index in terminal_indices]
    base_rank = rank(base)
    full_terminal_rank = rank(base + terminal)
    base_target_rank = rank(base + list(literal.targets))

    families = eight_carrier_sources(literal, m)
    cycle_sources = []
    cycle_tags = []
    for label, a_lambda, a_j1, source in families:
        for degree in range(3):
            multiple = shifted_x(source, degree)
            if not all(monomial in source_index for monomial in multiple):
                continue
            image = TT.indexed_image(literal, multiple, source_index)
            assert not any(
                literal.row_keys[row][0] == "C"
                and literal.row_keys[row][1] in literal.actual_agreement
                for row in image)
            cycle_sources.append(multiple)
            cycle_tags.append((label, a_lambda, a_j1, degree))

    cycles = [TT.indexed_image(literal, source, source_index)
              for source in cycle_sources]
    cycle_rank = rank(base + cycles)
    individual = tuple(
        rank(base + cycles + [target]) - cycle_rank
        for target in literal.targets)
    joint = rank(base + cycles + list(literal.targets)) - cycle_rank

    shifted_rows = []
    accumulated = list(base)
    previous = base_rank
    for shift in range(L - J):
        layer_sources = [shifted_z(source, shift) for source in cycle_sources]
        assert all(all(monomial in source_index for monomial in source)
                   for source in layer_sources)
        layer = [TT.indexed_image(literal, source, source_index)
                 for source in layer_sources]
        accumulated.extend(layer)
        current = rank(accumulated)
        shifted_rows.append({
            "shift": shift,
            "source_grade": J + 1 + shift,
            "rank_increment": current - previous,
        })
        previous = current

    old_case = LB.CASE
    try:
        LB.CASE = case
        local = LB.one_node(literal, 3, 3, 1)
    finally:
        LB.CASE = old_case
    assert local["matrix_shape_rank"] == (24, 24, 24)

    return {
        "parameters_n_w_g_m_D_s_t_J_L": case,
        "base_columns_rank": (len(base), base_rank),
        "base_joint_target_quotient_rank": base_target_rank - base_rank,
        "complete_terminal_shell_columns_rank_gain":
            (len(terminal), full_terminal_rank - base_rank),
        "legal_eight_carrier_coefficient_columns": len(cycles),
        "legal_carrier_tags_family_a_c_degree": tuple(cycle_tags),
        "eight_carrier_rank_gain": cycle_rank - base_rank,
        "eight_carrier_individual_target_defects": individual,
        "eight_carrier_joint_target_defect": joint,
        "selected_local_three_jet_block_rank": local["matrix_shape_rank"],
        "all_shift_rank_increments": tuple(shifted_rows),
    }


def main():
    M.T.PRIME = M.F.PRIME = G.T.PRIME = G.F.PRIME = F.PRIME = P
    payload = {
        "scope": (
            "one-error multiplicity sweep for terminal quotient state and "
            "all order-four seed shifts; finite exact evidence only"
        ),
        "field": P,
        "multiplicities": tuple(one_multiplicity(m)
                                for m in MULTIPLICITIES),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["canonical_sha256"] = hashlib.sha256(canonical.encode()).hexdigest()
    payload["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
