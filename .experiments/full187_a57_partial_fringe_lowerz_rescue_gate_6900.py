#!/usr/bin/env python3
"""Exact A57 partial-fringe / lower-Z rescue gate for Full187.

The fixed-z Pascal staircase first loses one scalar direction at A=57:
the q=12 coordinate of (y,r,s)=(36,11,10).  Its coefficient window still
contains a 208036-dimensional partial q=12 channel.  This experiment couples
that channel to *all* z=2624,A=58,h=1 predecessors after preserving the
already selected A=58 prefixes.

Only two of the 87 predecessors reach their first unprescribed coefficient
jet.  The tempting (38,10,10,q11) channel maps to an already legal A57 raw
column and is identically zero in the missing quotient.  The actual rescue is
(37,11,10,q12), whose h=1 output is 37*u1 times the omitted column.  Its
76965-dimensional fringe and the own 208036-dimensional fringe give the
polynomial-ring equation A+37*u1*B mod (X^N-1).  An exact 54108-square
Hankel minor is certified nonsingular by FLINT Berlekamp--Massey.

The A=58 diagonal disturbance is explicitly expressed in the proven selected
Pascal basis.  Every compensator has a different physical shape from the sole
quotient-visible predecessor, so all of its possible canonical higher jets
pair to zero with the A57 missing dual.  Thus the quotient equation is
section-independent: the induced correction K is exactly zero.
"""

from __future__ import annotations

from collections import Counter
from math import comb
import hashlib
import json
from pathlib import Path
import resource

import full187_actual_pascal_residual_and_first_fringe_gate_6900 as FG
import full187_parametric_pascal_straightening_window_gate_6900 as S
import full187_target_charge13_transposed_four_residue_gate_6900 as T


P = S.P
N = S.N
M = S.M
OUTER_Z = S.OUTER_Z

AUTHORITIES = {
    "full187_parametric_pascal_straightening_window_gate_6900.py":
        "f9c504d835c2a47009da6b27eef7b9d1f43535f11501ed960e2c94d9ae50a951",
    "full187_actual_pascal_residual_and_first_fringe_gate_6900.py":
        "4f71084905369899563eb496f2b9b044245107bd7a3357aac35336709b02da15",
    "full187_target_charge13_transposed_four_residue_gate_6900.py":
        "ebd359bd06642255c8fa34a56a5b9b295a2689bc5aea1b85b63cb49cd323b654",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_repr(value) -> str:
    return hashlib.sha256(repr(value).encode()).hexdigest()


def solve_independent_columns(rows, columns, target):
    """Solve sum x_j columns[j]=target for independent spanning columns."""
    column_count = len(columns)
    augmented = [
        [column.get(row, 0) % P for column in columns]
        + [target.get(row, 0) % P]
        for row in rows
    ]
    pivot_rows = []
    pivot_row = 0
    for column_index in range(column_count):
        pivot = next((row for row in range(pivot_row, len(augmented))
                      if augmented[row][column_index]), None)
        assert pivot is not None, "selected columns were not independent"
        augmented[pivot_row], augmented[pivot] = (
            augmented[pivot], augmented[pivot_row])
        inverse = pow(augmented[pivot_row][column_index], -1, P)
        augmented[pivot_row] = [
            value * inverse % P for value in augmented[pivot_row]
        ]
        for row in range(len(augmented)):
            if row == pivot_row or not augmented[row][column_index]:
                continue
            factor = augmented[row][column_index]
            augmented[row] = [
                (left - factor * right) % P
                for left, right in zip(augmented[row],
                                       augmented[pivot_row])
            ]
        pivot_rows.append(pivot_row)
        pivot_row += 1

    # Consistency in every nonpivot equation.
    assert all(not any(row[:column_count]) and not row[column_count]
               for row in augmented[pivot_row:])
    solution = tuple(augmented[row][column_count] % P
                     for row in pivot_rows)
    assert all(
        sum(value * column.get(row, 0)
            for value, column in zip(solution, columns)) % P
        == target.get(row, 0) % P
        for row in rows
    )
    return solution


def a57_missing_dual_data():
    """Reconstruct the committed normalized dual, retaining literal data."""
    active = 57
    n = 38
    raw = []
    legal = []
    for y, r, s, z in S.B.physical_shapes(active):
        for q in range(M - y):
            if y + q - s != n:
                continue
            key = (y, r, s, q, z)
            item = (key, S.B.raw_contact_column(active, key))
            raw.append(item)
            if q < S.legal_depth(active, y, r, s):
                legal.append(item)
    rows = tuple(sorted(
        set().union(*(set(column) for _key, column in raw)),
        key=lambda row: (row[1] + row[3], row[0] + 3 * row[1], row),
    ))
    equations = [
        [column.get(row, 0) for row in rows] for _key, column in legal
    ]
    nullspace = S.nullspace_basis(equations)
    omitted = tuple(item for item in raw if item not in legal)
    assert len(omitted) == 1
    omitted_key, omitted_column = omitted[0]
    assert omitted_key == (36, 11, 10, 12, OUTER_Z)
    dual = next(vector for vector in nullspace
                if sum(value * omitted_column.get(row, 0)
                       for row, value in zip(rows, vector)) % P)
    evaluation = sum(value * omitted_column.get(row, 0)
                     for row, value in zip(rows, dual)) % P
    dual = tuple(value * pow(evaluation, -1, P) % P for value in dual)
    assert all(sum(value * column.get(row, 0)
                   for row, value in zip(rows, dual)) % P == 0
               for _key, column in legal)
    assert sum(value * omitted_column.get(row, 0)
               for row, value in zip(rows, dual)) % P == 1
    return rows, tuple(raw), tuple(legal), omitted_key, omitted_column, dual


def dual_evaluation(rows, dual, column):
    return sum(value * column.get(row, 0)
               for row, value in zip(rows, dual)) % P


def predecessor_and_dual_gate():
    """Enumerate every nearest h=1 predecessor and its exact dual action."""
    rows, raw57, legal57, omitted_key, omitted_column, dual = (
        a57_missing_dual_data())
    selected58, depths58, raw_rank58 = S.minimal_prefix_basis(
        58, enforce_capacity=True)
    depth = dict(depths58)
    target_row = (59, 0, 36, 21, OUTER_Z)

    predecessors = []
    quotient_visible = []
    first_unprescribed = []
    q_minus_depth_histogram = Counter()
    for s in range(S.CURVATURE + 1):
        for r in range(S.SLOPE - s + 1):
            c_s = target_row[3] - s
            residual_r = target_row[2] - r
            f = residual_r + c_s
            q = target_row[0] - f - c_s
            if min(c_s, residual_r, f, q) < 0:
                continue
            y = f + 1
            if y >= M:
                continue
            source_z = OUTER_Z - 1
            assert S.C.row_of(r, s, source_z, f, 1, 0, c_s, q) == target_row
            selected_depth = depth[(y, r, s)]
            width = S.F.H.width(y, r, s)
            preserved_residual = width - selected_depth * N
            shifted_key = (y - 1, r, s, q, OUTER_Z)
            shifted_column = S.B.raw_contact_column(57, shifted_key)
            scalar = y % P
            h1_column = {
                row: scalar * value % P
                for row, value in shifted_column.items()
            }
            evaluation = dual_evaluation(rows, dual, h1_column)
            record = (
                y, r, s, q, selected_depth, width, preserved_residual,
                shifted_key, scalar, evaluation,
            )
            predecessors.append(record)
            q_minus_depth_histogram[q - selected_depth] += 1
            if q >= selected_depth:
                first_unprescribed.append(record)
            if evaluation:
                quotient_visible.append(record)

    assert len(predecessors) == 87
    assert {record[7] for record in predecessors} == {
        key for key, _column in raw57
    }
    assert q_minus_depth_histogram == Counter({
        -8: 2, -7: 11, -6: 15, -5: 15, -4: 14,
        -3: 13, -2: 9, -1: 6, 0: 2,
    })
    assert tuple(record[:7] for record in first_unprescribed) == (
        (38, 10, 10, 11, 11, 3_222_692, 339_108),
        (37, 11, 10, 12, 12, 3_222_693, 76_965),
    )
    # The first tempting >N residual is a legal A57 raw direction and dies.
    assert first_unprescribed[0][7] == (37, 10, 10, 11, OUTER_Z)
    assert first_unprescribed[0][-1] == 0
    # Only the second physical shape is visible in the one-dimensional
    # quotient, with h=1 scalar binom(37,36)=37.
    assert len(quotient_visible) == 1
    assert quotient_visible[0][7] == omitted_key
    assert quotient_visible[0][-2:] == (37, 37)

    predecessor_hash = sha256_repr(tuple(predecessors))
    assert predecessor_hash == (
        "7ae845e9ac23b5723188aaf06baaf6bc97459f623ef756e5615bd082dbb35669")
    return {
        "a57_n38_raw_legal_rank_defect": (
            len(raw57), len(legal57), S.F.modular_rank([
                [column.get(row, 0) for _key, column in raw57]
                for row in rows
            ]), S.F.modular_rank([
                [column.get(row, 0) for _key, column in legal57]
                for row in rows
            ])),
        "normalized_omitted_key_and_dual_evaluation": (omitted_key, 1),
        "a58_selected_count_rawrank": (len(selected58), raw_rank58),
        "nearest_h1_predecessor_count": len(predecessors),
        "q_minus_selected_depth_histogram": tuple(sorted(
            q_minus_depth_histogram.items())),
        "all_predecessor_records_sha256": predecessor_hash,
        "first_unprescribed_y_r_s_q_depth_width_residual_shifted_"
        "scalar_dual": tuple(first_unprescribed),
        "quotient_visible_predecessors": tuple(quotient_visible),
        "q11_large_residual_is_legal_direction_and_pairs_zero": True,
        "unique_rescue_predecessor": (37, 11, 10, 12, OUTER_Z - 1),
    }, (rows, dual, selected58, depth, omitted_key)


def diagonal_compensation_gate(context):
    """Cancel each unprescribed A58 diagonal and audit all induced tails."""
    rows57, dual57, selected58, depth58, omitted_key = context
    selected_items = []
    for y, r, s, q, z, n, _h, _j in selected58:
        selected_items.append(((y, r, s, q, z), n,
                               S.B.raw_contact_column(58, (y, r, s, q, z))))

    receipts = []
    for target_key in (
            (38, 10, 10, 11, OUTER_Z),
            (37, 11, 10, 12, OUTER_Z)):
        target_n = target_key[0] + target_key[3] - target_key[2]
        basis = tuple(item for item in selected_items if item[1] == target_n)
        basis_keys = tuple(item[0] for item in basis)
        basis_columns = tuple(item[2] for item in basis)
        target_column = S.B.raw_contact_column(58, target_key)
        rows58 = tuple(sorted(set(target_column).union(*(
            set(column) for column in basis_columns))))
        solution = solve_independent_columns(
            rows58, basis_columns, target_column)
        support = tuple((key, coefficient)
                        for key, coefficient in zip(basis_keys, solution)
                        if coefficient)
        assert support

        # A canonical interpolation section for a compensator may induce any
        # higher Hasse jet on that *same physical polynomial*.  For the A57
        # quotient, only one q per shape can land in n=38.  Audit that raw
        # direction for every compensator shape, without assuming it is zero.
        physical_shapes = tuple(sorted(set(key[:3] for key, _c in support)))
        induced = []
        for y, r, s in physical_shapes:
            q_target = 39 - y + s
            if not 0 <= q_target < M - y:
                induced.append(((y, r, s), q_target, None, 0))
                continue
            shifted_key = (y - 1, r, s, q_target, OUTER_Z)
            if y == 0 or y - 1 + r + s != 57:
                induced.append(((y, r, s), q_target, None, 0))
                continue
            shifted_column = S.B.raw_contact_column(57, shifted_key)
            evaluation = y * dual_evaluation(
                rows57, dual57, shifted_column) % P
            induced.append(((y, r, s), q_target, shifted_key, evaluation))

        # The sole quotient-visible shape is the target rescue polynomial
        # itself.  It cannot occur in its selected-basis representation:
        # its only n=39 coordinate is precisely the unselected target q.
        assert (37, 11, 10) not in physical_shapes
        assert all(record[-1] == 0 for record in induced)
        target_shifted = (
            target_key[0] - 1, target_key[1], target_key[2],
            target_key[3], OUTER_Z)
        direct_evaluation = target_key[0] * dual_evaluation(
            rows57, dual57,
            S.B.raw_contact_column(57, target_shifted)) % P
        receipts.append({
            "target_key_n": (target_key, target_n),
            "selected_basis_size": len(basis),
            "representation_support_count": len(support),
            "representation_support": support,
            "representation_support_sha256": sha256_repr(support),
            "exact_diagonal_reconstruction": True,
            "compensator_physical_shapes": physical_shapes,
            "all_possible_n38_higher_jet_dual_evaluations": tuple(induced),
            "all_compensator_canonical_higher_jets_pair_zero": True,
            "direct_h1_dual_evaluation": direct_evaluation,
        })

    assert receipts[0]["direct_h1_dual_evaluation"] == 0
    assert receipts[1]["direct_h1_dual_evaluation"] == 37
    assert tuple(record["representation_support_sha256"]
                 for record in receipts) == (
        "3b8019be0387456818512f5aebe3ee25fc1631e6888e9adb94c60e3cb04be1a6",
        "2f96c1933d6f455e14e92f1c2b1729925141be28eacb9a36c1e513ede9573f7c",
    )
    assert all(record["selected_basis_size"] == 85 for record in receipts)
    assert all(record["representation_support_count"] == 22
               for record in receipts)
    return {
        "unprescribed_diagonal_compensation_receipts": tuple(receipts),
        "section_independence": (
            "Every A58 right-inverse compensator has physical shape other "
            "than (37,11,10). For each such shape, the unique possible h=1 "
            "jet landing in n=38 is an A57 legal raw column and is killed "
            "by the normalized dual. This audits arbitrary induced higher "
            "jets, hence in particular the canonical section."),
        "induced_missing_quotient_correction_K": 0,
    }


def partial_fringe_hankel_gate():
    """Certify A+37*u1*B is onto Fp[X]/(X^N-1)."""
    own_width = S.F.H.width(36, 11, 10)
    predecessor_width = S.F.H.width(37, 11, 10)
    depth = 12
    a_dimension = own_width - depth * N
    b_dimension = predecessor_width - depth * N
    quotient_rows = N - a_dimension
    nominal_surplus = a_dimension + b_dimension - N
    assert (own_width, predecessor_width) == (3_353_764, 3_222_693)
    assert (a_dimension, b_dimension, quotient_rows, nominal_surplus) == (
        208_036, 76_965, 54_108, 22_857)

    instance = T.build_target_instance()
    u1_coefficients = instance.u1_values.copy()
    T.ntt(u1_coefficients, inverse=True)

    # A controls coefficient positions 0..a-1.  On positions a..N-1,
    # multiplication by u1 sends B_j to U1[a+i-j].  Select the final m B
    # monomials and reverse them to obtain Hankel entry sequence[i+j].
    first_selected_b = b_dimension - quotient_rows
    sequence_start = a_dimension - b_dimension + 1
    assert (first_selected_b, sequence_start) == (22_857, 131_072)
    sequence = tuple(u1_coefficients[
        sequence_start:sequence_start + 2 * quotient_rows])
    assert len(sequence) == 2 * quotient_rows
    connection, remainder, reduce_calls = FG.exact_bm(sequence)
    complexity = len(connection) - 1
    remainder_degree = len(remainder) - 1
    assert complexity == quotient_rows
    assert remainder_degree == quotient_rows - 1
    assert connection[0] and connection[-1]
    assert FG.sha256_u64(sequence) == (
        "8d9fea21871d9104845b19c040903cfedcaaefd1937d58c505cd687431e68962")
    assert (connection[0], connection[-1]) == (420_266_329, 1_127_397_145)
    assert FG.sha256_u64(connection) == (
        "2024f5e94ccfaa4f1b8c458511c96fef557e5022f53f1571d315a58a2895db02")
    assert FG.sha256_u64(remainder) == (
        "ae7fd640e023b221db1a7f23b0bc9bb8bc6221b03062402487be5989d6d428a9")

    return {
        "ring": "R=Fp[X]/(Omega), Omega=X^262144-1",
        "variation_equation_after_common_H12_diagonal": (
            "A + 37*u1*B; H12(Omega^12 V)(alpha)="
            "(N*alpha^-1)^12 V(alpha)"),
        "own_and_predecessor_windows": (own_width, predecessor_width),
        "fringe_dimensions_A_B": (a_dimension, b_dimension),
        "node_dimension_and_nominal_surplus": (N, nominal_surplus),
        "high_quotient_toeplitz_shape": (quotient_rows, b_dimension),
        "selected_B_columns": (first_selected_b, b_dimension - 1),
        "hankel_sequence_start_length": (sequence_start, len(sequence)),
        "hankel_sequence_sha256_u64": FG.sha256_u64(sequence),
        "hankel_minor_size": quotient_rows,
        "berlekamp_massey_complexity": complexity,
        "berlekamp_massey_remainder_degree": remainder_degree,
        "berlekamp_massey_reduce_calls": reduce_calls,
        "connection_first_last": (connection[0], connection[-1]),
        "connection_sha256_u64": FG.sha256_u64(connection),
        "remainder_sha256_u64": FG.sha256_u64(remainder),
        "scalar_37_inverse_mod_p": pow(37, -1, P),
        "exact_rank": N,
        "decision": "GREEN_A57_MISSING_NODE_CHANNEL_FULL_ROW_RANK",
    }


def strict_exit_scope_gate(compensation):
    """Name, but do not solve, the first strict-lex outgoing block."""
    selected58, depths58, _rank58 = S.minimal_prefix_basis(
        58, enforce_capacity=True)
    del selected58
    depth = dict(depths58)
    compensator_shapes = set()
    for receipt in compensation[
            "unprescribed_diagonal_compensation_receipts"]:
        compensator_shapes.update(receipt["compensator_physical_shapes"])

    # A fixed Hermite section for a depth-d prefix can first induce H_d.
    # Full contact keeps (z,A)=(2624,58), so its least row-contact weight is
    # y+d.  These are earlier than any larger-Z/nonfull-contact exit.
    possible_full_contact_heads = tuple(sorted(
        (y + depth[(y, r, s)], y, r, s, depth[(y, r, s)],
         S.F.H.width(y, r, s) - depth[(y, r, s)] * N)
        for y, r, s in compensator_shapes
        if S.F.H.width(y, r, s) - depth[(y, r, s)] * N > 0
    ))
    first_weight = possible_full_contact_heads[0][0]
    first_origins = tuple(record for record in possible_full_contact_heads
                          if record[0] == first_weight)
    assert first_weight == 49
    assert first_origins == (
        (49, 37, 12, 9, 12, 76_964),
        (49, 38, 11, 9, 11, 339_107),
    )

    # The rescue B itself first has an uncancelled full-contact H13 head.
    assert 37 + 13 == 50
    # Own A and rescue B at q=12 close the A57 diagonal; their q>12 heads
    # raise contact weight.  For f<y, rem=0 forces h=y-f and raises both
    # passive Z and J-active; every other term has positive u0 and belongs to
    # the later error-facing branch.  This is precisely the orientation used
    # in the committed Pascal induction statement.
    return {
        "closed_local_block": (
            "all A57 fixed-z scalar rows modulo the A57 legal-prefix image, "
            "including its unique n38 defect at every one of N nodes"),
        "first_unproved_outgoing_lex_key": (
            OUTER_Z - 1, S.F.J - 58, first_weight),
        "first_unproved_full_contact_origins_"
        "weight_y_r_s_q_fringe": first_origins,
        "rescue_B_next_full_contact_head": (
            OUTER_Z - 1, S.F.J - 58, 50, 37, 11, 10, 13),
        "tail_partition": (
            "full-contact induced q>=depth stays at (z,A) and strictly "
            "raises contact weight; u0-free f<y has h=y-f and strictly "
            "raises (outerZ,J-active); the remaining f<y terms have "
            "positive u0 and enter the later error-facing branch"),
        "decision_scope": "LOCAL_BLOCK_GREEN_ONLY",
        "first_outgoing_block_is_not_solved_here": True,
    }


def main():
    here = Path(__file__).resolve().parent
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(here / filename) == expected
    predecessors, context = predecessor_and_dual_gate()
    compensation = diagonal_compensation_gate(context)
    hankel = partial_fringe_hankel_gate()
    exits = strict_exit_scope_gate(compensation)
    stable = {
        "scope": (
            "A57 n=38 one-dimensional Pascal quotient, own q12 partial "
            "fringe, and the complete nearest z2624/A58/h1 predecessor "
            "family after preserving A58 prefixes; no later outgoing "
            "filtration blocks and no production changes"),
        "target_p_N_M_outerZ": (P, N, M, OUTER_Z),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "complete_predecessor_and_dual_gate": predecessors,
        "a58_diagonal_compensation_and_section_gate": compensation,
        "exact_polynomial_ring_hankel_gate": hankel,
        "strict_exit_scope": exits,
        "decision": (
            "LOCAL_BLOCK_GREEN__A57_PARTIAL_FRINGE_PLUS_UNIQUE_LOWERZ_"
            "PREDECESSOR__GREEN_EXACT_54108_HANKEL_MINOR__"
            "NEXT_STRICT_LEX_EXITS_UNPROVED"),
        "scope_guard": (
            "This closes exactly the first A57 raw/window defect. It does "
            "not claim that all induced strict-lex outgoing blocks close; "
            "those remain the next induction gate. The >N q11 residual is "
            "explicitly rejected as a rescue because its scalar direction "
            "is already in the A57 legal image."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    peak_rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert peak_rss_kib < 3 * 1024 * 1024
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": file_sha256(Path(__file__)),
        "peak_rss_kib": peak_rss_kib,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
