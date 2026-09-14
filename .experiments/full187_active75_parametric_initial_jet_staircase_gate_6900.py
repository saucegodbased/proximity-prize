#!/usr/bin/env python3
"""Exact active-75 discriminator for the parametric Full187 jet staircase.

The active-77 and active-76 receipts found two consecutive legal initial-jet
blocks, but their bases were written as hand-picked coordinate lists.  This
script extracts the common closed rule B_A, checks that it reproduces both
old bases, and subjects active 75 to the complete provenance/rank/SCC gate.

Only the (outer Z)=2625 diagonal is expanded.  Peak memory stays tiny: no
177-million-occurrence tail and no dense all-active scan is constructed.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import resource
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import full187_cross_slope_second_fringe_confluence_6900 as C
import full187_earliest_positive_u0_curvature_frontier_gate_6900 as F
import full187_next_positive_u0_initial_jet_recurrence_gate_6900 as R


P = F.P
N = F.N
M = F.M
J = F.J
OUTER_Z = F.OUTER_Z
ACTIVE = 75
INV2 = F.INV2

AUTHORITIES = {
    "full187_cross_slope_second_fringe_confluence_6900.py":
        "2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29",
    "full187_earliest_positive_u0_curvature_frontier_gate_6900.py":
        "cd763ffc825c0a9e1d73f055d1278b583fdcdac162a5ed597e289e24d4db53b0",
    "full187_next_positive_u0_initial_jet_recurrence_gate_6900.py":
        "08cedb9b214d3bb5cf4b055178582732ebc21a26dbeb5e607b0b72fc32139804",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def raw_contact_column(active, key):
    """Full live support of H_q(P) contactY^y R^r S^s Z^z."""
    y, r, s, q, z = key
    assert y + r + s == active and z == OUTER_Z
    out = {}
    for a_e in range(y + 1):
        for c_s in range(y - a_e + 1):
            residual_r = y - a_e - c_s
            row = (
                q + residual_r + 2 * c_s,
                a_e,
                r + residual_r,
                s + c_s,
                z,
            )
            if row[0] + 3 * row[1] >= M:
                continue
            scalar = (
                factorial(y)
                // (factorial(a_e) * factorial(c_s)
                    * factorial(residual_r))
            ) % P
            scalar = scalar * pow(-INV2 % P, c_s, P) % P
            assert scalar and row not in out
            out[row] = scalar
    assert out
    return out


def physical_shapes(active):
    return tuple(
        (y, active - y - s, s, OUTER_Z)
        for y in range(max(0, active - F.H.SLOPE), min(active, M - 1) + 1)
        for s in range(min(F.H.CURVATURE, active - y) + 1)
    )


def staircase_qmax(y, s):
    """Closed Ferrers boundary of B_A; selected jets are q=0..qmax."""
    d = M - y
    return max(0, (d - 1) // 3, (d + s - (F.H.CURVATURE + 1)) // 2)


def staircase_selected(active, key):
    y, r, s, q, z = key
    assert (y, r, s, z) in physical_shapes(active)
    return q <= staircase_qmax(y, s)


def coordinate_census(active):
    coordinates = []
    for y, r, s, z in physical_shapes(active):
        for q in range(M - y):
            key = (y, r, s, q, z)
            coordinates.append((key, raw_contact_column(active, key)))
    rows = tuple(sorted(
        set().union(*(set(column) for _key, column in coordinates)),
        key=lambda row: (row[0] + 3 * row[1], row),
    ))
    matrix = [[column.get(row, 0) for _key, column in coordinates]
              for row in rows]
    rank = F.modular_rank(matrix)
    return tuple(coordinates), rows, rank


def selected_staircase(active, coordinates):
    selected = tuple(
        (key, column) for key, column in coordinates
        if staircase_selected(active, key)
    )
    qsets = defaultdict(set)
    for y, r, s, q, z in (key for key, _column in selected):
        qsets[(y, r, s, z)].add(q)
    assert set(qsets) == set(physical_shapes(active))
    assert all(qset == set(range(max(qset) + 1))
               for qset in qsets.values())
    return selected, qsets


def known_block_reproduction():
    expected = {
        77: (110, 73, 56, 56,
             Counter({(0,): 32, (0, 1): 12})),
        76: (165, 112, 79, 79,
             Counter({(0,): 32, (0, 1): 22, (0, 1, 2): 1})),
        75: (231, 154, 103, 103,
             Counter({(0,): 32, (0, 1): 31, (0, 1, 2): 3})),
    }
    receipts = []
    active75_payload = None
    for active in (77, 76, 75):
        coordinates, rows, raw_rank = coordinate_census(active)
        selected, qsets = selected_staircase(active, coordinates)
        selected_rank = F.modular_rank([
            [column.get(row, 0) for _key, column in selected]
            for row in rows
        ])
        histogram = Counter(tuple(sorted(qset)) for qset in qsets.values())
        actual = (len(coordinates), len(rows), raw_rank, selected_rank,
                  histogram)
        assert actual == expected[active]
        receipts.append((active, len(coordinates), len(rows), raw_rank,
                         len(selected), selected_rank,
                         tuple(sorted(histogram.items()))))
        if active == ACTIVE:
            active75_payload = (coordinates, rows, selected, qsets)
    assert active75_payload is not None
    return active75_payload, {
        "active_coordinate_row_rawrank_selected_selectedrank_qsets":
            tuple(receipts),
        "same_closed_formula_reproduces_active77_active76_and_active75": True,
    }


def all_active_arithmetic_gate():
    """Check the formula's prefix, one-step growth, and literal capacity.

    This enumerates only integer shape/width inequalities, never matrices.
    It therefore checks every A in the full possible outer-Z band cheaply.
    """
    records = []
    minimum = None
    for active in range(C.L - OUTER_Z):  # 0..77: positive remaining u0.
        for y, r, s, z in physical_shapes(active):
            qmax = staircase_qmax(y, s)
            assert 0 <= qmax < M - y
            qset = tuple(range(qmax + 1))
            width = F.H.width(y, r, s)
            needed = len(qset) * N
            slack = width - needed
            assert slack >= 0
            record = (slack, active, (y, r, s, z), qset, width, needed)
            records.append(record)
            minimum = record if minimum is None or record < minimum else minimum

            # Lowering active by one sends y to y-1, hence d to d+1.  The
            # staircase asks for at most one additional initial jet.
            if y:
                next_qmax = staircase_qmax(y - 1, s)
                assert next_qmax - qmax in (0, 1)

    assert minimum == (
        76_929, 22, (1, 11, 10, OUTER_Z), tuple(range(30)),
        7_941_249, 30 * N)
    assert len(records) == 11_154
    return {
        "active_range_checked": (0, C.L - OUTER_Z - 1),
        "physical_shape_count_checked": len(records),
        "minimum_slack_active_physical_qset_width_needed": minimum,
        "every_qset_is_an_initial_prefix": True,
        "every_selected_qset_fits_its_literal_all_node_Hermite_window": True,
        "under_A_to_Aminus1_every_transferred_channel_gains_at_most_one_jet":
            True,
        "formula": (
            "qmax(y,s)=max(0,floor((59-y)/3),"
            "floor((49-y+s)/2)); B_A takes q=0..qmax on every admissible "
            "y+r+s=A, r+s<=21, s<=10, y<60"),
    }


def exact_original_provenance(coordinates, rows):
    coordinate_keys = {key for key, _column in coordinates}
    payload = []
    origin_count_histogram = Counter()
    kind_histogram = Counter()
    grouped_blocks = defaultdict(dict)
    for row in rows:
        origins = C.exact_target_provenance(row)
        assert origins and all(origin["u0_power"] == 3 for origin in origins)
        signatures = tuple(F.origin_signature(origin) for origin in origins)
        payload.append((row, signatures))
        origin_count_histogram[len(origins)] += 1
        kind_histogram.update(origin["kind"] for origin in origins)
        for origin in origins:
            sink = (
                origin["contact_f"], origin["r"], origin["s"],
                origin["coefficient_hasse_q"], OUTER_Z,
            )
            assert sink in coordinate_keys
            group = (
                origin["kind"], origin["r"], origin["s"],
                origin["source_y_or_k"], origin["contact_f"],
                origin["u_power_h"], origin["u0_power"],
                origin["coefficient_hasse_q"],
                origin["coefficient_width"],
            )
            assert row not in grouped_blocks[group]
            grouped_blocks[group][row] = origin["scalar_mod_p_before_Uh_Hq"]

    group_receipts = []
    for group, actual_column in sorted(grouped_blocks.items()):
        kind, r, s, k, f, h, rem, q, width = group
        sink = (f, r, s, q, OUTER_Z)
        common_scalar = comb(k, f) * comb(k - f, h) % P
        expected_column = {
            row: common_scalar * coefficient % P
            for row, coefficient in raw_contact_column(ACTIVE, sink).items()
        }
        assert actual_column == expected_column
        group_receipts.append((group, sink, common_scalar,
                               tuple(sorted(actual_column.items()))))

    total_origins = sum(size * count
                        for size, count in origin_count_histogram.items())
    assert (len(rows), total_origins, len(grouped_blocks)) == (154, 2_629, 583)
    assert kind_histogram == Counter({"P": 1_749, "C": 880})
    return {
        "row_origin_group_counts": (len(rows), total_origins,
                                    len(grouped_blocks)),
        "origin_count_per_row_histogram": tuple(sorted(
            origin_count_histogram.items())),
        "origin_kind_histogram": tuple(sorted(kind_histogram.items())),
        "every_original_origin_has_u0_power_three": True,
        "every_original_origin_sink_is_one_of_231_raw_coordinates": True,
        "every_group_aggregates_to_common_scalar_times_raw_column": True,
        "all_origin_signatures_sha256": hashlib.sha256(
            json.dumps(payload, separators=(",", ":")).encode()
        ).hexdigest(),
        "all_grouped_raw_column_identities_sha256": hashlib.sha256(
            repr(tuple(group_receipts)).encode()).hexdigest(),
    }


def preceding_section_first_outgoing(coordinates, rows):
    previous_coordinates, previous_rows, _rank = R.complete_coordinate_census()
    previous_selected, previous_physical_qsets, _windows, _receipt = (
        R.initial_jet_basis(previous_coordinates, previous_rows))
    previous_physical = set(previous_physical_qsets)
    assert len(previous_selected) == 79 and len(previous_physical) == 55
    coordinate_keys = {key for key, _column in coordinates}
    outgoing_rows = set()
    occurrence_count = 0
    records = []
    for source in sorted(previous_physical):
        source_y, r, s, z = source
        f = source_y - 1
        assert f + r + s == ACTIVE
        for q in range(M - f):
            sink = (f, r, s, q, z)
            assert sink in coordinate_keys
            column = raw_contact_column(ACTIVE, sink)
            outgoing_rows.update(column)
            occurrence_count += len(column)
            records.append((source, sink, source_y % P,
                            tuple(sorted(column.items()))))
    assert (len(records), occurrence_count, len(outgoing_rows)) == (
        220, 869, 154)
    assert outgoing_rows == set(rows)
    return {
        "preceding_physical_sections": len(previous_physical),
        "earliest_outgoing_block_occurrence_row_counts": (
            len(records), occurrence_count, len(outgoing_rows)),
        "earliest_order_derivation": (
            "h=0 minimizes outer Z; f=y-1 minimizes J-active among f<y; "
            "the remaining u0 power is exactly two"),
        "every_outgoing_sink_is_one_of_231_raw_coordinates": True,
        "outgoing_rows_equal_complete_154_row_universe": True,
        "outgoing_block_receipts_sha256": hashlib.sha256(
            repr(tuple(records)).encode()).hexdigest(),
    }


def independent_row_indices(matrix):
    """Deterministically retain the first independent rows over F_p."""
    basis = {}
    chosen = []
    for row_index, row in enumerate(matrix):
        work = [value % P for value in row]
        for pivot in sorted(basis):
            if work[pivot]:
                factor = work[pivot]
                work = [(left - factor * right) % P
                        for left, right in zip(work, basis[pivot])]
        pivot = next((i for i, value in enumerate(work) if value), None)
        if pivot is None:
            continue
        inverse = pow(work[pivot], -1, P)
        work = [value * inverse % P for value in work]
        basis[pivot] = work
        chosen.append(row_index)
    return tuple(chosen)


def exact_active75_basis_gate(coordinates, rows, selected, physical_qsets):
    windows = []
    for physical, qset in sorted(physical_qsets.items()):
        y, r, s, _z = physical
        width = F.H.width(y, r, s)
        needed = len(qset) * N
        windows.append((width - needed, physical, tuple(sorted(qset)),
                        width, needed))
    assert min(windows) == (
        208_053, (54, 12, 9, OUTER_Z), (0, 1, 2), 994_485, 3 * N)

    full_matrix = [
        [column.get(row, 0) for _key, column in selected] for row in rows
    ]
    selected_rank = F.modular_rank(full_matrix)
    union_rank = F.modular_rank([
        [column.get(row, 0)
         for _key, column in selected + tuple(coordinates)]
        for row in rows
    ])
    assert (len(selected), selected_rank, union_rank) == (103, 103, 103)

    # Process falsifier: support matching over all 154 rows is not enough.
    # Its determinant is singular.  Select an independent row basis first.
    all_row_index = {row: i for i, row in enumerate(rows)}
    naive_adjacency = tuple(tuple(all_row_index[row] for row in column)
                            for _key, column in selected)
    naive_match, _ = F.hopcroft_karp(naive_adjacency, len(rows))
    assert all(index >= 0 for index in naive_match)
    naive_rows = tuple(rows[index] for index in naive_match)
    naive_matrix = [[column.get(naive_rows[i], 0)
                     for _key, column in selected]
                    for i in range(len(selected))]
    naive_rank, naive_det = F.modular_rank_and_det(naive_matrix)
    assert (naive_rank, naive_det) == (42, 0)

    independent = independent_row_indices(full_matrix)
    assert len(independent) == 103
    basis_rows = tuple(rows[index] for index in independent)
    basis_row_index = {row: i for i, row in enumerate(basis_rows)}
    adjacency = tuple(tuple(basis_row_index[row] for row in column
                            if row in basis_row_index)
                      for _key, column in selected)
    match_l, _match_r = F.hopcroft_karp(adjacency, len(basis_rows))
    assert all(index >= 0 for index in match_l)
    pivot_rows = tuple(basis_rows[index] for index in match_l)
    pivot_owner = {row: i for i, row in enumerate(pivot_rows)}
    assert len(pivot_owner) == 103

    matrix = [[column.get(pivot_rows[row_owner], 0)
               for _key, column in selected]
              for row_owner in range(103)]
    rank, determinant = F.modular_rank_and_det(matrix)
    assert (rank, determinant) == (103, 4_161_536)  # -1/512.
    matching_hash = hashlib.sha256(repr(tuple(
        (selected[i][0], pivot_rows[i], selected[i][1][pivot_rows[i]])
        for i in range(103)
    )).encode()).hexdigest()
    assert matching_hash == (
        "95516c0a1bd9789d0b85d375dd793473f87849569e9302d93020a297f7615286")
    row_basis_hash = hashlib.sha256(repr(basis_rows).encode()).hexdigest()
    assert row_basis_hash == (
        "a081213f5962ef725969557ecb024dcbb48d1af07a829698f1a7972f07617197")

    graph = []
    induced_edges = []
    for source, (key, column) in enumerate(selected):
        y, r, s, _q, z = key
        successors = {pivot_owner[row] for row in column
                      if row in pivot_owner}
        qmax = max(physical_qsets[(y, r, s, z)])
        for induced_q in range(qmax + 1, M - y):
            induced_column = raw_contact_column(
                ACTIVE, (y, r, s, induced_q, z))
            for row in induced_column:
                if row not in pivot_owner:
                    continue
                target = pivot_owner[row]
                successors.add(target)
                induced_edges.append((source, target, key, induced_q, row))
        graph.append(tuple(sorted(successors)))
    graph = tuple(graph)
    components = F.tarjan_scc(graph)
    owner_component = {
        member: component_index
        for component_index, component in enumerate(components)
        for member in component
    }

    histogram = Counter()
    component_keys = []
    nontrivial = []
    for component in components:
        diagonal = [
            [selected[column][1].get(pivot_rows[row_owner], 0)
             for column in component]
            for row_owner in component
        ]
        component_rank, component_det = F.modular_rank_and_det(diagonal)
        assert component_rank == len(component) and component_det
        histogram[(len(component), component_rank, component_det)] += 1
        component_keys.append(tuple(selected[i][0] for i in component))
        if len(component) > 2:
            nontrivial.append((
                tuple(selected[i][0] for i in component),
                tuple(pivot_rows[i] for i in component),
                component_rank, component_det,
            ))

    assert Counter(map(len, components)) == Counter({1: 32, 2: 31, 6: 1,
                                                      3: 1})
    assert histogram == Counter({
        (1, 1, 1): 32,
        (2, 2, P - 1): 20,
        (2, 2, 1): 9,
        (2, 2, -INV2 % P): 2,
        (6, 6, 133_169_152): 1,  # -1/16.
        (3, 3, 1_864_368_129): 1,  # +1/8.
    })
    assert len(induced_edges) == 534
    assert all(owner_component[source] != owner_component[target]
               for source, target, _key, _q, _row in induced_edges)
    assert all(
        pivot_rows[target][0] + 3 * pivot_rows[target][1]
        > selected[source][0][0] + selected[source][0][3]
        for source, target, _key, _q, _row in induced_edges)
    assert all(
        pivot_rows[target][0] + 3 * pivot_rows[target][1]
        >= selected[source][0][0] + selected[source][0][3]
        for source, successors in enumerate(graph) for target in successors)

    levels = Counter(key[0] + key[3] for key, _column in selected)
    assert levels == Counter({54: 11, 55: 22, 56: 24,
                              57: 23, 58: 12, 59: 11})
    component_hash = hashlib.sha256(
        repr(tuple(component_keys)).encode()).hexdigest()
    assert component_hash == (
        "029bf517d20ad27b260552760aef580fc6bba4390dae9b15de6f63f5f7b3b0ec")
    return {
        "selected_coordinate_physical_counts": (103, 66),
        "physical_qset_histogram": tuple(sorted(Counter(
            tuple(sorted(qset)) for qset in physical_qsets.values()).items())),
        "minimum_section_slack_physical_qset_width_needed": min(windows),
        "selected_and_selected_plus_all_231_ranks": (
            selected_rank, union_rank),
        "selected_spans_complete_raw_module": True,
        "invalid_arbitrary_support_matching_rank_determinant": (
            naive_rank, naive_det),
        "independent_rows_before_matching": True,
        "selected_103_by_103_rank_determinant_mod_p": (rank, determinant),
        "determinant_as_small_fraction": "-1/512",
        "expanded_all_node_rank_cokernel": (103 * N, 0),
        "ambient_154_row_type_cokernel": len(rows) - rank,
        "coordinate_level_y_plus_q_histogram": tuple(sorted(levels.items())),
        "matching_key_row_scalar_sha256": matching_hash,
        "independent_row_basis_sha256": row_basis_hash,
        "dependency_scc_size_histogram": tuple(sorted(
            Counter(map(len, components)).items())),
        "scc_size_rank_determinant_histogram": tuple(sorted(histogram.items())),
        "size_gt_two_scc_keys_rows_rank_det": tuple(nontrivial),
        "component_physical_keys_sha256": component_hash,
        "induced_higher_jet_edge_count": len(induced_edges),
        "no_induced_higher_jet_edge_inside_an_scc": True,
        "all_induced_higher_jet_edges_strictly_increase_contact_weight": True,
        "all_dependency_edges_non_decreasing_in_contact_weight": True,
    }


def outgoing_filtration(selected, rows):
    physical = {key[:3] + key[4:] for key, _column in selected}
    assert len(physical) == 66
    counts = Counter()
    same_rows = set()
    for y, r, s, z in sorted(physical):
        source_order = (z, J - (y + r + s))
        for f in range(y + 1):
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    q_count = max(0, M - (f + 2 * a_e + c_s))
                    if not q_count:
                        continue
                    if f == y:
                        counts["same_filtration_full_contact"] += q_count
                        for q in range(q_count):
                            same_rows.add(C.row_of(
                                r, s, z, f, 0, a_e, c_s, q))
                    else:
                        assert (z, J - (f + r + s)) > source_order
                        assert (z + y - f,
                                J - (f + r + s)) > source_order
                        counts["strictly_later_u0free"] += q_count
                        counts["strictly_later_positive_u0"] += (
                            (y - f) * q_count)
    assert counts == Counter({
        "same_filtration_full_contact": 880,
        "strictly_later_u0free": 7_203_724,
        "strictly_later_positive_u0": 251_470_241,
    })
    assert same_rows == set(rows)
    return {
        "common_order": "lexicographic (outer Z, J-active degree)",
        "physical_section_polynomial_count": len(physical),
        "same_filtration_distinct_rows": len(same_rows),
        "occurrence_counts": tuple(sorted(counts.items())),
        "all_nonfull_contact_outputs_strictly_advance_common_order": True,
    }


def main():
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(HERE / filename) == expected

    (coordinates, rows, selected, qsets), reproduction = (
        known_block_reproduction())
    assert (len(coordinates), len(rows), len(selected)) == (231, 154, 103)
    assert sum(len(column) for _key, column in coordinates) == 880
    arithmetic = all_active_arithmetic_gate()
    provenance = exact_original_provenance(coordinates, rows)
    incoming = preceding_section_first_outgoing(coordinates, rows)
    basis = exact_active75_basis_gate(coordinates, rows, selected, qsets)
    outgoing = outgoing_filtration(selected, rows)

    stable = {
        "scope": (
            "whole (outerZ,active)=(2625,75) diagonal, plus exact integer "
            "legality of the closed B_A staircase for 0<=A<=77; no later "
            "diagonal matrices are expanded"),
        "target_p_N_M_J_outerZ_active": (P, N, M, J, OUTER_Z, ACTIVE),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "parametric_staircase_reproduction": reproduction,
        "all_active_literal_arithmetic": arithmetic,
        "complete_active75_raw_coordinate_census": {
            "coordinates_rows_entries_rank_cokernel": (231, 154, 880,
                                                        103, 51),
            "row_universe_sha256": hashlib.sha256(
                repr(rows).encode()).hexdigest(),
        },
        "complete_original_same_key_provenance": provenance,
        "exact_incoming_from_preceding_55_sections": incoming,
        "legal_active75_initial_jet_basis_and_scc_gate": basis,
        "outgoing_filtration": outgoing,
        "candidate_induction_invariant": (
            "Let V_A be the fixed-(2625,A) raw contact module and B_A the "
            "initial prefixes q=0..qmax(y,s).  The desired straightening "
            "lemma is span(B_A)=V_A.  Under A->A-1, every transferred "
            "channel is (y,r,s)->(y-1,r,s), qmax grows by at most one, and "
            "only y=59 boundary value channels need separate seeds.  Order "
            "rows by contact weight i+3a and close equal-weight SCCs by the "
            "unit Pascal minors; all induced higher jets increase weight and "
            "all nonfull contacts increase lex (outerZ,J-active)."),
        "candidate_uniform_proof_conditions": (
            "admissible shapes y+r+s=A, r+s<=21, s<=10, y<60; "
            "char(F)>60 so factorial/Pascal pivots and observed small minors "
            "are units; 2 is invertible for curvature; literal coefficient "
            "capacity (qmax+1)*262144<=width(y,r,s); positive remaining u0 "
            "for A<=77; and a uniform symbolic proof that the equal-weight "
            "Pascal SCC minors stay units for every admissible boundary."),
        "decision": "GREEN_ACTIVE75_AND_PARAMETRIC_STAIRCASE_CANDIDATE",
        "scope_guard": (
            "The formula and every Hermite-capacity inequality are global in "
            "A, but span(B_A)=V_A is matrix-proved only for A=75,76,77.  A "
            "symbolic Pascal straightening/minor lemma, lower-A boundary "
            "proof, passive-band transport, and F0..F3 integration remain."),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": file_sha256(Path(__file__)),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
