#!/usr/bin/env python3
"""Exact next positive-u0 Full187 initial-jet recurrence gate.

After quotienting the GREEN (outer Z,active)=(2625,77) block in commit
0feaaa1, the lexicographically first outgoing component has h=0 and loses one
contact factor.  It is exactly (2625,76).  This script enumerates that whole
component, groups every original C/P origin, aggregates the first outgoing
tail of all 44 preceding sections, and applies the same initial-Hasse-jet
legality/SCC falsifier.  It never expands the 177-million-occurrence tail.
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


P = F.P
N = F.N
M = F.M
J = F.J
OUTER_Z = F.OUTER_Z
ACTIVE = 76
INV2 = F.INV2

AUTHORITIES = {
    "full187_cross_slope_second_fringe_confluence_6900.py":
        "2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29",
    "full187_earliest_positive_u0_curvature_frontier_gate_6900.py":
        "cd763ffc825c0a9e1d73f055d1278b583fdcdac162a5ed597e289e24d4db53b0",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def raw_contact_column(key):
    """Full live support of H_q(P) contactY^y R^r S^s Z^z."""
    y, r, s, q, z = key
    assert y + r + s == ACTIVE and z == OUTER_Z
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


def complete_coordinate_census():
    coordinates = []
    for y in range(ACTIVE - F.H.SLOPE, M):
        for s in range(F.H.CURVATURE + 1):
            r = ACTIVE - y - s
            assert r >= 0 and r + s <= F.H.SLOPE
            for q in range(M - y):
                key = (y, r, s, q, OUTER_Z)
                coordinates.append((key, raw_contact_column(key)))
    rows = tuple(sorted(
        set().union(*(set(column) for _key, column in coordinates)),
        key=lambda row: (row[0] + 3 * row[1], row),
    ))
    matrix = [[column.get(row, 0) for _key, column in coordinates]
              for row in rows]
    rank = F.modular_rank(matrix)
    assert (len(coordinates), len(rows),
            sum(len(column) for _key, column in coordinates), rank) == (
                165, 112, 506, 79)
    return tuple(coordinates), rows, {
        "raw_coordinates_rows_entries_rank_cokernel": (
            len(coordinates), len(rows), 506, rank, len(rows) - rank),
        "coordinate_y_histogram": tuple(sorted(Counter(
            key[0] for key, _column in coordinates).items())),
        "row_contact_weight_histogram": tuple(sorted(Counter(
            row[0] + 3 * row[1] for row in rows).items())),
        "row_universe_sha256": hashlib.sha256(repr(rows).encode()).hexdigest(),
    }


def exact_original_provenance(coordinates, rows):
    """Group all original top-source origins into complete raw columns."""
    coordinate_keys = {key for key, _column in coordinates}
    payload = []
    origin_count_histogram = Counter()
    kind_histogram = Counter()
    grouped_blocks = defaultdict(dict)
    for row in rows:
        origins = C.exact_target_provenance(row)
        assert origins and all(origin["u0_power"] == 2 for origin in origins)
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
            grouped_blocks[group][row] = (
                origin["scalar_mod_p_before_Uh_Hq"])

    group_receipts = []
    for group, actual_column in sorted(grouped_blocks.items()):
        kind, r, s, k, f, h, rem, q, width = group
        sink = (f, r, s, q, OUTER_Z)
        common_scalar = comb(k, f) * comb(k - f, h) % P
        expected_column = {
            row: common_scalar * coefficient % P
            for row, coefficient in raw_contact_column(sink).items()
        }
        assert actual_column == expected_column
        group_receipts.append((group, sink, common_scalar,
                               tuple(sorted(actual_column.items()))))

    assert sum(size * count for size, count
               in origin_count_histogram.items()) == 1_595
    assert kind_histogram == Counter({"P": 1_089, "C": 506})
    assert len(grouped_blocks) == 451
    return {
        "row_origin_group_counts": (len(rows), 1_595, 451),
        "origin_count_per_row_histogram": tuple(sorted(
            origin_count_histogram.items())),
        "origin_kind_histogram": tuple(sorted(kind_histogram.items())),
        "every_original_origin_has_u0_power_two": True,
        "every_original_origin_sink_is_one_of_165_raw_coordinates": True,
        "every_group_aggregates_to_common_scalar_times_raw_column": True,
        "all_1595_origin_signatures_sha256": hashlib.sha256(
            json.dumps(payload, separators=(",", ":")).encode()
        ).hexdigest(),
        "all_451_grouped_raw_column_identities_sha256": hashlib.sha256(
            repr(tuple(group_receipts)).encode()).hexdigest(),
    }


def preceding_section_first_outgoing(coordinates, rows):
    """Aggregate exactly h=0, f=y-1 from the 44 preceding sections."""
    previous_all, previous_safe, _previous_unsafe = F.all_diagonal_coordinates()
    previous_selected, previous_physical, _windows, _receipt = (
        F.initial_jet_coordinates(previous_all, previous_safe))
    assert len(previous_selected) == 56 and len(previous_physical) == 44
    coordinate_keys = {key for key, _column in coordinates}
    outgoing_rows = set()
    occurrence_count = 0
    records = []
    for source in sorted(previous_physical):
        source_y, r, s, z = source
        f = source_y - 1
        assert z == OUTER_Z and f + r + s == ACTIVE
        for q in range(M - f):
            sink = (f, r, s, q, z)
            assert sink in coordinate_keys
            column = raw_contact_column(sink)
            outgoing_rows.update(column)
            occurrence_count += len(column)
            # binom(source_y,f)=source_y; h=0 and the remaining u0 power is 1.
            records.append((source, sink, source_y % P,
                            tuple(sorted(column.items()))))
    assert (len(records), occurrence_count, len(outgoing_rows)) == (
        154, 495, 112)
    assert outgoing_rows == set(rows)
    return {
        "preceding_physical_sections": len(previous_physical),
        "earliest_outgoing_block_occurrence_row_counts": (
            len(records), occurrence_count, len(outgoing_rows)),
        "earliest_order_derivation": (
            "h=0 minimizes outer Z; f=y-1 minimizes J-active among f<y; "
            "the remaining u0 power is exactly one"),
        "every_outgoing_sink_is_one_of_165_raw_coordinates": True,
        "outgoing_rows_equal_complete_112_row_universe": True,
        "outgoing_block_receipts_sha256": hashlib.sha256(
            repr(tuple(records)).encode()).hexdigest(),
    }


def initial_jet_basis(coordinates, rows):
    """The first repeated initial-jet staircase at active degree 76."""
    by_key = dict(coordinates)
    keys = []
    # q=0 on all 55 physical shapes.
    for y in range(55, 60):
        for s in range(11):
            keys.append((y, ACTIVE - y - s, s, 0, OUTER_Z))
    # q=1 on the bottom two contact layers, plus the curvature-cap neighbour.
    for y in (55, 56):
        for s in range(11):
            keys.append((y, ACTIVE - y - s, s, 1, OUTER_Z))
    keys.append((57, 9, 10, 1, OUTER_Z))
    # The one remaining direction is the next initial jet at the bottom cap.
    keys.append((55, 11, 10, 2, OUTER_Z))
    assert len(keys) == len(set(keys)) == 79
    selected = tuple((key, by_key[key]) for key in keys)

    physical_qsets = defaultdict(set)
    for y, r, s, q, z in keys:
        physical_qsets[(y, r, s, z)].add(q)
    qset_histogram = Counter(tuple(sorted(qset))
                             for qset in physical_qsets.values())
    assert len(physical_qsets) == 55
    assert qset_histogram == Counter({
        (0,): 32,
        (0, 1): 22,
        (0, 1, 2): 1,
    })

    windows = []
    for physical, qset in sorted(physical_qsets.items()):
        y, r, s, _z = physical
        width = F.H.width(y, r, s)
        needed = len(qset) * N
        windows.append((width - needed, physical, tuple(sorted(qset)),
                        width, needed))
    assert min(windows) == (
        76_983, (55, 11, 10, OUTER_Z), (0, 1, 2), 863_415, 3 * N)

    selected_rank = F.modular_rank([
        [column.get(row, 0) for _key, column in selected] for row in rows
    ])
    union_rank = F.modular_rank([
        [column.get(row, 0)
         for _key, column in selected + tuple(coordinates)]
        for row in rows
    ])
    assert (selected_rank, union_rank) == (79, 79)
    return selected, physical_qsets, tuple(windows), {
        "selected_coordinate_physical_counts": (79, 55),
        "physical_qset_histogram": tuple(sorted(qset_histogram.items())),
        "minimum_section_slack_physical_qset_width_needed": min(windows),
        "selected_and_selected_plus_all_165_ranks": (
            selected_rank, union_rank),
        "selected_spans_complete_raw_module": True,
    }


def exact_scc_gate(rows, selected, physical_qsets, windows):
    row_index = {row: i for i, row in enumerate(rows)}
    support_adjacency = tuple(tuple(
        row_index[row] for row in column
    ) for _key, column in selected)
    match_l, _match_r = F.hopcroft_karp(support_adjacency, len(rows))
    assert all(index >= 0 for index in match_l)
    pivot_rows = tuple(rows[index] for index in match_l)
    pivot_owner = {row: i for i, row in enumerate(pivot_rows)}
    assert len(pivot_owner) == 79

    matrix = [[column.get(pivot_rows[row_owner], 0)
               for _key, column in selected]
              for row_owner in range(79)]
    rank, determinant = F.modular_rank_and_det(matrix)
    assert (rank, determinant) == (79, 299_630_593)  # 55/64

    graph = []
    induced_edges = []
    for source, (key, column) in enumerate(selected):
        y, r, s, _q, z = key
        successors = {
            pivot_owner[row] for row in column if row in pivot_owner
        }
        qmax = max(physical_qsets[(y, r, s, z)])
        for induced_q in range(qmax + 1, M - y):
            induced_column = raw_contact_column((y, r, s, induced_q, z))
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
    size_five = None
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
        if len(component) == 5:
            size_five = (
                tuple(selected[i][0] for i in component),
                tuple(pivot_rows[i] for i in component),
                component_rank, component_det,
            )

    assert Counter(map(len, components)) == Counter({1: 32, 2: 21, 5: 1})
    assert histogram == Counter({
        (1, 1, 1): 32,
        (2, 2, P - 1): 18,
        (2, 2, INV2): 2,
        (2, 2, 1): 1,
        (5, 5, 1_198_522_372): 1,  # 55/16
    })
    assert size_five is not None
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
    assert min(windows)[0] == 76_983

    levels = Counter(key[0] + key[3] for key, _column in selected)
    assert levels == Counter({55: 11, 56: 22, 57: 23, 58: 12, 59: 11})
    return {
        "selected_79_by_79_rank_determinant_mod_p": (rank, determinant),
        "determinant_as_small_fraction": "55/64",
        "expanded_all_node_rank_cokernel": (79 * N, 0),
        "ambient_112_row_type_cokernel": len(rows) - rank,
        "coordinate_level_y_plus_q_histogram": tuple(sorted(levels.items())),
        "matching_key_row_scalar_sha256": hashlib.sha256(repr(tuple(
            (selected[i][0], pivot_rows[i],
             selected[i][1][pivot_rows[i]]) for i in range(79)
        )).encode()).hexdigest(),
        "dependency_scc_size_histogram": tuple(sorted(
            Counter(map(len, components)).items())),
        "scc_size_rank_determinant_histogram": tuple(sorted(histogram.items())),
        "unique_size_five_scc_keys_rows_rank_det": size_five,
        "component_physical_keys_sha256": hashlib.sha256(
            repr(tuple(component_keys)).encode()).hexdigest(),
        "induced_higher_jet_edge_count": len(induced_edges),
        "no_induced_higher_jet_edge_inside_an_scc": True,
        "all_induced_higher_jet_edges_strictly_increase_contact_weight": True,
        "all_dependency_edges_non_decreasing_in_contact_weight": True,
    }


def outgoing_filtration(selected, rows):
    physical = {key[:3] + key[4:] for key, _column in selected}
    assert len(physical) == 55
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
        "same_filtration_full_contact": 506,
        "strictly_later_u0free": 6_003_679,
        "strictly_later_positive_u0": 212_560_172,
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
    coordinates, rows, census = complete_coordinate_census()
    provenance = exact_original_provenance(coordinates, rows)
    incoming = preceding_section_first_outgoing(coordinates, rows)
    selected, physical_qsets, windows, basis = initial_jet_basis(
        coordinates, rows)
    scc = exact_scc_gate(rows, selected, physical_qsets, windows)
    outgoing = outgoing_filtration(selected, rows)

    stable = {
        "scope": (
            "whole lexicographically earliest outgoing component after the "
            "GREEN active77 quotient: (outerZ,active)=(2625,76); all later "
            "filtration components remain open"),
        "target_p_N_M_J_outerZ_active": (P, N, M, J, OUTER_Z, ACTIVE),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "complete_raw_coordinate_census": census,
        "complete_original_same_key_provenance": provenance,
        "exact_incoming_from_preceding_44_sections": incoming,
        "legal_initial_jet_basis": basis,
        "exact_dependency_scc_gate": scc,
        "outgoing_filtration": outgoing,
        "uniform_recurrence_evidence": (
            "active77 used 32 {0} and 12 {0,1} physical q-sets; active76 "
            "uses 32 {0}, 22 {0,1}, and one {0,1,2}. The new bottom contact "
            "layer is promoted to the next complete Hermite depth, while "
            "curvature-cap neighbours supply the extra boundary directions. "
            "This is two consecutive exact GREEN blocks, not an induction."),
        "decision": "GREEN_NEXT_POSITIVE_U0_INITIAL_JET_RECURRENCE_BLOCK",
        "scope_guard": (
            "This does not expand or close the 218,563,851 outgoing "
            "occurrences, prove the uniform recurrence for every active "
            "degree/passive band, connect F0..F3, or create a candidate."),
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
