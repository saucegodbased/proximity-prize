#!/usr/bin/env python3
"""Exact earliest positive-u0/error-facing Full187 frontier gate.

The whole first-later-Z receipt b86d33b supplies four physical section
polynomials at outer Z 2625 and 2626.  In its common filtration, the earliest
new grade is the h=0, one-u0 layer of the two band-1 sections.  This script:

* enumerates the seven initially hit rows and all 114 top-source origins;
* enumerates the complete 73-row same-key block and all 880 physical origins;
* proves the apparent 45/47 strong-capacity defect annihilates the actual
  Pascal tail and all variations made by b86d33b;
* repairs the invalid isolated-q antiderivative idea by prescribing initial
  Hasse jets: 12 legal two-jet sections and 32 legal value sections;
* retains every induced higher coefficient jet in the pivot graph and checks
  a 56-dimensional exact target-field Popov minor component by component.

The result is only a GREEN for this earliest diagonal.  Its lower-contact
exports are oriented but not solved.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import resource
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import full187_all_noncapacity_pascal_hermite_slide_6900 as A
import full187_complete_depth_pascal_hermite_slide_6900 as CD
import full187_cross_slope_second_fringe_confluence_6900 as C
import full187_terminal_lowT_hasse_closure_audit_6900 as H


P = 2_130_706_433
N = 262_144
M = 60
J = 82
G = 180_413
ERRORS = 81_731
OUTER_Z = 2_625
ACTIVE = 77
INV2 = pow(2, -1, P)

AUTHORITIES = {
    "full187_all_noncapacity_pascal_hermite_slide_6900.py":
        "d9c351812caded22dd2cf90abfa6892b830180854d68fdff641bcf4037c7bcae",
    "full187_complete_depth_pascal_hermite_slide_6900.py":
        "e6de6ca5273bcae6e369b7ffd779c815a393c6e7e3494ee8853f7c3ab1d46969",
    "full187_cross_slope_second_fringe_confluence_6900.py":
        "2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29",
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


def section_slack(key):
    """Mixed-CRT plus q-fold Hasse-antiderivative coefficient slack."""
    y, r, s, q, _z = key
    depth = M - (y + q)
    assert depth > 0
    return H.width(y, r, s) - (G * depth + ERRORS + q)


def all_diagonal_coordinates():
    all_coordinates = []
    safe = []
    unsafe = []
    for y in range(56, 60):
        for s in range(H.CURVATURE + 1):
            r = ACTIVE - y - s
            assert r >= 0 and r + s <= H.SLOPE
            for q in range(M - y):
                key = (y, r, s, q, OUTER_Z)
                column = raw_contact_column(key)
                all_coordinates.append((key, column))
                (safe if section_slack(key) >= 0 else unsafe).append(
                    (key, column))
    assert len(all_coordinates) == 110
    assert len(safe) == 99 and len(unsafe) == 11
    assert tuple(key[:4] for key, _column in unsafe) == tuple(
        (56, 21 - s, s, 0) for s in range(11))
    return tuple(all_coordinates), tuple(safe), tuple(unsafe)


def modular_rank(matrix):
    if not matrix:
        return 0
    a = [[value % P for value in row] for row in matrix]
    rank = 0
    for column in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a))
                      if a[i][column]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inverse = pow(a[rank][column], -1, P)
        a[rank] = [value * inverse % P for value in a[rank]]
        for i in range(len(a)):
            if i == rank or not a[i][column]:
                continue
            factor = a[i][column]
            a[i] = [(left - factor * right) % P
                    for left, right in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def modular_rank_and_det(matrix):
    assert matrix and len(matrix) == len(matrix[0])
    a = [[value % P for value in row] for row in matrix]
    rank = 0
    determinant = 1
    sign = 1
    for column in range(len(a)):
        pivot = next((i for i in range(rank, len(a))
                      if a[i][column]), None)
        if pivot is None:
            return rank, 0
        if pivot != rank:
            a[rank], a[pivot] = a[pivot], a[rank]
            sign = -sign
        value = a[rank][column]
        determinant = determinant * value % P
        inverse = pow(value, -1, P)
        for i in range(rank + 1, len(a)):
            if not a[i][column]:
                continue
            factor = a[i][column] * inverse % P
            a[i] = [(left - factor * right) % P
                    for left, right in zip(a[i], a[rank])]
        rank += 1
    return rank, determinant * sign % P


def dot(dual, column):
    return sum(coefficient * column.get(row, 0)
               for row, coefficient in dual.items()) % P


def safe_raw_module(safe):
    rows = tuple(sorted(
        set().union(*(set(column) for _key, column in safe)),
        key=lambda row: (row[0] + 3 * row[1], row),
    ))
    matrix = [[column.get(row, 0) for _key, column in safe] for row in rows]
    rank = modular_rank(matrix)
    entries = sum(len(column) for _key, column in safe)
    assert (len(rows), len(safe), entries, rank) == (47, 99, 198, 45)

    # The two exact row relations are supported at the curvature cap.  They
    # are independent and account for the complete two-dimensional cokernel.
    e_row = (56, 1, 66, 10, OUTER_Z)
    s1_row = (58, 0, 66, 11, OUTER_Z)
    ordinary_row = (57, 0, 67, 10, OUTER_Z)
    s2_row = (59, 0, 65, 12, OUTER_Z)
    duals = (
        {e_row: 1, s1_row: 2},
        {e_row: -14 % P, ordinary_row: 399, s2_row: 1},
    )
    assert all(all(dot(dual, column) == 0
                   for _key, column in safe) for dual in duals)
    assert modular_rank([
        [dual.get(row, 0) for row in rows] for dual in duals
    ]) == 2
    return rows, duals, {
        "safe_coordinates_rows_entries_rank_cokernel": (
            len(safe), len(rows), entries, rank, len(rows) - rank),
        "dual_relations": (
            "row(56,1,66,10)+2*row(58,0,66,11)=0",
            "-14*row(56,1,66,10)+399*row(57,0,67,10)"
            "+row(59,0,65,12)=0",
        ),
        "every_safe_column_annihilated_by_both_duals": True,
    }


def first_positive_frontier_rows():
    rows = set()
    source_receipts = []
    # These are precisely the two physical section polynomials at band 1 of
    # b86d33b.  q_min records H0=0 for its P57 variation.
    for source_name, k, r, s, q_min in (
            ("P58_two_jet_section", 58, 10, 10, 0),
            ("P57_H0zero_H1_section", 57, 11, 10, 1)):
        f = k - 1
        local_rows = set()
        for a_e in range(f + 1):
            for c_s in range(f - a_e + 1):
                for q in range(q_min, M - (f + 2 * a_e + c_s)):
                    row = C.row_of(r, s, OUTER_Z, f, 0, a_e, c_s, q)
                    local_rows.add(row)
                    rows.add(row)
        source_receipts.append((source_name, k, r, s, q_min,
                                tuple(sorted(local_rows))))
    rows = tuple(sorted(rows, key=lambda row: (row[0] + 3 * row[1], row)))
    assert rows == (
        (57, 0, 67, 10, 2625),
        (58, 0, 66, 11, 2625),
        (58, 0, 67, 10, 2625),
        (56, 1, 66, 10, 2625),
        (59, 0, 65, 12, 2625),
        (59, 0, 66, 11, 2625),
        (59, 0, 67, 10, 2625),
    )
    return rows, tuple(source_receipts)


def origin_signature(origin):
    return (
        origin["kind"], origin["r"], origin["s"],
        origin["source_y_or_k"], origin["contact_f"],
        origin["u_power_h"], origin["u0_power"], origin["aE"],
        origin["cS"], origin["coefficient_hasse_q"],
        origin["coefficient_width"],
        origin["scalar_mod_p_before_Uh_Hq"],
    )


def exact_top_source_provenance(rows):
    receipts = []
    payload = []
    block_keys = set()
    for row in rows:
        origins = C.exact_target_provenance(row)
        assert all(origin["u0_power"] == 1 for origin in origins)
        signatures = tuple(map(origin_signature, origins))
        for origin in origins:
            block_keys.add((
                origin["r"], origin["s"], origin["contact_f"],
                origin["coefficient_hasse_q"],
            ))
        receipts.append({
            "row": row,
            "contact_weight": row[0] + 3 * row[1],
            "origin_count": len(origins),
            "contact_block_count": len(set(
                (origin["r"], origin["s"], origin["contact_f"],
                 origin["coefficient_hasse_q"], origin["aE"],
                 origin["cS"])
                for origin in origins)),
            "origin_signature_sha256": hashlib.sha256(
                json.dumps(signatures, separators=(",", ":")).encode()
            ).hexdigest(),
        })
        payload.append((row, signatures))
    assert tuple(receipt["origin_count"] for receipt in receipts) == (
        11, 11, 20, 11, 11, 20, 30)
    assert sum(receipt["origin_count"] for receipt in receipts) == 114
    assert len(block_keys) == 19
    return tuple(receipts), tuple(sorted(block_keys)), hashlib.sha256(
        json.dumps(payload, separators=(",", ":")).encode()
    ).hexdigest()


def entire_same_key_provenance(all_coordinates):
    """Freeze every physical origin of the complete 73-row diagonal.

    The 110 raw coordinates are the exhaustive full-contact census: source
    contact degree is at least ``ACTIVE-SLOPE=56``, at most ``M-1=59``, and
    every legal curvature and live Hasse order is present.  Their row union is
    therefore the complete same-(outer Z,active) block.  For every such row we
    independently invert the original C/P source expansion as well.
    """
    rows = tuple(sorted(
        set().union(*(set(column) for _key, column in all_coordinates)),
        key=lambda row: (row[0] + 3 * row[1], row),
    ))
    assert len(rows) == 73

    payload = []
    coordinate_keys = {key for key, _column in all_coordinates}
    origin_count_histogram = Counter()
    kind_histogram = Counter()
    physical_blocks = set()
    for row in rows:
        origins = C.exact_target_provenance(row)
        assert origins and all(origin["u0_power"] == 1 for origin in origins)
        signatures = tuple(map(origin_signature, origins))
        payload.append((row, signatures))
        origin_count_histogram[len(origins)] += 1
        kind_histogram.update(origin["kind"] for origin in origins)
        physical_blocks.update((
            origin["kind"], origin["r"], origin["s"],
            origin["source_y_or_k"], origin["contact_f"],
            origin["coefficient_hasse_q"],
        ) for origin in origins)
        assert all((
            origin["contact_f"], origin["r"], origin["s"],
            origin["coefficient_hasse_q"], OUTER_Z,
        ) in coordinate_keys for origin in origins)

    assert sum(count * multiplicity for multiplicity, count
               in origin_count_histogram.items()) == 880
    assert kind_histogram == Counter({"P": 616, "C": 264})
    assert len(physical_blocks) == 330
    return rows, {
        "raw_coordinate_row_origin_block_counts": (
            len(all_coordinates), len(rows), 880, len(physical_blocks)),
        "origin_count_per_row_histogram": tuple(sorted(
            origin_count_histogram.items())),
        "origin_kind_histogram": tuple(sorted(kind_histogram.items())),
        "every_original_origin_has_u0_power_one": True,
        "every_original_origin_sink_is_one_of_110_raw_coordinates": True,
        "row_universe_sha256": hashlib.sha256(
            repr(rows).encode()).hexdigest(),
        "all_880_origin_signatures_sha256": hashlib.sha256(
            json.dumps(payload, separators=(",", ":")).encode()
        ).hexdigest(),
    }


def pascal_positive_tail_expression(r, s, f, q):
    """Actual one-u0 common coefficient after the complete-depth choices."""
    terminal_y = J - r - s
    correction_jets = {}
    for source_k in range(M - 1, f, -1):
        if q <= CD.complete_qmax(r, s, source_k):
            correction_jets[source_k] = A.negate(A.residual_expression(
                terminal_y, source_k, correction_jets))
        else:
            correction_jets[source_k] = {
                (("U", source_k, q), 0): 1,
            }

    expression = {}
    terminal_h = terminal_y - f - 1
    assert terminal_h >= 0
    A.add_scaled_shifted(
        expression, {(("C",), 0): 1},
        comb(terminal_y, f) * comb(terminal_y - f, terminal_h),
        terminal_h,
    )
    for source_k in range(f + 1, M):
        h = source_k - f - 1
        A.add_scaled_shifted(
            expression, correction_jets[source_k],
            comb(source_k, f) * (source_k - f), h,
        )
    return expression


def actual_tail_membership(block_keys, safe_key_set):
    records = []
    counts = Counter()
    for r, s, f, q in block_keys:
        expression = pascal_positive_tail_expression(r, s, f, q)
        sink_key = (f, r, s, q, OUTER_Z)
        safe = sink_key in safe_key_set
        counts[("safe" if safe else "unsafe",
                "nonzero" if expression else "zero")] += 1
        if expression:
            assert safe
        records.append((
            (r, s, f, q), safe,
            tuple(sorted(expression.items(), key=repr)),
        ))
    assert counts == Counter({
        ("safe", "zero"): 10,
        ("safe", "nonzero"): 6,
        ("unsafe", "zero"): 3,
    })

    # Arbitrary changes made by the b86d33b sections add only these six raw
    # blocks; each has its own safe lower-grade coordinate.
    section_variation_blocks = tuple(
        (57, 10, 10, q, OUTER_Z) for q in range(3)
    ) + tuple(
        (56, 11, 10, q, OUTER_Z) for q in range(1, 4)
    )
    assert all(key in safe_key_set for key in section_variation_blocks)
    return {
        "actual_pascal_block_class_counts": tuple(sorted(counts.items())),
        "all_unsafe_actual_pascal_blocks_cancel_identically": True,
        "every_nonzero_actual_pascal_block_has_safe_sink": True,
        "pascal_tail_records_sha256": hashlib.sha256(
            repr(tuple(records)).encode()).hexdigest(),
        "upstream_section_variation_safe_sink_keys": section_variation_blocks,
        "actual_rhs_lies_in_safe_raw_module": True,
    }


def initial_jet_coordinates(all_coordinates, safe):
    """Choose only initial Hasse-jet sets on every physical polynomial.

    The tempting 45-column raw basis used q=1 without q=0 on eleven P56
    polynomials and q=2 without q=0,1 on one of them.  A coefficientwise
    antiderivative does not make those omitted lower jets vanish.  The honest
    repair includes q=0 on every polynomial and moves the extra curvature-cap
    direction to q=1 of P57.  Every physical q-set is now {0} or {0,1}, so an
    ordinary all-node Hermite section realizes it inside the literal window.
    """
    all_by_key = dict(all_coordinates)
    selected_keys = []
    for s in range(11):
        r = ACTIVE - 56 - s
        selected_keys.extend((56, r, s, q, OUTER_Z) for q in (0, 1))
    for y in range(57, 60):
        for s in range(11):
            r = ACTIVE - y - s
            selected_keys.append((y, r, s, 0, OUTER_Z))
    selected_keys.append((57, 10, 10, 1, OUTER_Z))

    assert len(selected_keys) == len(set(selected_keys)) == 56
    assert all(key in all_by_key for key in selected_keys)
    selected = tuple((key, all_by_key[key]) for key in selected_keys)

    physical_qsets = defaultdict(set)
    for y, r, s, q, z in selected_keys:
        physical_qsets[(y, r, s, z)].add(q)
    qset_histogram = Counter(tuple(sorted(qset))
                             for qset in physical_qsets.values())
    assert len(physical_qsets) == 44
    assert qset_histogram == Counter({(0,): 32, (0, 1): 12})

    section_windows = []
    for physical, qset in sorted(physical_qsets.items()):
        y, r, s, _z = physical
        width = H.width(y, r, s)
        needed = len(qset) * N
        section_windows.append((width - needed, physical, tuple(sorted(qset)),
                                width, needed))
    assert min(section_windows) == (
        208_046, (56, 21, 0, OUTER_Z), (0, 1), 732_334, 2 * N)

    # The new selected image contains the entire 45-dimensional strong-
    # capacity module.  Hence it contains every actual tail/variation block,
    # although the 73-row ambient block itself has a 17-dimensional cokernel.
    all_rows = tuple(sorted(
        set().union(*(set(column) for _key, column in all_coordinates)),
        key=lambda row: (row[0] + 3 * row[1], row),
    ))
    selected_rank = modular_rank([
        [column.get(row, 0) for _key, column in selected]
        for row in all_rows
    ])
    safe_union_rank = modular_rank([
        [column.get(row, 0)
         for _key, column in selected + tuple(safe)]
        for row in all_rows
    ])
    all_union_rank = modular_rank([
        [column.get(row, 0)
         for _key, column in selected + tuple(all_coordinates)]
        for row in all_rows
    ])
    assert (selected_rank, safe_union_rank, all_union_rank) == (56, 56, 56)
    return selected, physical_qsets, tuple(section_windows), {
        "selected_coordinates_rank_in_73_rows": (56, 56),
        "physical_polynomial_qset_histogram": tuple(sorted(
            qset_histogram.items())),
        "minimum_section_slack_physical_qset_width_needed": min(
            section_windows),
        "selected_plus_all_99_safe_coordinates_rank": safe_union_rank,
        "selected_plus_all_110_diagonal_coordinates_rank": all_union_rank,
        "entire_safe_rank45_module_is_in_selected_rank56_image": True,
        "every_induced_same_diagonal_jet_is_in_selected_rank56_image": True,
    }


def hopcroft_karp(adjacency, right_count):
    left_count = len(adjacency)
    match_l = [-1] * left_count
    match_r = [-1] * right_count
    distance = [-1] * left_count

    def bfs():
        queue = deque()
        found = False
        for left in range(left_count):
            if match_l[left] < 0:
                distance[left] = 0
                queue.append(left)
            else:
                distance[left] = -1
        while queue:
            left = queue.popleft()
            for right in adjacency[left]:
                other = match_r[right]
                if other < 0:
                    found = True
                elif distance[other] < 0:
                    distance[other] = distance[left] + 1
                    queue.append(other)
        return found

    def dfs(left):
        for right in adjacency[left]:
            other = match_r[right]
            if other < 0 or (
                    distance[other] == distance[left] + 1 and dfs(other)):
                match_l[left] = right
                match_r[right] = left
                return True
        distance[left] = -1
        return False

    while bfs():
        for left in range(left_count):
            if match_l[left] < 0:
                dfs(left)
    return tuple(match_l), tuple(match_r)


def tarjan_scc(adjacency):
    index = 0
    indices = [-1] * len(adjacency)
    low = [0] * len(adjacency)
    stack = []
    on_stack = [False] * len(adjacency)
    components = []

    def visit(vertex):
        nonlocal index
        indices[vertex] = low[vertex] = index
        index += 1
        stack.append(vertex)
        on_stack[vertex] = True
        for successor in adjacency[vertex]:
            if indices[successor] < 0:
                visit(successor)
                low[vertex] = min(low[vertex], low[successor])
            elif on_stack[successor]:
                low[vertex] = min(low[vertex], indices[successor])
        if low[vertex] == indices[vertex]:
            component = []
            while True:
                member = stack.pop()
                on_stack[member] = False
                component.append(member)
                if member == vertex:
                    break
            components.append(tuple(sorted(component)))

    for vertex in range(len(adjacency)):
        if indices[vertex] < 0:
            visit(vertex)
    return tuple(components)


def exact_initial_jet_section_gate(all_rows, selected, physical_qsets,
                                   section_windows):
    """Check the exact 56-column Popov block and all induced higher jets."""
    row_index = {row: i for i, row in enumerate(all_rows)}
    support_adjacency = tuple(tuple(
        row_index[row] for row in column
    ) for _key, column in selected)
    match_l, _match_r = hopcroft_karp(support_adjacency, len(all_rows))
    assert all(index >= 0 for index in match_l)
    pivot_rows = tuple(all_rows[index] for index in match_l)
    pivot_owner = {row: i for i, row in enumerate(pivot_rows)}
    assert len(pivot_owner) == 56

    matrix = [[column.get(pivot_rows[row_owner], 0)
               for _key, column in selected]
              for row_owner in range(56)]
    rank, determinant = modular_rank_and_det(matrix)
    quarter = pow(4, -1, P)
    assert (rank, determinant) == (56, quarter)

    # A {0} or {0,1} all-node Hermite section prescribes exactly its initial
    # jets.  Every strictly higher jet is retained as an arbitrary actual
    # operator of all prescribed inputs of that same physical polynomial.
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
    components = tarjan_scc(graph)
    owner_component = {
        member: component_index
        for component_index, component in enumerate(components)
        for member in component
    }

    histogram = Counter()
    component_keys = []
    for component in components:
        diagonal = [
            [selected[column][1].get(pivot_rows[row_owner], 0)
             for column in component]
            for row_owner in component
        ]
        component_rank, component_det = modular_rank_and_det(diagonal)
        assert component_rank == len(component) and component_det
        histogram[(len(component), component_rank, component_det)] += 1
        component_keys.append(tuple(selected[i][0] for i in component))

    assert Counter(map(len, components)) == Counter({1: 32, 2: 12})
    assert histogram == Counter({
        (1, 1, 1): 32,
        (2, 2, P - 1): 10,
        (2, 2, -INV2 % P): 2,
    })
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

    coordinate_levels = Counter(key[0] + key[3]
                                for key, _column in selected)
    assert coordinate_levels == Counter({56: 11, 57: 22, 58: 12, 59: 11})
    assert min(section_windows)[0] == 208_046
    return {
        "selected_coordinate_count_distinct_physical_polynomials": (56, 44),
        "selected_coordinate_level_y_plus_q_histogram": tuple(sorted(
            coordinate_levels.items())),
        "section_construction": (
            "twelve physical polynomials prescribe initial jets H0,H1 by "
            "ordinary all-node two-jet Hermite interpolation; thirty-two "
            "prescribe H0 by all-node interpolation; all higher jets are "
            "retained as dependency edges"),
        "minimum_section_slack_physical_qset_width_needed": min(
            section_windows),
        "selected_56_by_56_rank_determinant_mod_p": (rank, determinant),
        "expanded_all_node_rank_cokernel_and_determinant": (
            56 * N, 0, f"({quarter})^{N}"),
        "ambient_73_row_type_cokernel": len(all_rows) - rank,
        "matching_key_row_scalar_sha256": hashlib.sha256(repr(tuple(
            (selected[i][0], pivot_rows[i],
             selected[i][1][pivot_rows[i]]) for i in range(56)
        )).encode()).hexdigest(),
        "dependency_scc_size_histogram": tuple(sorted(
            Counter(map(len, components)).items())),
        "scc_size_rank_determinant_histogram": tuple(sorted(histogram.items())),
        "component_physical_keys_sha256": hashlib.sha256(
            repr(tuple(component_keys)).encode()).hexdigest(),
        "induced_higher_jet_edge_count": len(induced_edges),
        "no_induced_higher_jet_edge_inside_an_scc": True,
        "all_induced_higher_jet_edges_strictly_increase_contact_weight": True,
        "all_dependency_edges_non_decreasing_in_contact_weight": True,
    }


def outgoing_filtration_gate(selected, all_rows):
    # The 56 coordinates occupy 44 physical polynomials.  Every physical
    # q-set now begins at q=0, so there is no silently omitted lower jet.
    physical_qmin = {}
    for key, _column in selected:
        y, r, s, q, z = key
        physical_qmin[(y, r, s, z)] = min(
            q, physical_qmin.get((y, r, s, z), q))
    assert len(physical_qmin) == 44

    counts = Counter()
    same_rows = set()
    per_y = Counter()
    for (y, r, s, z), q_min in sorted(physical_qmin.items()):
        source_order = (z, J - (y + r + s))
        for f in range(y + 1):
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    q_count = max(0, M - (f + 2 * a_e + c_s) - q_min)
                    if not q_count:
                        continue
                    if f == y:
                        counts["same_filtration_full_contact"] += q_count
                        per_y[(y, "full")] += q_count
                        for q in range(q_min, q_min + q_count):
                            same_rows.add(C.row_of(
                                r, s, z, f, 0, a_e, c_s, q))
                    else:
                        assert (z, J - (f + r + s)) > source_order
                        assert (z + y - f, J - (f + r + s)) > source_order
                        counts["strictly_later_u0free"] += q_count
                        counts["strictly_later_positive_u0"] += (
                            (y - f) * q_count)
                        per_y[(y, "u0free")] += q_count
                        per_y[(y, "u0positive")] += (y - f) * q_count
    assert len(same_rows) == 73
    assert counts == Counter({
        "same_filtration_full_contact": 264,
        "strictly_later_u0free": 4_803_260,
        "strictly_later_positive_u0": 172_449_684,
    })
    assert len(same_rows) == 73
    assert same_rows == set(all_rows)
    return {
        "common_order": "lexicographic (outer Z, J-active degree)",
        "physical_section_polynomial_count": len(physical_qmin),
        "same_filtration_distinct_rows": len(same_rows),
        "occurrence_counts": tuple(sorted(counts.items())),
        "per_source_y_occurrence_counts": tuple(sorted(per_y.items())),
        "all_nonfull_contact_outputs_strictly_advance_common_order": True,
    }


def main():
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(HERE / filename) == expected
    all_coordinates, safe, unsafe = all_diagonal_coordinates()
    safe_rows, duals, raw_module = safe_raw_module(safe)
    all_rows, all_provenance = entire_same_key_provenance(all_coordinates)
    initial_rows, source_receipts = first_positive_frontier_rows()
    provenance, block_keys, provenance_sha = exact_top_source_provenance(
        initial_rows)
    safe_key_set = {key for key, _column in safe}
    actual_membership = actual_tail_membership(block_keys, safe_key_set)
    selected, physical_qsets, section_windows, selected_receipt = (
        initial_jet_coordinates(all_coordinates, safe))
    section = exact_initial_jet_section_gate(
        all_rows, selected, physical_qsets, section_windows)
    outgoing = outgoing_filtration_gate(selected, all_rows)

    assert set(initial_rows) <= set(safe_rows)
    assert modular_rank([
        [column.get(row, 0) for _key, column in selected]
        for row in all_rows
    ]) == 56
    assert all(dot(dual, column) == 0
               for dual in duals for _key, column in safe)

    stable = {
        "scope": (
            "earliest positive-u0/same-Z grade after b86d33b: initial seven "
            "rows plus the complete source-legal (outerZ,active)=(2625,77) "
            "diagonal forced by its curvature sections; later grades open"),
        "target_p_N_G_errors_M_J_outerZ_active": (
            P, N, G, ERRORS, M, J, OUTER_Z, ACTIVE),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "initial_frontier_source_receipts": source_receipts,
        "initial_seven_row_provenance": provenance,
        "initial_114_origin_signatures_sha256": provenance_sha,
        "all_diagonal_coordinate_census": {
            "all_safe_unsafe": (
                len(all_coordinates), len(safe), len(unsafe)),
            "unsafe_keys": tuple(key for key, _column in unsafe),
        },
        "complete_73_row_same_key_provenance": all_provenance,
        "safe_raw_contact_module": raw_module,
        "two_safe_cokernel_dual_evaluations_on_actual_rhs": (0, 0),
        "actual_pascal_and_upstream_section_membership": actual_membership,
        "selected_image_contains_actual_rhs": selected_receipt,
        "legal_initial_jet_curvature_staircase_section": section,
        "outgoing_filtration": outgoing,
        "decision": "GREEN_EARLIEST_POSITIVE_U0_INITIAL_JET_POPOV_BLOCK",
        "rejected_process": (
            "Do not use the earlier 45-column isolated-q section: a q-fold "
            "coefficientwise Hasse antiderivative does not make its lower "
            "Hasse jets vanish at the N nodes. The repair includes q=0 and "
            "uses only initial q-sets {0} or {0,1}."),
        "scope_guard": (
            "The ambient 73-row module has rank 56 and cokernel 17, but all "
            "880 original origins sink in its 110 raw coordinates and the "
            "selected columns span all 110. The initially forced post-Pascal "
            "RHS lies in the smaller safe rank-45 module: its old two duals "
            "both evaluate to zero and every unsafe block present cancels. "
            "This does not close the 4,803,260 later u0-free or 172,449,684 "
            "later positive-u0 occurrences emitted by the 44 sections, one "
            "full passive band, F3 containment, or a 6900 candidate."),
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
