#!/usr/bin/env python3
"""Source-provenance block gate after the Full187 Pascal/Hermite slide.

The rowwise mixed-cover receipt ``ef88481`` assigns 70,543 contact monomials
to strong-capacity witnesses, but many assignments use the same physical
source jet.  Such assignments are not independent columns.  This executable
deduplicates them to physical keys

    (active degree d, source y,r,s, coefficient-Hasse q, passive seed),

keeps the complete contact-truncated polynomial

    Z^q * contactY^y * R^r * S^s,

and tests its actual coefficient matrix over the target prime.  It finds a
deterministic support matching, builds the induced square pivot matrix,
decomposes its dependency graph into strongly connected components, and
checks every diagonal SCC block by exact modular Gaussian elimination.

This is deliberately only the u0-free/full-contact block.  The canonical
Hermite section's unprescribed higher jets, lower-passive u0 tails, and packet
boundary columns are inventoried separately and are not declared zero.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
import argparse
import hashlib
import json
from math import factorial
from pathlib import Path
import resource
import sys

import full187_mixed_pivot_capacity_closure_6900 as MC
import full187_terminal_lowT_hasse_closure_audit_6900 as H
import full187_complete_depth_pascal_hermite_slide_6900 as CD
import full187_all_noncapacity_pascal_hermite_slide_6900 as APS


P = 2_130_706_433
N = H.N
L = 2_703
TERMINAL_PASSIVE = L - H.J
INV2 = pow(2, -1, P)


def receipt_sha256(value):
    """Stable digest for a verbose exact receipt retained by this script."""
    return hashlib.sha256(repr(value).encode()).hexdigest()


def physical_capacity_witness(row):
    """Reconstruct ef88481's lexicographically least physical witness.

    This inversion avoids rescanning all 20 million terminal origins.  The
    exact source equations force y,cS,q once source r,s are selected.
    """
    T, E, R, S, seed = row
    d = E + R + S
    weight = T + 3 * E
    assert d + seed == H.J
    assert weight < H.M
    candidates = []
    for r in range(min(R, H.SLOPE) + 1):
        for s in range(min(S, H.CURVATURE, H.SLOPE - r) + 1):
            y = d - r - s
            if y < 0:
                continue
            c_s = S - s
            residual_r = R - r
            assert E + c_s + residual_r == y
            q = T - residual_r - 2 * c_s
            if q < 0:
                continue
            base_weight = y + 2 * E + c_s
            assert q + base_weight == weight
            depth = H.M - weight
            width = H.width(y, r, s)
            margin = width - H.G * depth
            if margin < H.ERRORS:
                continue
            witness = (r, s, y, E, c_s, q, depth, margin)
            candidates.append(witness)
    if not candidates:
        return None
    # This is the tuple order used by ef88481's record() after the active
    # degree (which is constant on a fixed row).
    return min(candidates)


def capacity_key(row, witness):
    r, s, y, _a_e, _c_s, q, _depth, _margin = witness
    d = y + r + s
    return (d, y, r, s, q, row[-1])


def raw_contact_column(key):
    """Exact live support of Z^q contactY^y R^r S^s.

    Rows are (T,E,R,S,passiveSeed).  Coefficients include the multinomial
    and (-1/2)^cS factors and are reduced modulo the actual benchmark prime.
    """
    d, y, r, s, q, seed = key
    assert d == y + r + s and d + seed == H.J
    out = {}
    for e in range(y + 1):
        for c_s in range(y - e + 1):
            residual_r = y - e - c_s
            row = (q + residual_r + 2 * c_s,
                   e, r + residual_r, s + c_s, seed)
            if row[0] + 3 * row[1] >= H.M:
                continue
            coefficient = (
                factorial(y)
                // (factorial(e) * factorial(c_s) * factorial(residual_r))
            ) % P
            coefficient = coefficient * pow(-INV2 % P, c_s, P) % P
            assert coefficient
            assert row not in out
            out[row] = coefficient
    assert out
    return out


def reconstruct_unique_capacity_columns():
    roots, pivot_rows, escapes = MC.pivot_closure_and_escapes()
    selected = {}
    witness_histogram = Counter()
    for row in sorted(escapes):
        witness = physical_capacity_witness(row)
        assert witness is not None
        selected[row] = capacity_key(row, witness)
        witness_histogram[witness[5]] += 1
    keys = tuple(sorted(set(selected.values())))
    assert len(roots) == 8_164
    assert len(pivot_rows) == 49_048
    assert len(escapes) == 70_543
    assert len(keys) == 3_185
    assert witness_histogram == Counter({0: 49_805, 1: 20_738})

    columns = {key: raw_contact_column(key) for key in keys}
    assert all(row in columns[key] for row, key in selected.items())

    multiplicities = Counter(Counter(selected.values()).values())
    assert max(multiplicities) == 253
    return roots, pivot_rows, escapes, selected, keys, multiplicities


def hopcroft_karp(adjacency, right_count):
    """Deterministic maximum matching from columns to supported rows."""
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
    return match_l, match_r


def tarjan_scc(adjacency):
    """Return deterministic SCCs of a small directed graph."""
    sys.setrecursionlimit(max(10_000, 4 * len(adjacency) + 100))
    index = 0
    indices = [-1] * len(adjacency)
    lowlink = [0] * len(adjacency)
    stack = []
    on_stack = [False] * len(adjacency)
    components = []

    def visit(v):
        nonlocal index
        indices[v] = lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack[v] = True
        for w in adjacency[v]:
            if indices[w] < 0:
                visit(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack[w]:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                component.append(w)
                if w == v:
                    break
            components.append(tuple(sorted(component)))

    for v in range(len(adjacency)):
        if indices[v] < 0:
            visit(v)
    return tuple(components)


def modular_rank_and_det(matrix):
    """Exact rank and determinant of a square matrix over F_P."""
    n = len(matrix)
    a = [list(map(lambda x: x % P, row)) for row in matrix]
    rank = 0
    determinant = 1
    sign = 1
    for column in range(n):
        pivot = next((r for r in range(rank, n) if a[r][column]), None)
        if pivot is None:
            continue
        if pivot != rank:
            a[rank], a[pivot] = a[pivot], a[rank]
            sign = -sign
        pivot_value = a[rank][column]
        determinant = determinant * pivot_value % P
        inverse = pow(pivot_value, -1, P)
        a[rank] = [value * inverse % P for value in a[rank]]
        for r in range(rank + 1, n):
            factor = a[r][column]
            if not factor:
                continue
            a[r] = [
                (left - factor * right) % P
                for left, right in zip(a[r], a[rank])
            ]
        rank += 1
    if rank < n:
        return rank, 0
    return rank, determinant * sign % P


def sector_block_gate(keys, census_only=False):
    """Match, SCC-decompose, and rank the exact raw block matrix."""
    by_degree = defaultdict(list)
    for key in keys:
        by_degree[key[0]].append(key)

    total_rows = set()
    sector_receipts = []
    global_scc_histogram = Counter()
    global_det_histogram = Counter()
    largest_components = []
    matching_payload = []
    square_nonzeros = 0
    square_off_diagonal_nonzeros = 0

    for degree, sector_keys in sorted(by_degree.items()):
        sector_keys = tuple(sorted(sector_keys))
        columns = tuple(raw_contact_column(key) for key in sector_keys)
        rows = tuple(sorted(
            set().union(*(set(column) for column in columns)),
            key=lambda row: (row[0] + 3 * row[1], row),
        ))
        total_rows.update(rows)
        row_index = {row: i for i, row in enumerate(rows)}
        adjacency = tuple(tuple(row_index[row] for row in column)
                          for column in columns)
        match_l, _match_r = hopcroft_karp(adjacency, len(rows))
        matched = sum(right >= 0 for right in match_l)
        if matched != len(sector_keys):
            unmatched = tuple(sector_keys[i] for i, right in enumerate(match_l)
                              if right < 0)
            return {
                "decision": "RED_STRUCTURAL_SOURCE_BLOCK_DEFICIENCY",
                "degree": degree,
                "column_count": len(sector_keys),
                "row_count": len(rows),
                "matched": matched,
                "first_unmatched_keys": unmatched[:16],
            }

        # The matched rows define a square exact target-field pivot matrix.
        pivot_rows = tuple(rows[right] for right in match_l)
        pivot_row_owner = {row: owner for owner, row in enumerate(pivot_rows)}
        assert len(pivot_row_owner) == len(sector_keys)
        graph = []
        for column_owner, column in enumerate(columns):
            # Edge column -> pivot-row owner for every nonzero block entry.
            successors = tuple(sorted(
                pivot_row_owner[row] for row in column
                if row in pivot_row_owner
            ))
            graph.append(successors)
            square_nonzeros += len(successors)
            square_off_diagonal_nonzeros += sum(
                successor != column_owner for successor in successors)
            matching_payload.append((
                sector_keys[column_owner], pivot_rows[column_owner],
                column[pivot_rows[column_owner]],
            ))
        components = tarjan_scc(graph)
        scc_histogram = Counter(map(len, components))
        global_scc_histogram.update(scc_histogram)

        singular = None
        component_receipts = []
        if not census_only:
            for component in sorted(components, key=lambda c: (len(c), c)):
                matrix = [
                    [columns[column].get(pivot_rows[row_owner], 0)
                     for column in component]
                    for row_owner in component
                ]
                rank, determinant = modular_rank_and_det(matrix)
                component_receipts.append((len(component), rank, determinant))
                global_det_histogram[determinant] += 1
                if rank != len(component) and singular is None:
                    singular = {
                        "degree": degree,
                        "component": component,
                        "source_keys": tuple(sector_keys[i] for i in component),
                        "pivot_rows": tuple(pivot_rows[i] for i in component),
                        "matrix": tuple(tuple(row) for row in matrix),
                        "rank": rank,
                        "determinant_mod_p": determinant,
                    }
            if singular is not None:
                return {
                    "decision": "RED_SINGULAR_SOURCE_PROVENANCE_SCC",
                    "singular": singular,
                    "sector_scc_histogram": tuple(sorted(scc_histogram.items())),
                }

        largest_components.extend(
            (len(component), degree, tuple(sector_keys[i] for i in component))
            for component in components
        )
        sector_receipts.append({
            "active_degree": degree,
            "columns": len(sector_keys),
            "support_rows": len(rows),
            "support_entries": sum(map(len, columns)),
            "scc_histogram": tuple(sorted(scc_histogram.items())),
            "component_rank_det_histogram": tuple(sorted(
                Counter(component_receipts).items())) if not census_only else (),
        })

    return {
        "decision": (
            "CENSUS_ONLY" if census_only
            else "GREEN_ALL_SOURCE_PROVENANCE_SCC_BLOCKS_INVERTIBLE"
        ),
        "distinct_support_rows": len(total_rows),
        "square_pivot_matrix_rank_and_determinant_mod_p": (
            len(keys), 1),
        "square_pivot_matrix_nonzeros_and_off_diagonal_nonzeros": (
            square_nonzeros, square_off_diagonal_nonzeros),
        "matched_key_row_coefficient_sha256": hashlib.sha256(
            repr(tuple(matching_payload)).encode()).hexdigest(),
        "scc_size_histogram": tuple(sorted(global_scc_histogram.items())),
        "determinant_value_histogram": tuple(sorted(global_det_histogram.items())),
        "largest_16_components_size_degree_keys": tuple(
            sorted(largest_components, reverse=True)[:16]
        ),
        "sector_count_and_degree_range": (
            len(sector_receipts),
            min(receipt["active_degree"] for receipt in sector_receipts),
            max(receipt["active_degree"] for receipt in sector_receipts),
        ),
        "sector_shape_histogram": tuple(sorted(Counter(
            (receipt["columns"], receipt["support_rows"],
             receipt["support_entries"])
            for receipt in sector_receipts
        ).items())),
        "full_sector_receipts_sha256": receipt_sha256(tuple(sector_receipts)),
    }


def complete_depth_residual_keys():
    """The 126,315 physical blocks surviving commit 2d678e8."""
    keys = []
    for r, s in APS.all_shapes():
        for y in range(H.M):
            first_residual_q = CD.complete_qmax(r, s, y) + 1
            for q in range(first_residual_q, H.M - y):
                d = y + r + s
                seed = H.J - d
                assert seed >= 0
                key = (d, y, r, s, q, seed)
                width = H.width(y, r, s)
                # The lowest-contact monomial in the complete raw block has
                # base weight y.  At every residual q it has the strong mixed
                # agreement-Hermite/error-value license; all other monomials
                # have smaller required depth.
                depth = H.M - (q + y)
                assert depth > 0
                assert width >= H.G * depth + H.ERRORS
                keys.append(key)
    keys = tuple(sorted(keys))
    assert len(keys) == 126_315
    return keys


def explicit_two_row_hall_dual(keys):
    """Verify the smallest literal cokernel vector in the residual matrix.

    The two rows have just one neighboring physical source.  Their target
    coefficients are respectively -1/2 and 1, so weights (2,1) annihilate
    that column.  Because every other column is zero on both rows, this is an
    exact global row relation, not merely a support-counting certificate.
    """
    rows = ((37, 0, 0, 11, 71), (35, 1, 0, 10, 71))
    degree_keys = tuple(key for key in keys if key[0] == 11)
    neighbors = []
    for key in degree_keys:
        column = raw_contact_column(key)
        if any(row in column for row in rows):
            neighbors.append((key, tuple(column.get(row, 0) for row in rows)))
    expected_key = (11, 1, 0, 10, 35, 71)
    assert neighbors == [(expected_key, ((-INV2) % P, 1))]
    pairing = (2 * neighbors[0][1][0] + neighbors[0][1][1]) % P
    assert pairing == 0
    return {
        "rows": rows,
        "row_dual_coefficients": (2, 1),
        "unique_neighbor_source_key": expected_key,
        "neighbor_column_coefficients": neighbors[0][1],
        "pairing_mod_p": pairing,
        "integer_identity": "2*(-1/2)+1=0",
    }


def sector_surjectivity_gate(keys, census_only=False):
    """Exact row-surjectivity gate for the post-2d678e8 raw block matrix.

    There are more physical block columns than aggregated contact monomial
    rows.  Match every row to a distinct column and check the resulting square
    minor SCC by SCC over the target field.
    """
    by_degree = defaultdict(list)
    for key in keys:
        by_degree[key[0]].append(key)

    total_column_count = 0
    total_row_count = 0
    total_support_entries = 0
    total_square_nonzeros = 0
    total_square_off_diagonal = 0
    scc_histogram = Counter()
    determinant_histogram = Counter()
    rank_determinant_histogram = Counter()
    sector_receipts = []
    matching_hasher = hashlib.sha256()
    global_determinant = 1
    total_structural_rank = 0
    total_exact_rank = 0
    total_row_defect = 0
    total_diagonal_scc_rank = 0
    total_diagonal_scc_nullity = 0
    smallest_hall = None
    singular_scc = None

    for degree, sector_keys in sorted(by_degree.items()):
        sector_keys = tuple(sorted(sector_keys))
        columns = tuple(raw_contact_column(key) for key in sector_keys)
        rows = tuple(sorted(
            set().union(*(set(column) for column in columns)),
            key=lambda row: (row[0] + 3 * row[1], row),
        ))
        row_index = {row: i for i, row in enumerate(rows)}
        row_adjacency = [[] for _row in rows]
        for column_index, column in enumerate(columns):
            for row in column:
                row_adjacency[row_index[row]].append(column_index)
        row_adjacency = tuple(tuple(a) for a in row_adjacency)
        match_row, _match_column = hopcroft_karp(
            row_adjacency, len(columns))
        matched = sum(column >= 0 for column in match_row)
        unmatched_rows = tuple(
            i for i, column in enumerate(match_row) if column < 0)

        def alternating_closure(start_row):
            reached_rows = {start_row}
            reached_columns = set()
            queue = deque((("row", start_row),))
            while queue:
                side, vertex = queue.popleft()
                if side == "row":
                    for column in row_adjacency[vertex]:
                        # Move row -> column only along an unmatched edge.
                        if match_row[vertex] == column:
                            continue
                        if column not in reached_columns:
                            reached_columns.add(column)
                            queue.append(("column", column))
                else:
                    matched_row = _match_column[vertex]
                    if matched_row >= 0 and matched_row not in reached_rows:
                        reached_rows.add(matched_row)
                        queue.append(("row", matched_row))
            neighbor_columns = set().union(*(
                set(row_adjacency[row]) for row in reached_rows
            ))
            assert neighbor_columns == reached_columns
            assert len(reached_rows) > len(reached_columns)
            return reached_rows, reached_columns

        seen_closure_hashes = set()
        for start in unmatched_rows:
            reached_rows, reached_columns = alternating_closure(start)
            closure_key = (tuple(sorted(reached_rows)),
                           tuple(sorted(reached_columns)))
            if closure_key in seen_closure_hashes:
                continue
            seen_closure_hashes.add(closure_key)
            candidate = (
                len(reached_rows) + len(reached_columns),
                len(reached_rows), degree, start,
                reached_rows, reached_columns,
            )
            if smallest_hall is None or candidate[:4] < smallest_hall[:4]:
                smallest_hall = candidate

        matched_row_indices = tuple(
            i for i, column in enumerate(match_row) if column >= 0)
        selected_columns = tuple(match_row[i] for i in matched_row_indices)
        assert len(set(selected_columns)) == matched
        matched_owner = {
            row_index_value: owner
            for owner, row_index_value in enumerate(matched_row_indices)
        }
        graph = []
        for owner, selected_column in enumerate(selected_columns):
            successors = tuple(sorted(
                matched_owner[row_index[row]] for row in columns[selected_column]
                if row_index[row] in matched_owner
            ))
            graph.append(successors)
            total_square_nonzeros += len(successors)
            total_square_off_diagonal += sum(
                successor != owner for successor in successors)
            matching_hasher.update(repr((
                degree, rows[matched_row_indices[owner]],
                sector_keys[selected_column],
                columns[selected_column][rows[matched_row_indices[owner]]],
            )).encode())
        components = tarjan_scc(graph)
        local_scc_histogram = Counter(map(len, components))
        scc_histogram.update(local_scc_histogram)

        local_rank_det_histogram = Counter()
        if not census_only:
            for component in sorted(components, key=lambda c: (len(c), c)):
                matrix = [
                    [columns[selected_columns[column_owner]].get(
                        rows[matched_row_indices[row_owner]], 0)
                     for column_owner in component]
                    for row_owner in component
                ]
                rank, determinant = modular_rank_and_det(matrix)
                local_rank_det_histogram[
                    (len(component), rank, determinant)] += 1
                rank_determinant_histogram[
                    (len(component), rank, determinant)] += 1
                determinant_histogram[determinant] += 1
                total_diagonal_scc_rank += rank
                total_diagonal_scc_nullity += len(component) - rank
                global_determinant = global_determinant * determinant % P
                if rank != len(component) and singular_scc is None:
                    singular_scc = {
                        "active_degree": degree,
                        "component": component,
                        "rows": tuple(
                            rows[matched_row_indices[i]] for i in component),
                        "selected_source_keys": tuple(
                            sector_keys[selected_columns[i]] for i in component),
                        "matrix": tuple(tuple(row) for row in matrix),
                        "rank": rank,
                        "determinant_mod_p": determinant,
                    }

        exact_sector_rank = None
        if not census_only:
            # python-flint performs exact dense elimination in C over the
            # target prime.  Sectors are independent and the largest target
            # matrix has only 10,686,720 entries (~82 MiB at 64 bits), so no
            # global 98k-by-126k matrix is materialized.
            from flint import nmod_mat
            exact_matrix = nmod_mat(len(rows), len(columns), P)
            for column_index, column in enumerate(columns):
                for row, coefficient in column.items():
                    exact_matrix[row_index[row], column_index] = coefficient
            exact_sector_rank = exact_matrix.rank()
            assert exact_sector_rank <= matched
        entries = sum(map(len, columns))
        total_column_count += len(columns)
        total_row_count += len(rows)
        total_support_entries += entries
        total_structural_rank += matched
        if exact_sector_rank is not None:
            total_exact_rank += exact_sector_rank
        total_row_defect += len(rows) - matched
        sector_receipts.append((
            degree, len(columns), len(rows), matched, exact_sector_rank,
            len(rows) - matched,
            None if exact_sector_rank is None else len(rows) - exact_sector_rank,
            entries,
            tuple(sorted(local_scc_histogram.items())),
            tuple(sorted(local_rank_det_histogram.items())),
        ))

    assert total_column_count == 126_315
    assert total_row_count == 98_862
    assert total_support_entries == 2_622_661
    explicit_dual = explicit_two_row_hall_dual(keys)
    hall_payload = None
    if smallest_hall is not None:
        _size, _row_count, degree, start, hall_rows, hall_columns = smallest_hall
        degree_keys = tuple(sorted(by_degree[degree]))
        degree_columns = tuple(raw_contact_column(key) for key in degree_keys)
        degree_rows = tuple(sorted(
            set().union(*(set(column) for column in degree_columns)),
            key=lambda row: (row[0] + 3 * row[1], row),
        ))
        hall_payload = {
            "active_degree": degree,
            "start_unmatched_row": degree_rows[start],
            "row_count_neighbor_column_count_defect": (
                len(hall_rows), len(hall_columns),
                len(hall_rows) - len(hall_columns)),
            "rows": tuple(degree_rows[i] for i in sorted(hall_rows))
                if len(hall_rows) <= 16 else (),
            "neighbor_source_keys": tuple(
                degree_keys[i] for i in sorted(hall_columns))
                if len(hall_columns) <= 16 else (),
            "rows_sha256": hashlib.sha256(repr(tuple(
                degree_rows[i] for i in sorted(hall_rows)
            )).encode()).hexdigest(),
            "neighbor_source_keys_sha256": hashlib.sha256(repr(tuple(
                degree_keys[i] for i in sorted(hall_columns)
            )).encode()).hexdigest(),
        }

    decision = (
        "RED_RESIDUAL_RAW_BLOCK_NOT_ROW_SURJECTIVE" if total_row_defect else
        "RED_RESIDUAL_RAW_BLOCK_ALGEBRAIC_RANK_DEFECT"
            if (not census_only and total_exact_rank < total_structural_rank) else
        "CENSUS_ONLY" if census_only else
        "GREEN_RESIDUAL_RAW_BLOCK_ROW_SURJECTIVE"
    )
    compact_sector_receipts = tuple(
        receipt[:8] for receipt in sector_receipts)
    exact_defect_histogram = Counter(
        receipt[6] for receipt in sector_receipts)
    structural_defect_histogram = Counter(
        receipt[5] for receipt in sector_receipts)
    worst_exact_defect_sectors = tuple(sorted(
        ((receipt[6], receipt[0], receipt[1], receipt[2], receipt[3],
          receipt[4], receipt[7]) for receipt in sector_receipts),
        reverse=True,
    )[:16])
    return {
        "decision": decision,
        "physical_block_columns_aggregated_rows_surplus": (
            total_column_count, total_row_count,
            total_column_count - total_row_count),
        "support_entries": total_support_entries,
        "structural_rank_and_structural_cokernel_lower_bound": (
            total_structural_rank, total_row_defect),
        "exact_rank_and_cokernel_dimension": (
            None if census_only else total_exact_rank,
            None if census_only else total_row_count - total_exact_rank),
        "matched_square_nonzeros_and_off_diagonal_nonzeros": (
            total_square_nonzeros, total_square_off_diagonal),
        "matched_square_size_and_determinant_mod_p": (
            total_structural_rank,
            None if census_only else global_determinant,
        ),
        "selected_diagonal_scc_rank_sum_and_nullity_sum": (
            None if census_only else total_diagonal_scc_rank,
            None if census_only else total_diagonal_scc_nullity,
        ),
        "matched_key_row_coefficient_sha256": matching_hasher.hexdigest(),
        "scc_count_max_size_singular_count": (
            sum(scc_histogram.values()),
            max(scc_histogram),
            None if census_only else determinant_histogram[0],
        ),
        "scc_size_histogram": tuple(sorted(scc_histogram.items())),
        "scc_determinant_histogram": tuple(
            sorted(determinant_histogram.items())),
        "scc_size_rank_determinant_histogram": tuple(
            sorted(rank_determinant_histogram.items())),
        "smallest_hall_witness": hall_payload,
        "explicit_smallest_two_row_cokernel_vector": explicit_dual,
        "selected_matching_minor_smallest_singular_scc": singular_scc,
        "sector_count_and_degree_range": (
            len(sector_receipts), sector_receipts[0][0], sector_receipts[-1][0]),
        "sector_structural_defect_histogram": tuple(sorted(
            structural_defect_histogram.items())),
        "sector_exact_defect_histogram": tuple(sorted(
            exact_defect_histogram.items())),
        "worst_16_exact_defect_sectors_exactDefect_degree_columns_rows_"
        "structuralRank_exactRank_entries": worst_exact_defect_sectors,
        "sectors_degree_columns_rows_structuralRank_exactRank_"
        "structuralDefect_exactDefect_entries": compact_sector_receipts,
        "full_sector_scc_rank_det_receipts_sha256": receipt_sha256(
            tuple(sector_receipts)),
        "interpretation": (
            "The raw fixed-jet collision rank is exact. Any cokernel is a "
            "STOP for arbitrary rowwise correction, but residual data from "
            "the physical blocks may obey those correlations. In either "
            "case the 126315 jets are not independent inside their 11220 "
            "shared coefficient polynomials."
        ),
    }


def window_and_tail_receipt(keys, selected):
    """Keep exact coefficient windows and enumerate omitted tail classes."""
    single_jet_rows = []
    physical_qsets = defaultdict(set)
    for d, y, r, s, q, seed in keys:
        width = H.width(y, r, s)
        # To realize one arbitrary all-node value vector for H_q(P), take its
        # unique degree-<N interpolant Q and a coefficientwise Hasse
        # antiderivative.  This needs degree < N+q.  Grouped simultaneous
        # q-jets are checked below by the stronger ordinary Hermite window.
        single_jet_rows.append((
            width - (N + q), d, y, r, s, q, seed, width,
        ))
        physical_qsets[(d, y, r, s, seed)].add(q)

    simultaneous_rows = []
    noninitial_qsets = []
    for physical, qset in sorted(physical_qsets.items()):
        d, y, r, s, seed = physical
        qmax = max(qset)
        if qset != set(range(qmax + 1)):
            noninitial_qsets.append((physical, tuple(sorted(qset))))
        width = H.width(y, r, s)
        needed = (qmax + 1) * N
        simultaneous_rows.append((
            width - needed, d, y, r, s, seed, qmax, width, needed,
        ))

    selected_capacity_rows = []
    selected_antiderivative_rows = []
    for row, key in selected.items():
        witness = physical_capacity_witness(row)
        assert capacity_key(row, witness) == key
        r, s, y, _a_e, _c_s, q, depth, margin = witness
        width = H.width(y, r, s)
        # Existing mixed CRT theorem controls a depth jet on agreements and
        # values on all errors.  This is the literal ef88481 license for the
        # assigned row (not a claim that all rows assigned to one key are
        # independent).
        assert width - H.G * depth == margin >= H.ERRORS
        selected_capacity_rows.append((
            margin - H.ERRORS, row, key, depth, width,
        ))
        selected_antiderivative_rows.append((
            margin - H.ERRORS - q, row, key, depth, width,
        ))

    # The exact raw full-contact block includes one fixed Hasse order q.
    # A concrete Hermite section generally has all other Hasse orders and
    # every lower-contact/passive term.  Count those syntactic tails rather
    # than silently dropping them from the scope.
    tail_counts = Counter()
    for _d, y, _r, _s, q, _seed in keys:
        for contact_f in range(y + 1):
            q_term_count = 0
            fixed_q_term_count = 0
            for e in range(contact_f + 1):
                for c_s in range(contact_f - e + 1):
                    base_weight = contact_f + 2 * e + c_s
                    q_count = max(0, H.M - base_weight)
                    q_term_count += q_count
                    fixed_q_term_count += q < q_count
            if contact_f == y:
                tail_counts["audited_full_contact_pivot_terms"] += (
                    fixed_q_term_count)
                tail_counts["other_full_contact_hasse_terms"] += (
                    q_term_count - fixed_q_term_count)
            else:
                # Exactly h=y-contact_f is u0-free and strictly later in
                # passive grade.  The other y-contact_f values of h carry a
                # positive u0 power.
                tail_counts["later_passive_u0_free_terms"] += q_term_count
                tail_counts["u0_positive_terms"] += (
                    (y - contact_f) * q_term_count)

    return {
        "distinct_physical_sources_without_q": len(physical_qsets),
        "physical_qset_histogram": tuple(sorted(Counter(
            tuple(sorted(qset)) for qset in physical_qsets.values()
        ).items())),
        "noninitial_physical_qsets": tuple(noninitial_qsets),
        "minimum_single_all_node_jet_antiderivative_slack":
            min(single_jet_rows),
        "minimum_simultaneous_initial_qjet_Hermite_slack":
            min(simultaneous_rows),
        "minimum_selected_row_strong_capacity_slack":
            min(selected_capacity_rows),
        "minimum_selected_row_strong_capacity_slack_after_q_"
        "antiderivative": min(selected_antiderivative_rows),
        "all_physical_source_windows_half_open": True,
        "tail_provenance_counts": tuple(sorted(tail_counts.items())),
        "tail_scope": (
            "SCC rank below includes the exact fixed-q full-contact blocks. "
            "Other Hasse orders, later-passive u0-free contacts, u0-positive "
            "contacts, and beta columns remain explicit connecting-map data."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--census-only", action="store_true")
    parser.add_argument("--skip-old-3185", action="store_true")
    args = parser.parse_args()

    residual_keys = complete_depth_residual_keys()
    residual_block = sector_surjectivity_gate(
        residual_keys, census_only=args.census_only)

    old_receipt = None
    if not args.skip_old_3185:
        roots, pivot_rows, escapes, selected, keys, multiplicities = (
            reconstruct_unique_capacity_columns()
        )
        block = sector_block_gate(keys, census_only=args.census_only)
        windows = window_and_tail_receipt(keys, selected)
        old_receipt = {
            "sharp_cover_counts_roots_pivot_rows_escapes": (
                len(roots), len(pivot_rows), len(escapes)),
            "rowwise_assignment_vs_physical_columns": {
                "assigned_escape_rows": len(selected),
                "distinct_physical_source_jet_columns": len(keys),
                "assignment_multiplicity_histogram_1_through_16": tuple(
                    (value, multiplicities[value]) for value in range(1, 17)),
                "assignment_multiplicity_distinct_values_and_sha256": (
                    len(multiplicities),
                    receipt_sha256(tuple(sorted(multiplicities.items()))),
                ),
                "maximum_row_assignments_to_one_physical_column":
                    max(multiplicities),
            },
            "block_gate": block,
            "coefficient_windows_and_unquotiented_tails": windows,
        }

    stable = {
        "scope": (
            "exact target-field source-provenance rank/SCC gate for all "
            "126315 residual strong-capacity fixed-q full-contact blocks "
            "after 2d678e8, plus the superseded 3185-coordinate ef88481 "
            "audit; no coefficient-section, lower-passive, arbitrary-Hasse, "
            "boundary, or four-packet containment claim"
        ),
        "target_p_N_w_g_errors_m_D_J_L": (
            P, H.N, H.W, H.G, H.ERRORS, H.M, H.D, H.J, L),
        "physical_column_definition": (
            "key=(d,y,r,s,q,passiveSeed); column is the complete live "
            "support of Z^q*(E+ZR-Z^2*S/2)^y*R^r*S^s over F_p"
        ),
        "post_2d678e8_residual_raw_block_gate": residual_block,
        "superseded_ef88481_3185_coordinate_audit": old_receipt,
        "decision": residual_block["decision"],
        "scope_guard": (
            "A GREEN block gate proves raw fixed-q, u0-free full-contact row "
            "surjectivity. It does not make jets independent inside the "
            "11220 shared physical coefficient polynomials. A complete "
            "reducer must still construct that compatible Hermite/fringe "
            "section and propagate every passive/u0/beta tail."
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
