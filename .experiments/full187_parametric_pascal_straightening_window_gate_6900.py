#!/usr/bin/env python3
"""Symbolic Full187 contact straightening and literal-window obstruction.

This is the correction to the all-A conjecture in commit 79637e2.  It does
not enumerate another large contact matrix.  Instead it decomposes every raw
column into one-variable Pascal blocks indexed by (A,n,h), proves their exact
rank and a unit Vandermonde minor, and tests arbitrary initial-prefix depth
functions by a closed cardinality criterion.
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

import full187_active75_parametric_initial_jet_staircase_gate_6900 as B
import full187_cross_slope_second_fringe_confluence_6900 as C
import full187_earliest_positive_u0_curvature_frontier_gate_6900 as F


P = F.P
N = F.N
M = F.M
SLOPE = F.H.SLOPE
CURVATURE = F.H.CURVATURE
OUTER_Z = F.OUTER_Z
INV2 = F.INV2

AUTHORITIES = {
    "full187_active75_parametric_initial_jet_staircase_gate_6900.py":
        "db1725a1bb483e60f0b5e649aaa801d2090a2c14591a92e76b8c4a34e909035a",
    "full187_cross_slope_second_fringe_confluence_6900.py":
        "2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29",
    "full187_earliest_positive_u0_curvature_frontier_gate_6900.py":
        "cd763ffc825c0a9e1d73f055d1278b583fdcdac162a5ed597e289e24d4db53b0",
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def raw_y_interval(active, n, s):
    """All y with q=n-y+s a legal raw coordinate at fixed A,n,s."""
    if not 0 <= s <= CURVATURE or n + s >= M:
        return ()
    lower = max(0, active - SLOPE)
    upper = min(M - 1, active - s, n + s)
    if upper < lower:
        return ()
    return tuple(range(lower, upper + 1))


def raw_counts(active, n):
    return tuple(len(raw_y_interval(active, n, s))
                 for s in range(CURVATURE + 1))


def selected_counts(active, n, depth):
    counts = []
    for s in range(CURVATURE + 1):
        count = 0
        for y in raw_y_interval(active, n, s):
            r = active - y - s
            q = n - y + s
            assert min(r, q) >= 0
            if q < depth(active, y, r, s):
                count += 1
        counts.append(count)
    return tuple(counts)


def target_dimension(active, n, h):
    """Number of rows u^a v^(h-a) in this homogeneous target grade."""
    K = M - n
    if not 0 <= h <= min(active, K - 1):
        return 0
    return min(h + 1, K - h)


def jset(counts, h):
    """Associated leading columns v^s t^j with h=s+j."""
    return tuple(sorted(
        h - s for s, count in enumerate(counts)
        if 0 <= h - s < count
    ))


def stratum(active, n, h, depth=None):
    raw = raw_counts(active, n)
    raw_j = jset(raw, h)
    dimension = target_dimension(active, n, h)
    raw_rank = min(len(raw_j), dimension)
    if depth is None:
        return raw_j, (), dimension, raw_rank, 0, 0
    selected = selected_counts(active, n, depth)
    selected_j = jset(selected, h)
    selected_rank = min(len(selected_j), dimension)
    return (raw_j, selected_j, dimension, raw_rank, selected_rank,
            raw_rank - selected_rank)


def active_receipt(active, depth=None):
    total_raw_rank = 0
    total_selected_rank = 0
    defects = []
    strata = []
    for n in range(-CURVATURE, M):
        if not any(raw_counts(active, n)):
            continue
        K = M - n
        for h in range(min(active, K - 1) + 1):
            raw_j, selected_j, dimension, raw_rank, selected_rank, defect = (
                stratum(active, n, h, depth))
            if not raw_j:
                continue
            total_raw_rank += raw_rank
            total_selected_rank += selected_rank if depth is not None else 0
            record = (active, n, h, K, dimension, raw_j, selected_j,
                      raw_rank, selected_rank, defect)
            strata.append(record)
            if defect:
                defects.append(record)
    return total_raw_rank, total_selected_rank, tuple(strata), tuple(defects)


def raw_depth(_active, y, _r, _s):
    return M - y


def old_depth(_active, y, _r, s):
    return B.staircase_qmax(y, s) + 1


def legal_depth(_active, y, r, s):
    return min(M - y, F.H.width(y, r, s) // N)


def pascal_entry(j, a):
    if a > j:
        return 0
    return comb(j, a) * pow(-INV2 % P, j - a, P) % P


def vandermonde_minor(j_values):
    """Exact unit minor of v^s(u-v/2)^j in rows a=0..k-1."""
    k = len(j_values)
    if not k:
        return 1, 1
    matrix = [[pascal_entry(j, a) for j in j_values]
              for a in range(k)]
    rank, determinant = F.modular_rank_and_det(matrix)
    numerator = 1
    for left in range(k):
        for right in range(left + 1, k):
            numerator *= j_values[right] - j_values[left]
    denominator = 1
    for a in range(k):
        denominator *= factorial(a)
    exponent = sum(j_values) - k * (k - 1) // 2
    expected = (
        pow(-INV2 % P, exponent, P)
        * (numerator % P) * pow(denominator % P, -1, P)
    ) % P
    assert rank == k and determinant == expected and determinant
    return determinant, expected


def normalized_raw_identity_gate():
    """Check the literal row-to-(n,u,v) change on all 880 A=75 entries."""
    coordinates, rows, rank = B.coordinate_census(75)
    checked = 0
    n_histogram = Counter()
    for (y, r, s, q, z), column in coordinates:
        n = y + q - s
        for row, scalar in column.items():
            i, a, row_r, b, row_z = row
            c = b - s
            residual = y - a - c
            assert min(a, c, residual) >= 0
            assert (i, row_r, row_z) == (n - a + b, 75 - a - b, z)
            assert i + 3 * a == n + b + 2 * a < M
            expected = (
                factorial(y)
                // (factorial(a) * factorial(c) * factorial(residual))
            ) % P
            expected = expected * pow(-INV2 % P, c, P) % P
            assert scalar == expected
            checked += 1
            n_histogram[n] += 1
    assert (len(coordinates), len(rows), checked, rank) == (231, 154, 880,
                                                            103)
    return {
        "active75_coordinates_rows_entries_rank": (231, 154, 880, 103),
        "entry_identity": (
            "n=y+q-s=i+a-b; raw column is the weight-truncated coefficient "
            "vector of v^s(1+u-v/2)^y"),
        "n_entry_histogram": tuple(sorted(n_histogram.items())),
        "every_literal_entry_matches_the_normalized_formula": True,
    }


def all_strata_unit_minor_gate():
    receipts = []
    minor_receipts = []
    minor_size_histogram = Counter()
    minor_cache = {}
    max_j = 0
    for active in range(C.L - OUTER_Z):
        raw_rank, _unused, strata, _defects = active_receipt(active)
        receipts.append((active, raw_rank, len(strata)))
        for (_A, n, h, K, dimension, raw_j, _selected_j,
             stratum_rank, _selected_rank, _defect) in strata:
            chosen = tuple(sorted(raw_j)[:stratum_rank])
            assert len(chosen) == stratum_rank <= dimension
            if chosen not in minor_cache:
                minor_cache[chosen] = vandermonde_minor(chosen)[0]
            determinant = minor_cache[chosen]
            minor_receipts.append((active, n, h, chosen, determinant))
            minor_size_histogram[len(chosen)] += 1
            max_j = max(max_j, max(chosen, default=0))
    assert max_j <= SLOPE
    # Compare the symbolic rank formula to the three exact dense matrices.
    assert tuple(receipt[1] for receipt in receipts[75:78]) == (103, 79, 56)
    minor_hash = hashlib.sha256(
        repr(tuple(minor_receipts)).encode()).hexdigest()
    assert minor_hash == (
        "01a1452f3cbe47b0d72a7b2d23c7a756a116a17fed0e9160aa8b5463e5bfc758")
    return {
        "active_symbolic_rawrank_stratumcount": tuple(receipts),
        "canonical_minimal_J_formula": (
            "Jraw(A,n,h)={h-s:0<=s<=10, 0<=h-s<m(A,n,s)}; "
            "d(A,n,h)=min(h+1,60-n-h); take the smallest "
            "min(|Jraw|,d) distinct j values"),
        "unit_minor_formula": (
            "det[binom(j_c,a)(-1/2)^(j_c-a)]_{0<=a,c<k}="
            "(-1/2)^(sum(j)-k(k-1)/2)*Vandermonde(j)/prod(a!)"),
        "maximum_j": max_j,
        "characteristic_condition": "char(F)>60 (and hence 2 invertible)",
        "minor_size_histogram": tuple(sorted(minor_size_histogram.items())),
        "unique_J_minor_count": len(minor_cache),
        "all_stratum_J_and_minor_sha256": minor_hash,
        "every_nonempty_stratum_has_an_explicit_unit_minor": True,
        "dense_rank_crosscheck_A75_A76_A77": (103, 79, 56),
    }


def defect_census(depth):
    all_defects = []
    active_summary = []
    rank_summary = []
    for active in range(C.L - OUTER_Z):
        raw_rank, selected_rank, _strata, defects = active_receipt(
            active, depth)
        all_defects.extend(defects)
        active_summary.append((
            active, len(defects), sum(record[-1] for record in defects),
            max((record[-1] for record in defects), default=0),
        ))
        rank_summary.append((active, raw_rank, selected_rank,
                             raw_rank - selected_rank))
    return tuple(all_defects), tuple(active_summary), tuple(rank_summary)


def minimal_prefix_basis(active, enforce_capacity):
    """Greedy basis using the exact one-new-J-direction rank criterion.

    Coordinates are scanned by increasing q, then y, then s.  A coordinate
    can be accepted only when all lower q on its physical polynomial were
    accepted.  Adding the next exponent to an (n,s) group creates precisely
    j=count at h=s+j in the associated graded, so the test is local.
    """
    shapes = B.physical_shapes(active)
    depths = {(y, r, s): 0 for y, r, s, _z in shapes}
    counts = defaultdict(Counter)
    selected = []
    for q in range(M):
        for y, r, s, z in shapes:
            if q >= M - y or depths[(y, r, s)] != q:
                continue
            if enforce_capacity and (q + 1) * N > F.H.width(y, r, s):
                continue
            n = y + q - s
            j = counts[n][s]
            h = s + j
            raw_j, _unused, dimension, raw_rank, _selected_rank, _defect = (
                stratum(active, n, h))
            selected_j = jset(tuple(counts[n][index]
                                    for index in range(CURVATURE + 1)), h)
            before = min(len(selected_j), dimension)
            if before >= raw_rank:
                continue
            assert j in raw_j and j not in selected_j
            counts[n][s] += 1
            depths[(y, r, s)] += 1
            selected.append((y, r, s, q, z, n, h, j))
            after_j = jset(tuple(counts[n][index]
                                 for index in range(CURVATURE + 1)), h)
            assert min(len(after_j), dimension) == before + 1
    raw_rank, _unused, _strata, _defects = active_receipt(active)
    return tuple(selected), tuple(sorted(depths.items())), raw_rank


def corrected_minimal_prefix_gate():
    receipts = []
    all_selected = []
    first_negative = None
    for active in range(C.L - OUTER_Z):
        selected, depths, raw_rank = minimal_prefix_basis(
            active, enforce_capacity=False)
        assert len(selected) == raw_rank
        windows = tuple(
            (F.H.width(y, r, s) - depth * N, (y, r, s), depth)
            for (y, r, s), depth in depths if depth
        )
        minimum = min(windows)
        if minimum[0] < 0 and first_negative is None:
            first_negative = (active, minimum)
        receipts.append((active, raw_rank, len(selected), minimum,
                         max(depth for _physical, depth in depths)))
        all_selected.append((active, selected))
    # "First" for the actual descending construction is the largest bad A.
    descending_first_negative = next(
        record for record in reversed(receipts) if record[3][0] < 0)
    assert descending_first_negative == (
        57, 1_342, 1_342, (-54_108, (36, 11, 10), 13), 13)

    selected68 = dict(all_selected)[68]
    old68 = {
        (y, r, s, q, z)
        for y, r, s, z in B.physical_shapes(68)
        for q in range(M - y)
        if q < old_depth(68, y, r, s)
    }
    corrected68 = {record[:5] for record in selected68}
    assert corrected68 - old68 == {(57, 2, 9, 1, OUTER_Z)}
    assert not old68 - corrected68

    contiguous_green = tuple(
        active for active, _rank, _count, minimum, _maxdepth in receipts
        if active >= 58 and minimum[0] >= 0)
    assert contiguous_green == tuple(range(58, 78))
    selected_hash = hashlib.sha256(
        repr(tuple(all_selected)).encode()).hexdigest()
    assert selected_hash == (
        "c37ed7d1058c8e22858005994dafd89369f7cb9d1bf2d2589d8671098f33e535")
    return {
        "selection_rule": (
            "scan q,y,s; preserve physical q-prefixes; adding a coordinate "
            "to (n,s) creates j=current_count at h=s+j; retain it iff the "
            "current J-rank is below min(|Jraw|,d)"),
        "every_unconstrained_minimal_prefix_count_equals_symbolic_raw_rank":
            True,
        "corrected_contiguous_capacity_green_active_range": (58, 77),
        "first_old_B_repair_at_A68": (57, 2, 9, 1, OUTER_Z),
        "first_descending_negative_window_basis_receipt":
            descending_first_negative,
        "active_rawrank_selected_minwindow_maxdepth": tuple(receipts),
        "all_minimal_selected_coordinate_receipts_sha256": selected_hash,
    }


def old_staircase_correction_gate():
    defects, summary, ranks = defect_census(old_depth)
    descending_first = next(record for record in reversed(defects)
                            if record[0] == max(r[0] for r in defects))
    first_active = max(record[0] for record in defects)
    first_active_defects = tuple(record for record in defects
                                 if record[0] == first_active)
    assert first_active == 68 and len(first_active_defects) == 1
    assert len(defects) == 17_706
    defect_hash = hashlib.sha256(repr(defects).encode()).hexdigest()
    assert defect_hash == (
        "1dfb9480374b5be8e56d16e26ea7104e55704f571b0e69d832a6f87a3ed10a2d")
    witness = first_active_defects[0]
    assert witness == (
        68, 49, 10, 11, 1, (0, 1, 2, 3, 4, 5, 6), (), 1, 0, 1)
    # A single legal prefix extension repairs this first stratum.
    correction = (57, 2, 9, 1, OUTER_Z)
    width = F.H.width(*correction[:3])
    assert B.staircase_qmax(57, 9) == 0
    assert width - 2 * N == 1_387_684
    assert descending_first == witness
    return {
        "old_B_full_rank_active_range": (69, 77),
        "first_descending_defect": witness,
        "first_defect_explanation": (
            "A=68,n=49,h=10,K=11 has seven raw j directions and a "
            "one-dimensional target, but old B contributes none"),
        "one_legal_first_repair_y_r_s_q_z_width_slack": (
            correction, width, width - 2 * N),
        "per_active_defect_count_total_max": tuple(
            record for record in summary if record[1]),
        "per_active_raw_selected_defect_rank": tuple(
            record for record in ranks if record[3]),
        "all_defect_strata_count": len(defects),
        "all_defect_strata_sha256": defect_hash,
        "exact_defect_predicate": (
            "min(|Jselected(A,n,h)|,d(A,n,h)) < "
            "min(|Jraw(A,n,h)|,d(A,n,h))"),
        "old_all_A_span_conjecture_is_false": True,
    }


def maximal_legal_window_gate():
    defects, summary, ranks = defect_census(legal_depth)
    good = tuple(active for active, _raw, _selected, defect in ranks
                 if defect == 0)
    bad = tuple(active for active, _raw, _selected, defect in ranks
                if defect)
    assert good == (56,) + tuple(range(58, 78))
    assert bad == tuple(range(56)) + (57,)
    assert len(defects) == 9_031
    defect_hash = hashlib.sha256(repr(defects).encode()).hexdigest()
    assert defect_hash == (
        "21e976249053869a03c9112c02196c5434083a3758641682071d9a3430d8c3cc")
    # A=57 is bad and A=56 good, so spell out the nonmonotone exception.
    assert 57 in bad and 56 in good
    first_active = max(record[0] for record in defects)
    first_defects = tuple(record for record in defects
                          if record[0] == first_active)
    assert first_active == 57 and len(first_defects) == 1
    witness = first_defects[0]
    assert witness == (
        57, 38, 21, 22, 1, (11,), (), 1, 0, 1)

    # The only raw associated direction is j=11,s=10.  It needs all twelve
    # y=36..47 exponents at n=38.  The y=36 member is q=12 on the simultaneous
    # r+s=21,s=10 corner and exceeds its literal window by 54,108.
    chain = []
    for y in raw_y_interval(57, 38, 10):
        r = 57 - y - 10
        q = 38 - y + 10
        depth = legal_depth(57, y, r, 10)
        chain.append((y, r, 10, q, depth, F.H.width(y, r, 10),
                      F.H.width(y, r, 10) - (q + 1) * N))
    assert tuple(y for y, *_rest in chain) == tuple(range(36, 48))
    assert chain[0] == (36, 11, 10, 12, 12, 3_353_764, -54_108)
    assert all(record[-1] >= 0 for record in chain[1:])
    residual = chain[0][5] - chain[0][4] * N
    assert residual == 208_036 and N - residual == 54_108

    return {
        "all_literal_initial_prefixes_span_exactly_for_active": good,
        "literal_initial_prefix_span_fails_for_active": bad,
        "first_descending_window_defect": witness,
        "first_defect_raw_chain_y_r_s_q_capacity_width_slack": tuple(chain),
        "first_defect_is_intersection_r_plus_s_21_and_s_10": True,
        "partial_thirteenth_jet_dimension_and_remaining_node_quotient": (
            residual, N - residual),
        "per_active_defect_count_total_max": tuple(
            record for record in summary if record[1]),
        "per_active_raw_legal_defect_rank": tuple(
            record for record in ranks if record[3]),
        "all_defect_strata_count": len(defects),
        "all_defect_strata_sha256": defect_hash,
        "no_all_node_initial_prefix_choice_can_span_at_A57": True,
    }


def nullspace_basis(matrix):
    """Deterministic right-nullspace basis over F_p for a small matrix."""
    if not matrix:
        return ()
    a = [[value % P for value in row] for row in matrix]
    row_count = len(a)
    column_count = len(a[0])
    pivot_columns = []
    pivot_row = 0
    for column in range(column_count):
        pivot = next((row for row in range(pivot_row, row_count)
                      if a[row][column]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        inverse = pow(a[pivot_row][column], -1, P)
        a[pivot_row] = [value * inverse % P for value in a[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or not a[row][column]:
                continue
            factor = a[row][column]
            a[row] = [(left - factor * right) % P
                      for left, right in zip(a[row], a[pivot_row])]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == row_count:
            break
    free_columns = tuple(column for column in range(column_count)
                         if column not in set(pivot_columns))
    basis = []
    for free in free_columns:
        vector = [0] * column_count
        vector[free] = 1
        for row, pivot in reversed(tuple(enumerate(pivot_columns))):
            vector[pivot] = -sum(
                a[row][column] * vector[column]
                for column in free_columns
            ) % P
        assert all(sum(left * right for left, right in zip(equation, vector))
                   % P == 0 for equation in matrix)
        basis.append(tuple(vector))
    return tuple(basis)


def literal_a57_n38_gate():
    """Dense, tiny authority for the disputed first window obstruction."""
    active = 57
    n = 38
    raw = []
    legal = []
    for y, r, s, z in B.physical_shapes(active):
        for q in range(M - y):
            if y + q - s != n:
                continue
            key = (y, r, s, q, z)
            item = (key, B.raw_contact_column(active, key))
            raw.append(item)
            if q < legal_depth(active, y, r, s):
                legal.append(item)
    rows = tuple(sorted(
        set().union(*(set(column) for _key, column in raw)),
        key=lambda row: (row[1] + row[3], row[0] + 3 * row[1], row),
    ))
    raw_matrix = [[column.get(row, 0) for _key, column in raw]
                  for row in rows]
    legal_matrix = [[column.get(row, 0) for _key, column in legal]
                    for row in rows]
    raw_rank = F.modular_rank(raw_matrix)
    legal_rank = F.modular_rank(legal_matrix)
    omitted = tuple(item for item in raw if item not in legal)
    assert (len(raw), len(legal), len(rows), raw_rank, legal_rank,
            len(omitted)) == (87, 86, 132, 87, 86, 1)
    omitted_key, omitted_column = omitted[0]
    assert omitted_key == (36, 11, 10, 12, OUTER_Z)

    equations = [
        [column.get(row, 0) for row in rows] for _key, column in legal
    ]
    nullspace = nullspace_basis(equations)
    assert len(nullspace) == len(rows) - legal_rank == 46
    dual = next(vector for vector in nullspace
                if sum(value * omitted_column.get(row, 0)
                       for row, value in zip(rows, vector)) % P)
    evaluation = sum(value * omitted_column.get(row, 0)
                     for row, value in zip(rows, dual)) % P
    inverse = pow(evaluation, -1, P)
    dual = tuple(value * inverse % P for value in dual)
    assert all(sum(value * column.get(row, 0)
                   for row, value in zip(rows, dual)) % P == 0
               for _key, column in legal)
    assert sum(value * omitted_column.get(row, 0)
               for row, value in zip(rows, dual)) % P == 1
    dual_sparse = tuple((row, value) for row, value in zip(rows, dual)
                        if value)
    omitted_hash = hashlib.sha256(
        repr(tuple(sorted(omitted_column.items()))).encode()).hexdigest()
    dual_hash = hashlib.sha256(repr(dual_sparse).encode()).hexdigest()
    assert omitted_hash == (
        "707ed944ad4eda2740da7470292017ad43aad3b46d2bc0c4830a0c28f38456dc")
    assert dual_hash == (
        "ee4106cbef0fd9ae18a82d00f1692554c59aa0cbca9cae7aee0e12abfaa80be5")
    return {
        "active_n_rawcoords_legalcoords_rows_rawrank_legalrank": (
            active, n, len(raw), len(legal), len(rows), raw_rank, legal_rank),
        "omitted_key": omitted_key,
        "omitted_raw_column_sha256": omitted_hash,
        "dual_support_count": len(dual_sparse),
        "dual_sparse_sha256": dual_hash,
        "dual_evaluations_on_all_legal_then_omitted": (
            tuple(0 for _item in legal), 1),
        "literal_dense_block_confirms_symbolic_defect": True,
    }


def closest_lower_outer_z_predecessors():
    """Enumerate the h=1 section tails which can hit the A57 witness row."""
    target = (59, 0, 36, 21, OUTER_Z)
    predecessors = []
    for s in range(CURVATURE + 1):
        for r in range(SLOPE - s + 1):
            c = target[3] - s
            b = target[2] - r
            f = b + c
            q = target[0] - f - c
            if min(b, c, f, q) < 0:
                continue
            shift = 1
            y = f + shift
            if y >= M:
                continue
            source_z = OUTER_Z - shift
            assert C.row_of(r, s, source_z, f, shift, 0, c, q) == target
            scalar = (comb(y, f) * comb(y - f, shift)
                      * C.local_scalar(f, 0, c)) % P
            assert scalar
            predecessors.append((
                r, s, y, f, q, shift, source_z, y + r + s,
                y - f - shift, scalar,
            ))
    assert len(predecessors) == 87
    predecessor_hash = hashlib.sha256(
        repr(tuple(predecessors)).encode()).hexdigest()
    assert predecessor_hash == (
        "77b438e5d11ae50200fdbc4048f8d20f0944c47d04f6a112e9e8f780e070c8e4")
    minimum_shape_order = min(r + s for r, s, *_rest in predecessors)
    smallest = tuple(record for record in predecessors
                     if record[0] + record[1] == minimum_shape_order)
    assert tuple(record[:9] for record in smallest) == (
        (1, 9, 48, 47, 0, 1, 2624, 58, 0),
        (0, 10, 48, 47, 1, 1, 2624, 58, 0),
    )
    smallest_slacks = tuple(
        (record[:5], F.H.width(record[2], record[0], record[1]),
         F.H.width(record[2], record[0], record[1])
         - (record[4] + 1) * N)
        for record in smallest
    )
    assert smallest_slacks == (
        ((1, 9, 48, 47, 0), 3_222_681, 2_960_537),
        ((0, 10, 48, 47, 1), 3_222_682, 2_698_394),
    )
    return {
        "missing_target_row": target,
        "nearest_shift": 1,
        "all_87_nearest_predecessor_parameterization": (
            "0<=s<=10, max(0,19-2s)<=r<=21-s; "
            "y=58-r-s, f=57-r-s, q=r+2s-19, source z=2624, "
            "source active=58, remaining u0=0"),
        "nearest_predecessor_count_sha256": (
            len(predecessors), predecessor_hash),
        "minimum_derivative_order": minimum_shape_order,
        "smallest_predecessors": smallest,
        "smallest_predecessor_key_width_slack": smallest_slacks,
        "reachability_is_not_a_rescue_proof": True,
    }


def main():
    for filename, expected in AUTHORITIES.items():
        assert file_sha256(HERE / filename) == expected
    normalized = normalized_raw_identity_gate()
    unit_minors = all_strata_unit_minor_gate()
    corrected = corrected_minimal_prefix_gate()
    old_correction = old_staircase_correction_gate()
    legal = maximal_legal_window_gate()
    literal_a57 = literal_a57_n38_gate()
    predecessors = closest_lower_outer_z_predecessors()

    stable = {
        "scope": (
            "symbolic fixed-outer-Z contact straightening for every "
            "0<=A<=77, correction of the old B_A conjecture, and exact "
            "literal-window defect census; no production changes"),
        "target_p_N_M_outerZ": (P, N, M, OUTER_Z),
        "authority_sha256": tuple(sorted(AUTHORITIES.items())),
        "normalized_contact_identity": normalized,
        "all_strata_pascal_unit_minors": unit_minors,
        "corrected_minimal_prefix_recurrence": corrected,
        "old_staircase_correction": old_correction,
        "maximal_literal_initial_prefix_gate": legal,
        "literal_A57_n38_dense_discriminator": literal_a57,
        "closest_lower_outer_z_predecessors": predecessors,
        "well_founded_induction_statement": (
            "Order pending blocks lexicographically by (outerZ,J-active,"
            "contact weight). At fixed outerZ,A decompose by n=y+q-s and "
            "ordinary t/v degree h. Solve each h block by the displayed "
            "unit Pascal minor. Unprescribed higher q increases every contact "
            "weight; every f<y output increases (outerZ,J-active), with its "
            "positive-u0 mate also increasing outerZ. Hence local solves "
            "terminate provided each block's legal J-set meets the exact "
            "rank criterion. This premise holds through A=58 and fails at "
            "A=57 for the all-node initial-prefix source class."),
        "decision": "GREEN_SYMBOLIC_STRAIGHTENING_RED_UNIFORM_WINDOW_AT_A57",
        "scope_guard": (
            "The Pascal rank theorem is symbolic and covers both caps. The "
            "RED says only that fixed-z all-node initial-prefix sections "
            "cannot span A57. The 87 h=1 lower-z tails establish reachability "
            "of the missing row, not an independent kernel jet or a rescue; "
            "that connecting map remains open. The short corner still has a "
            "208036-dimensional partial thirteenth-jet channel; only its "
            "54108-dimensional node quotient is obstructed by this gate."),
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
