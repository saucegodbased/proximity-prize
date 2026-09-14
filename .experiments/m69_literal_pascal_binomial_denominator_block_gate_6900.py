#!/usr/bin/env python3
"""Exact literal-Pascal rank gate for one allowed nonmonomial rational W.

This attacks the genuine shared-tail map for the first compact m69 chain

    (r,s,q)=(0,0,26), Y={41,42}, terminal T=94.

Choose the root-free denominator

    E(X)=X^4096-2,  N0(X)=1,  W=N0/E

over the benchmark prime field.  Since 4096 divides the NTT length 262144,
putting Z=X^4096 splits the cyclic polynomial ring into 4096 independent
blocks of length 64.  Clearing the unit E from output row y turns the exact
source/terminal equation into

    sum_k binom(k,y) E^(T-k) P_k = binom(T,y) C, y=41,42,

where P_k ranges over the real alternating physical prefix cap and C ranges
over the terminal prefix.  We compute exact FLINT ranks for every distinct
residue-cap pattern.  No giant 524288-row matrix is materialized.

This is an exact positive/negative discriminator for this allowed rational
only.  It is not an arbitrary-rational theorem.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from math import comb
import hashlib
import json
from pathlib import Path
import resource
import sys

from flint import nmod_mat


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import m69_reciprocal_all_defect_interval_gate_6900 as profile


P = 2_130_706_433
OMEGA_DEGREE = profile.N
DENOMINATOR_DEGREE = 4_096
ALPHA = 2
BLOCK_LENGTH = OMEGA_DEGREE // DENOMINATOR_DEGREE
FIRST_Y = 41
SECOND_Y = 42
TERMINAL = 94
Q = 26
SOURCE_CONTACTS = tuple(range(FIRST_Y, profile.M))
PROFILE_SHA256 = "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069"


def prefix_count(cap: int, residue: int) -> int:
    if residue >= cap:
        return 0
    return (cap - 1 - residue) // DENOMINATOR_DEGREE + 1


def source_cap(k: int) -> int:
    cap = profile.width(k, 0, 0) % OMEGA_DEGREE
    assert 0 < cap < OMEGA_DEGREE
    return cap


def terminal_dimension() -> int:
    result = profile.width(TERMINAL, 0, 0) - Q
    assert result == 127_797
    return result


def terminal_degrees(residue: int):
    """Z-degrees of physical terminal exponents q <= j < width(T)."""
    return tuple(
        degree for degree in range(BLOCK_LENGTH)
        if Q <= residue + DENOMINATOR_DEGREE * degree
        < profile.width(TERMINAL, 0, 0)
    )


def binomial_power_coefficients(power: int):
    """Coefficients of `(Z-ALPHA)^power` over the benchmark field."""
    assert 0 <= power < BLOCK_LENGTH
    return tuple(
        comb(power, degree)
        * pow(-ALPHA, power - degree, P) % P
        for degree in range(power + 1)
    )


def block_pattern(residue: int):
    return (
        tuple(prefix_count(source_cap(k), residue)
              for k in SOURCE_CONTACTS),
        terminal_degrees(residue),
    )


def horizontal_concat(left: nmod_mat, right: nmod_mat) -> nmod_mat:
    assert left.nrows() == right.nrows()
    return nmod_mat(left.nrows(), left.ncols() + right.ncols(), [
        int(left[row, column]) % P
        if column < left.ncols()
        else int(right[row, column - left.ncols()]) % P
        for row in range(left.nrows())
        for column in range(left.ncols() + right.ncols())
    ], P)


def pattern_matrices(pattern):
    source_counts, target_degrees = pattern
    rows = 2 * BLOCK_LENGTH
    columns = []
    labels = []
    power_cache = {
        TERMINAL - k: binomial_power_coefficients(TERMINAL - k)
        for k in SOURCE_CONTACTS
    }
    for k, count in zip(SOURCE_CONTACTS, source_counts):
        scalar_first = comb(k, FIRST_Y) % P
        scalar_second = comb(k, SECOND_Y) % P
        coefficients = power_cache[TERMINAL - k]
        for source_degree in range(count):
            column = [0] * rows
            for offset, coefficient in enumerate(coefficients):
                output_degree = (source_degree + offset) % BLOCK_LENGTH
                column[output_degree] = (
                    column[output_degree] + scalar_first * coefficient
                ) % P
                column[BLOCK_LENGTH + output_degree] = (
                    column[BLOCK_LENGTH + output_degree]
                    + scalar_second * coefficient
                ) % P
            labels.append((k, source_degree))
            columns.append(column)

    targets = []
    target_labels = []
    terminal_first = comb(TERMINAL, FIRST_Y) % P
    terminal_second = comb(TERMINAL, SECOND_Y) % P
    for degree in target_degrees:
        column = [0] * rows
        column[degree] = terminal_first
        column[BLOCK_LENGTH + degree] = terminal_second
        targets.append(column)
        target_labels.append(degree)

    source = nmod_mat(rows, len(columns), [
        columns[column][row]
        for row in range(rows) for column in range(len(columns))
    ], P)
    target = nmod_mat(rows, len(targets), [
        targets[column][row]
        for row in range(rows) for column in range(len(targets))
    ], P)
    return source, target, tuple(labels), tuple(target_labels)


def pivot_columns_from_rref(matrix: nmod_mat):
    reduced, rank = matrix.rref()
    pivots = []
    previous = -1
    for row in range(rank):
        pivot = next(
            column for column in range(previous + 1, reduced.ncols())
            if int(reduced[row, column]) % P
        )
        assert int(reduced[row, pivot]) % P == 1
        pivots.append(pivot)
        previous = pivot
    return tuple(pivots), rank


def compact_preimage(source, target, labels, target_labels,
                     target_column_index=0):
    """Extract one deterministic preimage when source has full row rank."""
    pivots, rank = pivot_columns_from_rref(source)
    assert rank == source.nrows()
    square = nmod_mat(source.nrows(), source.nrows(), [
        int(source[row, pivots[column]]) % P
        for row in range(source.nrows())
        for column in range(source.nrows())
    ], P)
    rhs = nmod_mat(source.nrows(), 1, [
        int(target[row, target_column_index]) % P
        for row in range(source.nrows())
    ], P)
    solution = square.solve(rhs)
    assert square * solution == rhs
    support = tuple(
        (labels[pivots[index]], int(solution[index, 0]) % P)
        for index in range(len(pivots))
        if int(solution[index, 0]) % P
    )
    return {
        "target_block_degree": target_labels[target_column_index],
        "pivot_count": len(pivots),
        "nonzero_source_count": len(support),
        "source_support": support,
        "support_sha256": hashlib.sha256(repr(support).encode()).hexdigest(),
    }


def main():
    profile_path = Path(profile.__file__)
    assert hashlib.sha256(profile_path.read_bytes()).hexdigest() == PROFILE_SHA256
    assert OMEGA_DEGREE % DENOMINATOR_DEGREE == 0
    assert BLOCK_LENGTH == 64
    assert 2_151 <= DENOMINATOR_DEGREE <= 18_414

    # If E and X^N-1 shared a root, alpha^(N/e) would equal one.
    alpha_power = pow(ALPHA, BLOCK_LENGTH, P)
    assert alpha_power == 402_124_772
    assert alpha_power != 1

    _defects, _shapes, coefficients = profile.defect_census()
    chain = tuple(y for y, r, s, q in coefficients
                  if (r, s, q) == (0, 0, Q))
    assert chain == (FIRST_Y, SECOND_Y)

    grouped = defaultdict(list)
    for residue in range(DENOMINATOR_DEGREE):
        grouped[block_pattern(residue)].append(residue)

    records = []
    rank_histogram = Counter()
    defect_histogram = Counter()
    representative_preimage = None
    for pattern, residues in sorted(grouped.items(), key=lambda item: item[1][0]):
        source, target, labels, target_labels = pattern_matrices(pattern)
        source_rank = source.rank()
        augmented_rank = horizontal_concat(source, target).rank()
        defect = augmented_rank - source_rank
        rank_histogram[source_rank] += len(residues)
        defect_histogram[defect] += len(residues)
        record = (
            (residues[0], residues[-1], len(residues)),
            pattern,
            (source.nrows(), source.ncols(), target.ncols()),
            (source_rank, augmented_rank, defect),
        )
        records.append(record)
        assert defect == 0
        if representative_preimage is None and target.ncols() > 0:
            assert source_rank == source.nrows()
            representative_preimage = {
                "residue": residues[0],
                "pattern_residue_interval": (residues[0], residues[-1]),
                **compact_preimage(
                    source, target, labels, target_labels),
            }

    assert representative_preimage is not None
    assert sum(len(residues) for residues in grouped.values()) == 4_096
    assert defect_histogram == Counter({0: 4_096})
    record_stream = hashlib.sha256(repr(tuple(records)).encode()).hexdigest()

    stable = {
        "field_prime_N": (P, OMEGA_DEGREE),
        "literal_chain_r_s_q_Y_T": (
            (0, 0, Q), chain, TERMINAL),
        "denominator": "E=X^4096-2",
        "numerator": "N0=1",
        "denominator_degree_allowed_range": (
            DENOMINATOR_DEGREE, (2_151, 18_414)),
        "rootfree_receipt_alpha_pow_64_mod_p": alpha_power,
        "cyclic_block_decomposition": (
            "Z=X^4096, 4096 blocks, modulus Z^64-1"),
        "cleared_literal_equations": (
            "sum_k binom(k,y) E^(94-k) P_k = binom(94,y) C, "
            "y=41,42"),
        "source_contact_range": (
            min(SOURCE_CONTACTS), max(SOURCE_CONTACTS)),
        "source_prefix_caps": tuple(source_cap(k) for k in SOURCE_CONTACTS),
        "terminal_physical_exponent_interval_and_dimension": (
            (Q, profile.width(TERMINAL, 0, 0)), terminal_dimension()),
        "distinct_residue_cap_pattern_count": len(grouped),
        "block_rank_histogram_weighted_by_residue": tuple(sorted(
            rank_histogram.items())),
        "target_containment_defect_histogram_weighted_by_residue": tuple(
            sorted(defect_histogram.items())),
        "every_terminal_block_column_in_literal_source_image": True,
        "representative_compact_preimage": representative_preimage,
        "pattern_record_stream_sha256": record_stream,
        "decision": "GREEN_THIS_ALLOWED_BINOMIAL_DENOMINATOR",
        "scope": (
            "exact shared-tail containment for chain (0,0,26) and "
            "W=1/(X^4096-2) only; no arbitrary-rational claim"),
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
