#!/usr/bin/env python3
"""Exact literal-Pascal gate with a genuinely high-degree numerator.

For the m69 chain (r,s,q)=(0,0,26), Y={41,42}, T=94, take

    Z = X^4096,
    E = Z - 2,
    N0 = Z^32 - 3,
    W = N0/E.

Thus deg E=4096 and deg N0=131072, in the unresolved high-numerator
branch.  Both are units modulo X^262144-1 and are coprime.  The common
4096 stride splits the exact cyclic calculation into 4096 blocks of size
64.  For each distinct physical-cap pattern we check the two-row literal
Pascal containment after clearing denominators:

  sum_k binom(k,y) N0^(k-y) E^(94-k) P_k
      = binom(94,y) N0^(94-y) C,  y=41,42.

All ranks are exact over the benchmark prime using python-flint.  This is
an instance discriminator, not an arbitrary-rational theorem.
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
STRIDE = 4_096
BLOCK_LENGTH = OMEGA_DEGREE // STRIDE
FIRST_Y = 41
SECOND_Y = 42
TERMINAL = 94
Q = 26
SOURCE_CONTACTS = tuple(range(FIRST_Y, profile.M))
PROFILE_SHA256 = "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069"


def cyclic_mul(left, right):
    result = [0] * BLOCK_LENGTH
    for i, a in enumerate(left):
        if not a:
            continue
        for j, b in enumerate(right):
            if b:
                result[(i + j) % BLOCK_LENGTH] = (
                    result[(i + j) % BLOCK_LENGTH] + a * b
                ) % P
    return tuple(result)


def power_table(base, largest):
    one = (1,) + (0,) * (BLOCK_LENGTH - 1)
    answer = [one]
    for _ in range(largest):
        answer.append(cyclic_mul(answer[-1], base))
    return tuple(answer)


E = tuple([P - 2, 1] + [0] * (BLOCK_LENGTH - 2))
N0 = tuple([P - 3] + [0] * 31 + [1] + [0] * 31)
E_POWERS = power_table(E, TERMINAL - FIRST_Y)
N_POWERS = power_table(N0, TERMINAL - FIRST_Y)


def prefix_count(cap: int, residue: int) -> int:
    if residue >= cap:
        return 0
    return (cap - 1 - residue) // STRIDE + 1


def source_cap(k: int) -> int:
    cap = profile.width(k, 0, 0) % OMEGA_DEGREE
    assert 0 < cap < OMEGA_DEGREE
    return cap


def terminal_degrees(residue: int):
    return tuple(
        degree for degree in range(BLOCK_LENGTH)
        if Q <= residue + STRIDE * degree < profile.width(TERMINAL, 0, 0)
    )


def block_pattern(residue: int):
    return (
        tuple(prefix_count(source_cap(k), residue) for k in SOURCE_CONTACTS),
        terminal_degrees(residue),
    )


def shifted(poly, amount):
    result = [0] * BLOCK_LENGTH
    for degree, coefficient in enumerate(poly):
        result[(degree + amount) % BLOCK_LENGTH] = coefficient
    return result


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
    source_columns = []
    multiplier_cache = {}
    for k in SOURCE_CONTACTS:
        e_power = E_POWERS[TERMINAL - k]
        for y in (FIRST_Y, SECOND_Y):
            multiplier_cache[(k, y)] = cyclic_mul(
                N_POWERS[k - y], e_power)

    for k, count in zip(SOURCE_CONTACTS, source_counts):
        scalar_first = comb(k, FIRST_Y) % P
        scalar_second = comb(k, SECOND_Y) % P
        for source_degree in range(count):
            first = shifted(multiplier_cache[(k, FIRST_Y)], source_degree)
            second = shifted(multiplier_cache[(k, SECOND_Y)], source_degree)
            source_columns.append(
                [(scalar_first * value) % P for value in first]
                + [(scalar_second * value) % P for value in second])

    target_columns = []
    terminal_first = comb(TERMINAL, FIRST_Y) % P
    terminal_second = comb(TERMINAL, SECOND_Y) % P
    target_first = N_POWERS[TERMINAL - FIRST_Y]
    target_second = N_POWERS[TERMINAL - SECOND_Y]
    for degree in target_degrees:
        first = shifted(target_first, degree)
        second = shifted(target_second, degree)
        target_columns.append(
            [(terminal_first * value) % P for value in first]
            + [(terminal_second * value) % P for value in second])

    source = nmod_mat(rows, len(source_columns), [
        source_columns[column][row]
        for row in range(rows)
        for column in range(len(source_columns))
    ], P)
    target = nmod_mat(rows, len(target_columns), [
        target_columns[column][row]
        for row in range(rows)
        for column in range(len(target_columns))
    ], P)
    return source, target


def main():
    profile_path = Path(profile.__file__)
    assert hashlib.sha256(profile_path.read_bytes()).hexdigest() == PROFILE_SHA256
    assert OMEGA_DEGREE == 262_144
    assert BLOCK_LENGTH == 64
    assert 2_151 <= 4_096 <= 18_414
    assert 130_509 <= 131_072 <= 149_776

    # E=Z-2 is root-free for Z^64=1 exactly when 2^64 != 1.
    e_rootfree_receipt = pow(2, 64, P)
    assert e_rootfree_receipt == 402_124_772 != 1
    # N0=Z^32-3 is root-free because Z^32 is +/-1 on Z^64=1.
    assert 3 % P not in (1, P - 1)
    # E and N0 are coprime because N0(2)=2^32-3 is nonzero.
    gcd_receipt = (pow(2, 32, P) - 3) % P
    assert gcd_receipt != 0

    _defects, _shapes, coefficients = profile.defect_census()
    chain = tuple(y for y, r, s, q in coefficients
                  if (r, s, q) == (0, 0, Q))
    assert chain == (FIRST_Y, SECOND_Y)
    assert profile.width(TERMINAL, 0, 0) - Q == 127_797

    grouped = defaultdict(list)
    for residue in range(STRIDE):
        grouped[block_pattern(residue)].append(residue)

    records = []
    source_rank_histogram = Counter()
    defect_histogram = Counter()
    for pattern, residues in sorted(grouped.items(), key=lambda item: item[1][0]):
        source, target = pattern_matrices(pattern)
        source_rank = source.rank()
        augmented_rank = horizontal_concat(source, target).rank()
        defect = augmented_rank - source_rank
        source_rank_histogram[source_rank] += len(residues)
        defect_histogram[defect] += len(residues)
        records.append((
            (residues[0], residues[-1], len(residues)),
            pattern,
            (source.nrows(), source.ncols(), target.ncols()),
            (source_rank, augmented_rank, defect),
        ))

    assert sum(map(len, grouped.values())) == STRIDE
    record_hash = hashlib.sha256(repr(tuple(records)).encode()).hexdigest()
    stable = {
        "field_prime_N": (P, OMEGA_DEGREE),
        "literal_chain_r_s_q_Y_T": ((0, 0, Q), chain, TERMINAL),
        "denominator": "E=X^4096-2",
        "numerator": "N0=X^131072-3",
        "degrees_e_n": (4_096, 131_072),
        "rootfree_E_receipt_2_pow_64_mod_p": e_rootfree_receipt,
        "rootfree_N_reason": "Z^32 is +/-1 when Z^64=1, hence never 3",
        "coprime_receipt_N_at_Z_eq_2": gcd_receipt,
        "cyclic_block_decomposition": "Z=X^4096, 4096 blocks modulo Z^64-1",
        "cleared_literal_equations": (
            "sum_k binom(k,y) N0^(k-y) E^(94-k) P_k = "
            "binom(94,y) N0^(94-y) C, y=41,42"),
        "source_contact_range": (min(SOURCE_CONTACTS), max(SOURCE_CONTACTS)),
        "source_prefix_caps": tuple(source_cap(k) for k in SOURCE_CONTACTS),
        "terminal_physical_exponent_interval_and_dimension": (
            (Q, profile.width(TERMINAL, 0, 0)), 127_797),
        "distinct_residue_cap_pattern_count": len(grouped),
        "source_rank_histogram_weighted_by_residue": tuple(
            sorted(source_rank_histogram.items())),
        "target_containment_defect_histogram_weighted_by_residue": tuple(
            sorted(defect_histogram.items())),
        "every_terminal_block_column_in_literal_source_image": (
            defect_histogram == Counter({0: STRIDE})),
        "pattern_record_stream_sha256": record_hash,
        "scope": "exact one-instance gate; not an arbitrary-rational theorem",
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
