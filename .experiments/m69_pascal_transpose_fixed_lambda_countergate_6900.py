#!/usr/bin/env python3
"""Exact census audit of the literal m69 Pascal-transpose obstruction.

Fix a physical tail `(r,s,q)` and let `Y` be its consecutive deficient
contact indices.  A shared source at contact `k` enters every equation
`y in Y, y<=k`; hence a dual family `(lambda_y)` acts on that source by

    mu_k = sum_y binom(k,y) W^(k-y) lambda_y.

This is a Pascal transform of independent covectors, not one fixed covector
times successive powers of W.  For every chain with at least two rows, this
script constructs an exact two-row family which kills the terminal contact
pointwise but violates the first adjacent fixed-power relation.  It also
records the especially clean literal chain `(r,s,q)=(0,0,26)`, whose first
two sources have identical Hasse depth/order 26.

The countergate is algebraic: it falsifies the old source-adapter inference.
It does not construct a dual annihilating every ordinary source prefix.  In
the reciprocal-monomial specialization those ordinary constraints instead
close terminal containment by Pascal/Vandermonde rank; that is a different
mechanism and does not validate the fixed-lambda recurrence.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from math import comb
import hashlib
import json
from pathlib import Path
import resource
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import m69_reciprocal_all_defect_interval_gate_6900 as profile


P = 2_130_706_433
PROFILE_SHA256 = "9417a5797aa188cb6a1381b7c11e54f3df0ecf46908ad452d6dee925e1ae5069"


def deficient_chains(coefficients):
    grouped = defaultdict(list)
    for y, r, s, q in coefficients:
        grouped[(r, s, q)].append(y)
    result = {}
    for key, values in grouped.items():
        ys = tuple(sorted(values))
        assert ys == tuple(range(ys[0], ys[-1] + 1))
        result[key] = ys
    return result


def two_row_terminal_null_record(key, ys):
    """Construct and verify the universal two-row obstruction at W=1.

    Put `a=min(Y)`, `T=J-r-s`, and choose

        lambda_a     = T-a,
        lambda_(a+1) = -(a+1).

    Pascal's adjacent-binomial identity makes the terminal row zero.  At
    source contacts a and a+1 the geometric defect is

        mu_(a+1)-mu_a = a*(T-a-1)-1,

    which is nonzero for every literal multirow m69 chain.
    """
    r, s, q = key
    assert len(ys) >= 2
    a = ys[0]
    assert ys[1] == a + 1
    terminal = profile.J - r - s
    assert a + 1 < profile.M < terminal

    lambda_a = terminal - a
    lambda_next = -(a + 1)
    terminal_pairing = (
        comb(terminal, a) * lambda_a
        + comb(terminal, a + 1) * lambda_next
    )
    assert terminal_pairing == 0

    mu_a = lambda_a
    mu_next = (a + 1) * lambda_a + lambda_next
    defect = mu_next - mu_a
    closed_formula = a * (terminal - a - 1) - 1
    assert defect == closed_formula
    assert defect != 0
    assert abs(defect) < P
    assert defect % P != 0

    width_a = profile.width(a, r, s)
    width_next = profile.width(a + 1, r, s)
    depth_a, fringe_a = divmod(width_a, profile.N)
    depth_next, fringe_next = divmod(width_next, profile.N)
    assert 0 < fringe_a < profile.N
    assert 0 < fringe_next < profile.N
    assert depth_a <= q and depth_next <= q

    return (
        key, (ys[0], ys[-1]), len(ys), terminal,
        (lambda_a, lambda_next), terminal_pairing,
        (mu_a, mu_next, defect),
        (depth_a, fringe_a), (depth_next, fringe_next),
    )


def literal_monomial_terminal_pascal_rank(exponent=2_151):
    """Independent exact rank check for the clean two-row literal chain.

    In the reciprocal-monomial model, invariant coordinate `a` sees source
    contact `k` exactly when `(a+k*exponent) mod N` lies in its prefix.  Any
    two distinct Pascal columns have nonzero determinant in characteristic
    P.  We stream over the terminal interval and verify this directly.
    """
    first_y = 41
    terminal = 94
    terminal_dimension = profile.width(terminal, 0, 0) - 26
    terminal_start = (-terminal * exponent) % profile.N
    histogram = Counter()
    stream = hashlib.sha256()
    minimum = profile.M
    minimum_witness = None
    for offset in range(terminal_dimension):
        invariant = (terminal_start + offset) % profile.N
        contacts = tuple(
            k for k in range(first_y, profile.M)
            if (invariant + k * exponent) % profile.N
            < profile.width(k, 0, 0) % profile.N
        )
        assert len(contacts) >= 2
        k1, k2 = contacts[:2]
        determinant = (
            comb(k1, 41) * comb(k2, 42)
            - comb(k2, 41) * comb(k1, 42)
        ) % P
        assert determinant != 0
        histogram[len(contacts)] += 1
        if len(contacts) < minimum:
            minimum = len(contacts)
            minimum_witness = invariant
        stream.update(repr((invariant, contacts, determinant)).encode())
        stream.update(b"\n")
    assert sum(histogram.values()) == terminal_dimension
    assert (minimum, minimum_witness) == (13, 114751)
    return {
        "reciprocal_exponent": exponent,
        "terminal_dimension": terminal_dimension,
        "minimum_available_source_contacts": minimum,
        "minimum_witness_invariant": minimum_witness,
        "coverage_histogram": tuple(sorted(histogram.items())),
        "every_terminal_invariant_has_two_independent_pascal_columns": True,
        "terminal_column_contained_by_pascal_rank_not_fixed_recurrence": True,
        "coordinate_stream_sha256": stream.hexdigest(),
    }


def main():
    profile_path = Path(profile.__file__)
    assert hashlib.sha256(profile_path.read_bytes()).hexdigest() == PROFILE_SHA256
    defects, shapes, coefficients = profile.defect_census()
    assert (len(defects), len(shapes), len(coefficients)) == (
        13_093, 6_930, 140_153)
    chains = deficient_chains(coefficients)
    assert len(chains) == 9_900

    length_histogram = Counter(map(len, chains.values()))
    records = []
    for key, ys in sorted(chains.items()):
        if len(ys) >= 2:
            records.append(two_row_terminal_null_record(key, ys))
    assert len(records) == 9_405

    literal_key = (0, 0, 26)
    literal_ys = chains[literal_key]
    assert literal_ys == (41, 42)
    literal = two_row_terminal_null_record(literal_key, literal_ys)
    assert literal == (
        (0, 0, 26), (41, 42), 2, 94,
        (53, -42), 0, (53, 2184, 2131),
        (26, 258842), (26, 127771),
    )
    assert (comb(94, 41), comb(94, 42)) == (
        760365888182828026538367852,
        959509335087854414441273718,
    )
    assert pow(profile.N, 26, P) == 243251425
    monomial_terminal_rank = literal_monomial_terminal_pascal_rank()

    stream = hashlib.sha256()
    for record in records:
        stream.update(repr(record).encode())
        stream.update(b"\n")

    stable = {
        "profile_M_slope_curvature_J_L": (
            profile.M, profile.SLOPE, profile.CURVATURE,
            profile.J, profile.L),
        "defect_shape_coefficient_counts": (
            len(defects), len(shapes), len(coefficients)),
        "fixed_r_s_q_chain_count": len(chains),
        "chain_length_range": (
            min(length_histogram), max(length_histogram)),
        "chain_length_histogram": tuple(sorted(length_histogram.items())),
        "multirow_chain_count": len(records),
        "transpose_formula": (
            "mu_k=sum_(y in Y,y<=k) binom(k,y) W^(k-y) lambda_y"),
        "terminal_null_vector_formula": (
            "lambda_a=(T-a), lambda_(a+1)=-(a+1)W"),
        "first_step_defect_formula": (
            "mu_(a+1)-W*mu_a=(a*(T-a-1)-1)*W"),
        "all_multirow_terminal_null_vectors_have_nonzero_first_step_defect_mod_p":
            True,
        "defect_integer_range": (
            min(record[6][2] for record in records),
            max(record[6][2] for record in records)),
        "literal_chain_r_s_q": literal_key,
        "literal_chain_receipt": literal,
        "literal_terminal_binomials": (comb(94, 41), comb(94, 42)),
        "common_normalized_hasse_scalar_mod_p": pow(profile.N, 26, P),
        "literal_reciprocal_monomial_terminal_rank": monomial_terminal_rank,
        "record_stream_sha256": stream.hexdigest(),
        "decision": "RED_FIXED_LAMBDA_RECURRENCE_EVEN_WITH_TERMINAL_CANCELLATION",
        "scope": (
            "exact literal Pascal transpose and terminal row; does not claim "
            "a nonzero annihilator of all ordinary source prefixes"),
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
