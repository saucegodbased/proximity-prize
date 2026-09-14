#!/usr/bin/env python3
"""Exact Hasse-weight audit for every direct m69 predecessor channel.

The cyclic-interval gate models the free tail of a source polynomial as a
coefficient prefix.  That is exact only if taking the required Hasse jet of

    (X^N - 1)^depth * X^j

has nonzero weight for every coefficient exponent in that prefix.  This file
checks the issue over the literal benchmark prime, rather than assuming it.

After evaluation at an N-th root and multiplication by the harmless monomial
X^q, the coefficient-basis weight is

    [z^q] (((1+z)^N - 1)^depth * (1+z)^j).

Dividing by the nonzero scalar N^depth and putting k=q-depth gives the
degree-k polynomial in j

    [z^k] A(z)^depth * (1+z)^j,
    A(z)=((1+z)^N-1)/(N*z).

python-flint factors this polynomial exactly over the target prime and lists
all of its field roots.  We require that none is an integer 0 <= j < N.  The
gate checks a superset of the physical census: every 1 <= depth <= 47 and
depth <= q <= 68, then reconnects those facts to every deficient physical
coefficient and every available higher-contact predecessor.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path
import resource

from flint import nmod_poly

import m69_reciprocal_all_defect_interval_gate_6900 as M69


P = 2_130_706_433
N = M69.N
MAX_Q = M69.M - 1
MAX_DEPTH = M69.D // N


def binomial_polynomials():
    """Return the polynomials binom(x,t), 0 <= t <= MAX_Q."""
    x = nmod_poly([0, 1], P)
    answer = [nmod_poly([1], P)]
    for t in range(1, MAX_Q + 1):
        answer.append(answer[-1] * (x - (t - 1)) * pow(t, -1, P))
    return tuple(answer)


def normalized_factor_polynomial():
    """A(z)=((1+z)^N-1)/(N*z), truncated above degree MAX_Q."""
    inverse_n = pow(N, -1, P)
    coefficients = [comb(N, r + 1) % P * inverse_n % P
                    for r in range(MAX_Q + 1)]
    return nmod_poly(coefficients, P)


def weight_polynomial(depth, q, binomials, normalized_factor):
    """Polynomial in j for the normalized (depth,q) Hasse weight."""
    assert 1 <= depth <= q <= MAX_Q
    k = q - depth
    factor_power = (normalized_factor ** depth).truncate(k + 1)
    answer = nmod_poly([], P)
    for t in range(k + 1):
        answer += binomials[t] * int(factor_power[k - t])
    assert answer.degree() == k
    return answer


def exact_all_pair_root_gate():
    binomials = binomial_polynomials()
    normalized_factor = normalized_factor_polynomial()
    receipts = []
    root_count = 0
    maximum_root_multiplicity = 0
    for depth in range(1, MAX_DEPTH + 1):
        for q in range(depth, MAX_Q + 1):
            polynomial = weight_polynomial(
                depth, q, binomials, normalized_factor)
            roots = tuple((int(root), multiplicity)
                          for root, multiplicity in polynomial.roots())
            root_count += len(roots)
            maximum_root_multiplicity = max(
                maximum_root_multiplicity,
                max((multiplicity for _root, multiplicity in roots),
                    default=0))
            assert all(not 0 <= root < N for root, _multiplicity in roots)
            receipts.append((
                depth, q, polynomial.degree(),
                tuple(int(polynomial[index])
                      for index in range(polynomial.degree() + 1)),
                roots,
            ))
    assert len(receipts) == 2_115
    return tuple(receipts), {
        "audited_depth_q_pair_count": len(receipts),
        "audited_depth_range": (1, MAX_DEPTH),
        "audited_q_range": (1, MAX_Q),
        "total_distinct_field_root_entries": root_count,
        "maximum_field_root_multiplicity": maximum_root_multiplicity,
        "no_weight_polynomial_has_a_root_at_an_integer_0_le_j_lt_N": True,
        "all_weight_polynomial_receipts_sha256": hashlib.sha256(
            repr(tuple(receipts)).encode()).hexdigest(),
    }


def physical_channel_gate():
    _defects, _shapes, coefficients = M69.defect_census()
    channel_count = 0
    channel_digest = hashlib.sha256()
    used_pairs = set()
    powers = Counter()
    for y, r, s, q in coefficients:
        for power in range(M69.M - y):
            source_y = y + power
            width = M69.width(source_y, r, s)
            assert width > 0
            depth, fringe = divmod(width, N)
            assert 1 <= depth <= q <= MAX_Q
            assert 0 < fringe < N
            scalar = comb(source_y, y) % P
            assert scalar != 0
            used_pairs.add((depth, q))
            powers[power] += 1
            record = (y, r, s, q, power, source_y,
                      depth, fringe, scalar)
            channel_digest.update(repr(record).encode())
            channel_digest.update(b"\n")
            channel_count += 1
    assert len(coefficients) == 140_153
    assert len(used_pairs) == 2_010
    return {
        "rank_insensitive_deficient_coefficient_count": len(coefficients),
        "physical_direct_predecessor_channel_count": channel_count,
        "physical_depth_q_pair_count": len(used_pairs),
        "physical_depth_q_pairs_are_covered_by_the_superset_gate": True,
        "every_channel_has_q_at_least_preserved_depth": True,
        "every_pascal_source_scalar_is_nonzero": True,
        "power_channel_histogram": tuple(sorted(powers.items())),
        "physical_channel_stream_sha256": channel_digest.hexdigest(),
    }


def main():
    receipts, root_gate = exact_all_pair_root_gate()
    physical = physical_channel_gate()
    stable = {
        "target_prime_N_M_max_depth": (P, N, M69.M, MAX_DEPTH),
        "normalized_weight_formula": (
            "N^(-depth)*[z^q](((1+z)^N-1)^depth*(1+z)^j)="
            "[z^(q-depth)]A(z)^depth*(1+z)^j"
        ),
        "all_pair_root_gate": root_gate,
        "physical_channel_gate": physical,
        "decision": "GREEN_ALL_M69_DIRECT_PREFIX_WEIGHTS_NONZERO",
        "scope": (
            "repairs the coefficient-weight assumption in the direct m69 "
            "prefix model; does not prove arbitrary-rational rank or "
            "simultaneous allocation/confluence"
        ),
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    payload = {
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
