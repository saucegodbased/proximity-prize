#!/usr/bin/env python3
"""Exact combinatorial closure of the Full187 sharp order-two pivots.

For every distinct locally-pivoted contact row occurring in the conservative
103-shape terminal face (all surviving coefficient-Hasse orders), expand the
literal leading-basis polynomial

  Z^k * (E + ZR - Z^2 S/2)^a0
      * R^b * (E - Z^2 S/2)^rho * E^e * S^(min(h,t)-e).

The leading monomial is the pivot used by ``Order2FullLayerLeading6900``.
Every other monomial has larger shifted contact weight.  This audit asks the
next essential question: is every surviving remainder monomial itself
admissible as another sharp pivot?  It deliberately does not infer global
coefficientwise confluence or packet containment from support closure.
"""

from __future__ import annotations

from collections import Counter, deque
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import resource

import full187_terminal_lowT_hasse_closure_audit_6900 as H


M = H.M
J = H.J
SLOPE = H.SLOPE
CURVATURE = H.CURVATURE
ERRORS = H.ERRORS


def pivot_parameters(row):
    """Return the canonical sharp-basis indices, or ``None``."""
    T, E, R, S, seed = row
    d = E + R + S
    rho = max(E + S - CURVATURE, 0)
    a0 = max(0, d - SLOPE)
    upper = min(R, T - 2 * rho)
    if a0 > upper or E > min(E + S, CURVATURE) or d > J:
        return None
    q_source = d - a0
    b = R - a0
    k = T - a0 - 2 * rho
    h = E + S
    assert q_source <= SLOPE
    assert b <= q_source
    assert E <= min(h, CURVATURE)
    assert min(k, a0, h, b, E, seed) >= 0
    return (a0, h, b, E, k, seed)


def multinomial3(n, i, j, k):
    assert i + j + k == n
    return factorial(n) // (factorial(i) * factorial(j) * factorial(k))


def basis_support(row):
    """Exact exponent/coefficient support over the benchmark prime.

    Exponents are ``(T,E,R,S,seed)``.  Coefficients are retained only to
    ensure that no combinatorial term accidentally vanishes in the target
    characteristic; closure itself depends on support.
    """
    params = pivot_parameters(row)
    assert params is not None
    a0, h, b, e, k, seed = params
    rho = h - min(h, CURVATURE)
    support = {}
    inv2 = pow(2, -1, 2_130_706_433)
    prime = 2_130_706_433
    # iE+iR+iS=a0 expands contactY^a0.  j is the number of E
    # choices in (E-Z^2 S/2)^rho.
    for iE in range(a0 + 1):
        for iR in range(a0 - iE + 1):
            iS = a0 - iE - iR
            cy = multinomial3(a0, iE, iR, iS)
            cy = cy * pow(-inv2 % prime, iS, prime) % prime
            for j in range(rho + 1):
                cu = comb(rho, j) * pow(-inv2 % prime, rho - j, prime)
                coefficient = cy * cu % prime
                exponent = (
                    k + iR + 2 * iS + 2 * (rho - j),
                    e + iE + j,
                    b + iR,
                    min(h, CURVATURE) - e + iS + rho - j,
                    seed,
                )
                support[exponent] = (support.get(exponent, 0) + coefficient) % prime
    support = {exponent: coefficient for exponent, coefficient in support.items()
               if coefficient}
    assert row in support
    assert support[row]
    pivot_weight = row[0] + 3 * row[1]
    assert all(exponent == row or exponent[0] + 3 * exponent[1] > pivot_weight
               for exponent in support)
    return support


def initial_rows():
    shapes = tuple(
        (r, s) for s in range(CURVATURE + 1)
        for r in range(SLOPE - s + 1)
        if H.compact_affine_free_shape(r, s)
    )
    rows = set()
    origin_count = 0
    for r, s in shapes:
        y = J - r - s
        for f in range(M):
            assert f <= y
            for a_e in range(f + 1):
                for c_s in range(f - a_e + 1):
                    base = f + 2 * a_e + c_s
                    if base >= M:
                        continue
                    for q in range(M - base):
                        status, row, _margin = H.origin_status(
                            r, s, f, a_e, c_s, q, ERRORS)
                        if status == "pivot":
                            origin_count += 1
                            rows.add(row)
    assert origin_count == 21_049 + 49_007
    return rows, origin_count


def main():
    roots, origin_count = initial_rows()
    queue = deque(sorted(roots))
    seen = set(roots)
    edge_count = 0
    truncated_count = 0
    escaping = set()
    escape_reasons = Counter()
    support_sizes = Counter()
    weight_jumps = Counter()

    while queue:
        row = queue.popleft()
        support = basis_support(row)
        support_sizes[len(support)] += 1
        weight = row[0] + 3 * row[1]
        for successor in support:
            if successor == row:
                continue
            successor_weight = successor[0] + 3 * successor[1]
            weight_jumps[successor_weight - weight] += 1
            if successor_weight >= M:
                truncated_count += 1
                continue
            edge_count += 1
            if pivot_parameters(successor) is None:
                escaping.add(successor)
                T, E, R, S, _seed = successor
                d = E + R + S
                rho = max(E + S - CURVATURE, 0)
                a0 = max(0, d - SLOPE)
                if E > min(E + S, CURVATURE):
                    escape_reasons["E exceeds curvature basis cap"] += 1
                elif d > J:
                    escape_reasons["derivative total exceeds active cap"] += 1
                elif T < a0 + 2 * rho:
                    escape_reasons["low-T sharp-pivot inequality"] += 1
                elif R < a0:
                    escape_reasons["R below active-overflow requirement"] += 1
                else:
                    escape_reasons["other"] += 1
                continue
            if successor not in seen:
                seen.add(successor)
                queue.append(successor)

    stable = {
        "scope": (
            "target-parameter exponent closure of exact sharp order-two "
            "basis remainders from every all-Hasse pivot row in the strong "
            "103-shape terminal face; no coefficientwise or packet claim"
        ),
        "target_m_J_slope_curvature": (M, J, SLOPE, CURVATURE),
        "initial_pivot_origins_and_distinct_rows": (origin_count, len(roots)),
        "transitive_pivot_row_count": len(seen),
        "nontruncated_successor_edge_count": edge_count,
        "truncated_successor_term_count": truncated_count,
        "escaping_nonpivot_successor_count": len(escaping),
        "escaping_nonpivot_successor_edge_reasons": tuple(
            sorted(escape_reasons.items())),
        "first_32_escaping_nonpivot_successors": tuple(sorted(escaping)[:32]),
        "basis_support_size_min_max_and_distinct_sizes": (
            min(support_sizes), max(support_sizes), len(support_sizes)),
        "basis_rows_and_expansion_terms": (
            sum(support_sizes.values()),
            sum(size * count for size, count in support_sizes.items())),
        "strict_weight_jump_min_max_and_edge_count": (
            min(weight_jumps), max(weight_jumps), sum(weight_jumps.values())),
        "decision": (
            "GREEN_PIVOT_REMAINDERS_CLOSE_BY_STRICT_WEIGHT"
            if not escaping else "RED_PIVOT_REMAINDERS_ESCAPE_LOCAL_BASIS"
        ),
        "scope_guard": (
            "Even a GREEN result proves only finite exponent closure.  The "
            "external-X multiplier bounds, Hermite tails, passive recurrence, "
            "and four atomic packet columns must still be propagated."
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
