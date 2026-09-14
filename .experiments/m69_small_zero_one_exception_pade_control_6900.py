#!/usr/bin/env python3
"""Exhaust the first exceptional-node analogue of the small-zero Padé gate.

On the order-16 domain over F_97, prescribe W=±1 at 15 nodes and leave one
node arbitrary.  Exhaust all 2^15 sign patterns and solve, rather than sample,
for every degree-1 denominator E such that N=(E*W mod X^16-1) has degree at
most 9.  A reduced solution would be the smallest model of the geometric
chain with a nonconstant common kernel factor C vanishing at one domain node.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import itertools
import json
import resource

import m69_small_zero_sign_pade_control_6900 as base

P, ORDER, N_CAP = base.MOD, base.ORDER, base.N_CAP
NODES = base.NODES


def inv(a):
    return pow(a % P, P - 2, P)


def rref_nullspace(matrix):
    a = [list(x % P for x in row) for row in matrix]
    rows, cols = len(a), len(a[0])
    pivots = []
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = inv(a[r][c])
        a[r] = [z * x % P for x in a[r]]
        for i in range(rows):
            if i != r and a[i][c]:
                z = a[i][c]
                a[i] = [(x - z * y) % P for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = [0] * cols
        v[f] = 1
        for i, c in enumerate(pivots):
            v[c] = -a[i][f] % P
        basis.append(tuple(v))
    return tuple(basis)


def projective_vectors(basis):
    d = len(basis)
    if d == 0:
        return
    # Normalize the first nonzero basis coefficient to one.
    for first in range(d):
        for tail in itertools.product(range(P), repeat=d - first - 1):
            coeffs = (0,) * first + (1,) + tail
            yield tuple(sum(coeffs[j] * basis[j][k] for j in range(d)) % P
                        for k in range(4))


def main():
    omitted = 0  # node 1; cyclic symmetry makes this the canonical control.
    pinv = inv(ORDER)
    delta = (pinv,) * ORDER
    hist = Counter()
    reduced = []
    accepted_receipt = []

    for signs in itertools.product((1, P - 1), repeat=ORDER - 1):
        values = (0,) + signs
        s0 = base.interpolate(values)
        rows = []
        for k in range(N_CAP + 1, ORDER):
            rows.append((s0[k], s0[(k - 1) % ORDER],
                         delta[k], delta[(k - 1) % ORDER]))
        basis = rref_nullspace(rows)
        hist[f"nullity_{len(basis)}"] += 1
        for e0, e1, e0u, e1u in projective_vectors(basis):
            if e0 == 0 and e1 == 0:
                continue
            if e0:
                u = e0u * inv(e0) % P
                if e1u != e1 * u % P:
                    continue
            else:
                if e0u:
                    continue
                u = e1u * inv(e1) % P
            hist["bilinear_solutions"] += 1
            if e1 == 0:
                hist["constant_denominator"] += 1
                continue
            if any((e0 + e1 * x) % P == 0 for x in NODES):
                hist["denominator_domain_root"] += 1
                continue
            s = tuple((s0[k] + u * delta[k]) % P for k in range(ORDER))
            full_n = base.cyclic_mul_linear(s, e0, e1)
            assert all(full_n[k] == 0 for k in range(N_CAP + 1, ORDER))
            E = base.trim((e0, e1))
            N = base.trim(full_n[:N_CAP + 1])
            common = base.gcd(E, N)
            accepted_receipt.append((signs, u, E, N, common))
            if base.degree(common) == 0:
                hist["reduced_counterexample"] += 1
                reduced.append((signs, u, E, N))
            else:
                hist["common_factor_only"] += 1

    result = {
        "field_modulus": P,
        "domain_order": ORDER,
        "omitted_node_index": omitted,
        "prescribed_sign_nodes": ORDER - 1,
        "sign_patterns_exhausted": 2 ** (ORDER - 1),
        "denominator_exact_degree": 1,
        "numerator_degree_cap": N_CAP,
        "histogram": sorted(hist.items()),
        "reduced_counterexample_count": len(reduced),
        "first_reduced_counterexample": reduced[:1],
        "receipt_sha256": hashlib.sha256(
            repr(tuple(accepted_receipt)).encode()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
