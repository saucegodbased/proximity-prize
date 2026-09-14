#!/usr/bin/env python3
"""Small exact controls for the geometric-dual sign/Pade obstruction.

For a cyclic domain H of order P, the constant geometric ratio A=B=1 asks
for a reduced rational word W=N/E with W(x)^2=1 on H.  This exhausts every
sign word for P=16 and searches degree-1 denominators whose cyclic product
has numerator degree at most 9, the smallest faithful analogue of the m69
high-numerator regime.  It distinguishes the obvious half-period monomial
solutions (which retain E as a common factor) from genuinely reduced ones.

This is a falsification control, not evidence for the full P=262144 theorem.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import itertools
import json
import resource


MOD = 97
ORDER = 16
E_DEG = 1
N_CAP = 9


def inv(a: int) -> int:
    return pow(a % MOD, MOD - 2, MOD)


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] % MOD == 0:
        a.pop()
    return tuple(x % MOD for x in a)


def degree(a):
    return len(trim(a)) - 1


def poly_divmod(a, b):
    a, b = list(trim(a)), trim(b)
    assert b != (0,)
    q = [0] * max(1, len(a) - len(b) + 1)
    ib = inv(b[-1])
    while len(a) >= len(b) and any(a):
        k = len(a) - len(b)
        c = a[-1] * ib % MOD
        q[k] = c
        for j, bj in enumerate(b):
            a[k + j] = (a[k + j] - c * bj) % MOD
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    return trim(q), trim(a)


def gcd(a, b):
    a, b = trim(a), trim(b)
    while b != (0,):
        _, r = poly_divmod(a, b)
        a, b = b, r
    if a == (0,):
        return a
    scale = inv(a[-1])
    return trim(tuple(scale * x % MOD for x in a))


def primitive_root():
    for g in range(2, MOD):
        if pow(g, (MOD - 1) // 2, MOD) != 1 and pow(g, (MOD - 1) // 3, MOD) != 1:
            return g
    raise AssertionError


GEN = primitive_root()
OMEGA = pow(GEN, (MOD - 1) // ORDER, MOD)
NODES = tuple(pow(OMEGA, i, MOD) for i in range(ORDER))
assert len(set(NODES)) == ORDER and pow(OMEGA, ORDER // 2, MOD) == MOD - 1


def interpolate(values):
    # Inverse DFT on the full cyclic domain: c_k=P^-1 sum_i v_i*x_i^-k.
    pinv = inv(ORDER)
    return tuple(
        pinv * sum(values[i] * pow(NODES[i], (-k) % ORDER, MOD)
                   for i in range(ORDER)) % MOD
        for k in range(ORDER)
    )


def cyclic_mul_linear(s, e0, e1):
    out = [0] * ORDER
    for k, sk in enumerate(s):
        out[k] = (out[k] + e0 * sk) % MOD
        out[(k + 1) % ORDER] = (out[(k + 1) % ORDER] + e1 * sk) % MOD
    return tuple(out)


def kernel_vectors(rows):
    # Nullspace of a matrix with exactly two columns, projectively enumerated.
    answers = []
    for e0, e1 in [(1, t) for t in range(MOD)] + [(0, 1)]:
        if all((a * e0 + b * e1) % MOD == 0 for a, b in rows):
            answers.append((e0, e1))
    return tuple(answers)


def main():
    # Before enumerating square-root sign words, exhaust every pair of monic
    # linear A,B which is nonzero on the cyclic domain.  In this control the
    # condition B(x)/A(x) is a square at every node already forces A=B.
    linear = tuple((a, 1) for a in range(MOD)
                   if all((a + x) % MOD != 0 for x in NODES))
    square_linear_ratios = []
    for A in linear:
        for B in linear:
            if all(pow((B[0] + x) * inv(A[0] + x) % MOD,
                       (MOD - 1) // 2, MOD) == 1 for x in NODES):
                square_linear_ratios.append((A, B))
    assert len(linear) == 81
    assert len(square_linear_ratios) == 81
    assert all(A == B for A, B in square_linear_ratios)

    histogram = Counter()
    genuine = []
    receipts = []
    for bits in itertools.product((1, MOD - 1), repeat=ORDER):
        s = interpolate(bits)
        rows = tuple((s[k], s[(k - 1) % ORDER])
                     for k in range(N_CAP + 1, ORDER))
        kernels = kernel_vectors(rows)
        if not kernels:
            histogram["no_degree1_pade"] += 1
            continue
        histogram["has_degree1_pade"] += 1
        for e0, e1 in kernels:
            if e1 == 0:
                histogram["constant_denominator"] += 1
                continue
            E = trim((e0, e1))
            if any((e0 + e1 * x) % MOD == 0 for x in NODES):
                histogram["denominator_domain_root"] += 1
                continue
            N = trim(cyclic_mul_linear(s, e0, e1)[:N_CAP + 1])
            assert degree(N) <= N_CAP
            g = gcd(E, N)
            receipts.append((bits, E, degree(N), g))
            if degree(g) == 0:
                genuine.append((bits, s, E, N))
                histogram["reduced_counterexample"] += 1
            else:
                histogram["common_factor_only"] += 1

    # Every nonconstant, domain-root-free denominator which passes the Padé
    # support gate retains a polynomial common factor.  There are more than
    # the two pure half-period characters because the numerator cap leaves
    # one scaled degree of slack; none is a reduced rational counterexample.
    assert not genuine
    assert histogram == Counter({
        "no_degree1_pade": 65_468,
        "common_factor_only": 324,
        "denominator_domain_root": 128,
        "has_degree1_pade": 68,
        "constant_denominator": 4,
    })
    assert histogram["reduced_counterexample"] == 0
    result = {
        "field_modulus": MOD,
        "domain_order": ORDER,
        "denominator_exact_degree": E_DEG,
        "numerator_degree_cap": N_CAP,
        "sign_words_exhausted": 2 ** ORDER,
        "domain_root_free_monic_linear_polynomials": len(linear),
        "ordered_linear_ratios_exhausted": len(linear) ** 2,
        "linear_ratios_square_on_every_node": len(square_linear_ratios),
        "every_everywhere_square_linear_ratio_is_constant": True,
        "histogram": sorted(histogram.items()),
        "reduced_counterexamples": 0,
        "conclusion": (
            "in this exact small control, every nonconstant-denominator "
            "solution of W^2=1 retains the denominator as a common factor"
        ),
        "receipt_sha256": hashlib.sha256(repr(tuple(receipts)).encode()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
