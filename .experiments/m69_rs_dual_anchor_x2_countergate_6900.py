#!/usr/bin/env python3
"""Exact finite-field countergate for the spurious X^2 dual recurrence.

For the ordinary evaluation prefix F_<f on a full roots-of-unity domain, an
annihilator word has the fixed representation lambda(x)=x*H(x), independent
of f.  Therefore multiplying a source channel by W=N/E yields

    N*H_t = E*H_(t+1)

at the nodes, and two steps yield N^2*H_t=E^2*H_(t+2).  There is no X^2.

The tiny witness below is itself a simultaneous annihilator of three cyclic
prefix channels and satisfies the no-X recurrence while falsifying the X^2
variant used in the old conditional m69 lemmas.
"""

import hashlib
import json
import resource

P = 97
ORDER = 16


def primitive_root():
    for g in range(2, P):
        if pow(g, 48, P) != 1 and pow(g, 32, P) != 1:
            return g
    raise AssertionError


g = primitive_root()
omega = pow(g, (P - 1) // ORDER, P)
nodes = tuple(pow(omega, i, P) for i in range(ORDER))
assert len(set(nodes)) == ORDER


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % P


def ev_monomial(k):
    return tuple(pow(x, k % ORDER, P) for x in nodes)


def pointwise(a, b):
    return tuple(x * y % P for x, y in zip(a, b))


def main():
    # W=X^-1, E=X, N=1.  With three equal F_<8 channels their cyclic
    # supports are [0,7], [-1,6], [-2,5].  lambda=X^3 has Fourier mate 13,
    # outside their union, so it annihilates every channel.
    lam = ev_monomial(3)
    W = ev_monomial(-1)
    for t in range(3):
        lw = pointwise(lam, ev_monomial(-t))
        assert all(dot(lw, ev_monomial(k)) == 0 for k in range(8))

    # lambda*W^t = X*H_t with H_0=X^2,H_1=X,H_2=1.
    H = (ev_monomial(2), ev_monomial(1), ev_monomial(0))
    E = ev_monomial(1)
    N = ev_monomial(0)
    X2 = ev_monomial(2)
    assert lam == pointwise(ev_monomial(1), H[0])
    assert pointwise(lam, W) == pointwise(ev_monomial(1), H[1])
    assert pointwise(pointwise(lam, W), W) == pointwise(ev_monomial(1), H[2])
    assert pointwise(N, H[0]) == pointwise(E, H[1])
    assert pointwise(N, H[1]) == pointwise(E, H[2])
    assert pointwise(pointwise(N, N), H[0]) == pointwise(pointwise(E, E), H[2])

    wrong_rhs = pointwise(X2, pointwise(pointwise(E, E), H[2]))
    assert pointwise(pointwise(N, N), H[0]) != wrong_rhs
    bad_nodes = tuple(i for i in range(ORDER)
                      if H[0][i] != wrong_rhs[i])
    assert len(bad_nodes) == 14
    stable = {
        "field": P,
        "domain_order": ORDER,
        "source": "F_<8 + X^-1 F_<8 + X^-2 F_<8",
        "annihilator": "lambda=X^3",
        "fixed_dual_anchor": "lambda*W^t = X*H_t",
        "H_sequence": ["X^2", "X", "1"],
        "correct_relations": ["N*H0=E*H1", "N*H1=E*H2",
                              "N^2*H0=E^2*H2"],
        "old_X2_relation": "N^2*H0=X^2*E^2*H2",
        "old_X2_relation_false_node_count": len(bad_nodes),
        "decision": "X2_RECURRENCE_RED__NO_X_RECURRENCE_GREEN",
    }
    canonical = json.dumps(stable, sort_keys=True, separators=(",", ":"))
    print(json.dumps({
        **stable,
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
