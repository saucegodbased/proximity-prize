#!/usr/bin/env python3
"""Deterministic edge-stratum discriminator for the lifted K0 t=7 packet.

The actual target bridge gives only
``valuation_q(g(q, gamma)) <= M-1``.  This script tests the hardest equality
case.  It first pins a faithful K=2 counterexample, then exhausts a structured
family at K=3.  All ranks are exact over F_101; this remains a falsifier, not
a uniform theorem.
"""

from __future__ import annotations

from flint import nmod_mat


P = 101


def ranks(g, *, over: int, m: int, k: int, alpha: int, gamma: int):
    qrows = m + over + 1
    zrows = k + 2
    cols = 4 * (m + 1) * (k + 1)
    base = qrows * zrows
    entries = [[0] * cols for _ in range(base + 4)]

    def col(i: int, qr: int, zr: int) -> int:
        return (i * (m + 1) + qr) * (k + 1) + zr

    def row(qr: int, zr: int) -> int:
        return qr * zrows + zr

    for aq in range(m + 1):
        for az in range(k + 1):
            for r, pair in enumerate(g):
                for gz, gv in enumerate(pair):
                    if not gv:
                        continue
                    if aq + 1 + r < qrows:
                        entries[row(aq + 1 + r, az + gz)][
                            col(0, aq, az)] = -gv % P
                    if aq + 2 + r < qrows:
                        entries[row(aq + 2 + r, az + gz)][
                            col(1, aq, az)] = -(r + 1) * gv % P
                    if aq + 3 + r < qrows:
                        entries[row(aq + 3 + r, az + gz)][
                            col(2, aq, az)] = -(r + 1) * (r + 2) * gv % P
            entries[row(aq, az + 1)][col(3, aq, az)] = 1

            xval = pow(alpha, m - aq, P)
            zval = pow(gamma, az, P)
            value = xval * zval % P
            entries[base + 0][col(0, aq, az)] = value
            entries[base + 1][col(1, aq, az)] = value
            entries[base + 2][col(2, aq, az)] = value
            entries[base + 3][col(3, aq, az)] = (az + 1) * value % P

    top = nmod_mat(entries[:base], P).rank()
    joint = nmod_mat(entries, P).rank()
    return top, joint, joint - top


def pinned_regression():
    g = [[0, 0] for _ in range(10)]
    g[3] = [56, 85]
    g[4] = [77, 0]
    g[5] = [16, 0]
    g[6] = [0, 15]
    assert (g[3][0] + 18 * g[3][1]) % P != 0
    out = {
        k: ranks(g, over=5, m=4, k=k, alpha=89, gamma=18)
        for k in range(6)
    }
    assert out[2][2] == 3
    assert out[3][2] == 4
    return out


def structured_edge_sweep():
    m, over, k = 4, 5, 3
    qrows = m + over + 1
    first = m - 1
    values = (1, 2, -1 % P)
    tested = 0
    failures = []

    # Prefix coefficients lie on the affine line killed by evaluation at
    # gamma.  The coefficient at `first` is normalized to scalar value one.
    # One later coefficient probes every support position and both channels.
    for gamma in range(1, 6):
        for alpha in range(1, 6):
            for prefix in range(first):
                for prefix_value in values:
                    for leading_z in (0, 1, 2, -1 % P):
                        leading = [
                            (1 - gamma * leading_z) % P,
                            leading_z,
                        ]
                        for suffix in range(first + 1, qrows):
                            for channel in range(2):
                                for suffix_value in values:
                                    g = [[0, 0] for _ in range(qrows)]
                                    g[prefix] = [
                                        (-gamma * prefix_value) % P,
                                        prefix_value,
                                    ]
                                    g[first] = leading
                                    g[suffix][channel] = suffix_value
                                    assert all(
                                        (a + gamma * b) % P == 0
                                        for a, b in g[:first]
                                    )
                                    assert (
                                        g[first][0] + gamma * g[first][1]
                                    ) % P == 1
                                    tested += 1
                                    receipt = ranks(
                                        g,
                                        over=over,
                                        m=m,
                                        k=k,
                                        alpha=alpha,
                                        gamma=gamma,
                                    )
                                    if receipt[2] < 4:
                                        failures.append(
                                            (gamma, alpha, prefix,
                                             prefix_value, leading_z,
                                             suffix, channel, suffix_value,
                                             receipt)
                                        )
    assert not failures
    return {"tested": tested, "failures": len(failures)}


def main():
    print({"pinned_passive_degree_regression": pinned_regression()})
    print({"structured_k3_edge_sweep": structured_edge_sweep()})


if __name__ == "__main__":
    main()
