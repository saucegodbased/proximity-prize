#!/usr/bin/env python3
"""Finite-field rank probe for the K0 order-seven bivariate approximant.

This is deliberately a small symbolic model.  At infinity, for
N = X^n - 1 and U = U0 + U1 Z, put q = X^-1 and

  g(q,Z) = sum_{r>=1} u_{n-r}(Z) q^(r-1).

After removing their exact X powers, the data faces of J,C1,C2 are

  j  = -g,
  c1 = -(theta+1)g,
  c2 = -(theta+1)(theta+2)g.

The eight order-seven covariants are j^a c1^b c2^c with
a+2b+3c=7.  Coefficients have q degree <= m (equivalently X degree
<= m) and Z degree <= k.  The script computes the rank of cancellation
through q^(m+gap-1), then the extra rank contributed by four literal
fresh-boundary gradient rows.  An increment of four means the tested
approximant kernel still maps onto all four boundary directions.

The model is exact over a prime field, but random specialization is only a
discriminator; a positive result still needs a uniform proof for the actual
U0/U1 data.
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass

from flint import nmod_mat


P = 1_000_003
PROFILES = ((7, 0, 0), (5, 1, 0), (3, 2, 0), (1, 3, 0),
            (4, 0, 1), (2, 1, 1), (0, 2, 1), (1, 0, 2))


def add(a, b, qcap, zcap):
    out = [[0] * (zcap + 1) for _ in range(qcap)]
    for q in range(qcap):
        for z in range(zcap + 1):
            out[q][z] = (a[q][z] + b[q][z]) % P
    return out


def mul(a, b, qcap, zcap):
    out = [[0] * (zcap + 1) for _ in range(qcap)]
    for qa, ar in enumerate(a):
        for za, av in enumerate(ar):
            if not av:
                continue
            for qb in range(qcap - qa):
                br = b[qb]
                for zb in range(zcap + 1 - za):
                    bv = br[zb]
                    if bv:
                        out[qa + qb][za + zb] = (
                            out[qa + qb][za + zb] + av * bv) % P
    return out


def power(a, e, qcap, zcap):
    out = [[0] * (zcap + 1) for _ in range(qcap)]
    out[0][0] = 1
    base = a
    while e:
        if e & 1:
            out = mul(out, base, qcap, zcap)
        e >>= 1
        if e:
            base = mul(base, base, qcap, zcap)
    return out


def scale_theta(g, offset, qcap, zcap):
    # q^r corresponds to the original U coefficient at distance r+1.
    out = [[0] * (zcap + 1) for _ in range(qcap)]
    for q in range(qcap):
        scalar = q + offset
        for z in range(zcap + 1):
            out[q][z] = scalar * g[q][z] % P
    return out


def generators(rng, qcap):
    # g is affine in Z.  Force both top coefficients nonzero.
    g = [[0] * 8 for _ in range(qcap)]
    for q in range(qcap):
        g[q][0] = rng.randrange(1 if q == 0 else 0, P)
        g[q][1] = rng.randrange(1 if q == 0 else 0, P)
    j = [[(-x) % P for x in row] for row in g]
    c1 = [[(-x) % P for x in row]
          for row in scale_theta(g, 1, qcap, 7)]
    tmp = scale_theta(g, 2, qcap, 7)
    c2 = [[(-x) % P for x in row]
          for row in scale_theta(tmp, 1, qcap, 7)]
    ans = []
    for a, b, c in PROFILES:
        f = power(j, a, qcap, 7)
        f = mul(f, power(c1, b, qcap, 7), qcap, 7)
        f = mul(f, power(c2, c, qcap, 7), qcap, 7)
        ans.append(f)
    return ans


def monomial_value_gradient(a, b, c, j, c1, c2, dj, dc1, dc2):
    val = pow(j, a, P) * pow(c1, b, P) * pow(c2, c, P) % P
    grad = [0] * 4
    if a:
        scalar = a * pow(j, a - 1, P) * pow(c1, b, P) * pow(c2, c, P)
        for h in range(4):
            grad[h] += scalar * dj[h]
    if b:
        scalar = b * pow(j, a, P) * pow(c1, b - 1, P) * pow(c2, c, P)
        for h in range(4):
            grad[h] += scalar * dc1[h]
    if c:
        scalar = c * pow(j, a, P) * pow(c1, b, P) * pow(c2, c - 1, P)
        for h in range(4):
            grad[h] += scalar * dc2[h]
    return val, [x % P for x in grad]


def build_matrix(seed, gap, m, k, include_boundary):
    rng = random.Random(seed)
    qcap = m + gap
    fs = generators(rng, qcap)
    out_z = k + 7
    a_rows = qcap * (out_z + 1)
    cols = 8 * (m + 1) * (k + 1)
    extra = 4 if include_boundary else 0
    entries = [[0] * cols for _ in range(a_rows + extra)]

    def col(i, qr, zs):
        return (i * (m + 1) + qr) * (k + 1) + zs

    def row(qr, zs):
        return qr * (out_z + 1) + zs

    for i, f in enumerate(fs):
        for aq in range(m + 1):
            for az in range(k + 1):
                cc = col(i, aq, az)
                for fq in range(qcap - aq):
                    for fz in range(8):
                        if az + fz <= out_z and f[fq][fz]:
                            entries[row(aq + fq, az + fz)][cc] = f[fq][fz]

    if include_boundary:
        # Literal triangular gradients for (S,Y,R,Z), with random legal data.
        alpha = rng.randrange(1, P)
        zeta = rng.randrange(1, P)
        n0 = rng.randrange(1, P)
        n1 = rng.randrange(P)
        pp = rng.randrange(P)
        b0, b1, b2 = (rng.randrange(P) for _ in range(3))
        j0, c10, c20 = (rng.randrange(1, P) for _ in range(3))
        dj = [0, 1, 0, -b0]
        dc1 = [0, n1, -n0, b1]
        dc2 = [2 * n0 * n0 % P, pp, -2 * n0 * n1 % P, b2]
        vals_grads = [monomial_value_gradient(*prof, j0, c10, c20,
                                               dj, dc1, dc2)
                      for prof in PROFILES]
        # Unknown reverse coefficient aq is original X^(m-aq) Z^az.
        for i, (gv, gg) in enumerate(vals_grads):
            for aq in range(m + 1):
                xeval = pow(alpha, m - aq, P)
                for az in range(k + 1):
                    cc = col(i, aq, az)
                    peval = xeval * pow(zeta, az, P) % P
                    dpz = (az * xeval * pow(zeta, az - 1, P)) % P if az else 0
                    for h in range(4):
                        v = peval * gg[h]
                        if h == 3:
                            v += dpz * gv
                        entries[a_rows + h][cc] = v % P
    return nmod_mat(entries, P), a_rows, cols


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gap', type=int, default=5)
    ap.add_argument('--m', type=int, default=12)
    ap.add_argument('--k', type=int, default=5)
    ap.add_argument('--seeds', type=int, default=3)
    args = ap.parse_args()
    for seed in range(args.seeds):
        a, rows, cols = build_matrix(seed, args.gap, args.m, args.k, False)
        rank_a = a.rank()
        ab, _, _ = build_matrix(seed, args.gap, args.m, args.k, True)
        rank_ab = ab.rank()
        print(dict(seed=seed, gap=args.gap, m=args.m, k=args.k,
                   rows=rows, cols=cols, rank=rank_a,
                   nullity=cols-rank_a, boundary_increment=rank_ab-rank_a))


if __name__ == '__main__':
    main()
