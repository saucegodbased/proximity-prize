#!/usr/bin/env python3
"""Faithful exact discriminator for the complete lifted-t7 *next-rung* map.

This is deliberately stronger than the earlier ambient/top-boundary probes.
For a small multiplicative-subgroup analogue of the target it builds

* ``N = X^n-1`` and an actual agreement locator ``H``;
* a degree-``<=w`` selected polynomial ``P``;
* a received combination ``Q_gamma = P + H*E`` of degree at least ``g``;
* received interpolants ``U0,U1`` with ``U0+gamma*U1 = Q_gamma``;
* the exact reversed-top map for
  ``N^6 J, N^5 C1, N^4 C2, N^7 Z``;
* one literal epsilon-order-seven evaluation row at every error; and
* the four raw compatible-boundary derivative rows at a fresh point.

The target-scaled parameters satisfy ``M=e=n-g`` and
``over = 7*n-10*g``.  Thus the top row count is exactly
``(M+over+1)*(K+2)``, the analogue of
``(81731+30878+1)*(3+2)``.  The order-seven error rows use the leading
epsilon coefficients of the literal raw covariants, not independent random
weights.

This remains a finite falsifier, not a uniform proof and certainly not a
6900 endpoint: a green result concerns only the seventh recurrence rung.
"""

from __future__ import annotations

import argparse
import random

from flint import nmod_mat


def trim(a, p):
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a, b, p):
    out = [0] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = ((a[i] if i < len(a) else 0) +
                  (b[i] if i < len(b) else 0)) % p
    return trim(out, p)


def scale(a, c, p):
    return trim([c * x % p for x in a], p)


def mul(a, b, p, cap=None):
    size = len(a) + len(b) - 1
    if cap is not None:
        size = min(size, cap)
    out = [0] * max(size, 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j >= size:
                break
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out, p)


def deriv(a, p):
    return trim([i * a[i] % p for i in range(1, len(a))] or [0], p)


def eval_poly(a, x, p):
    out = 0
    for c in reversed(a):
        out = (out * x + c) % p
    return out


def degree(a):
    return -1 if all(x == 0 for x in a) else len(trim(a, 10**100)) - 1


def product_linear(roots, p):
    out = [1]
    for x in roots:
        out = mul(out, [-x % p, 1], p)
    return out


def primitive_root(p):
    factors = []
    x = p - 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            factors.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise AssertionError("no primitive root")


def taylor(poly, x, order, p):
    """Coefficients of poly(x+epsilon), through ``order-1``."""
    out = []
    work = poly
    factorial = 1
    for j in range(order):
        if j:
            factorial = factorial * j % p
        out.append(eval_poly(work, x, p) * pow(factorial, -1, p) % p)
        work = deriv(work, p)
    return out


def covariant_leads(N, U0, U1, x, z, raw_r, raw_s, raw_t, p):
    """Leading epsilon^1,^2,^3 coefficients of J,C1,C2 at an old node."""
    order = 5
    ns = taylor(N, x, order, p)
    u0 = taylor(U0, x, order, p)
    u1 = taylor(U1, x, order, p)
    assert ns[0] == 0 and ns[1] != 0

    js = [0] * order
    js[0] = (-u0[0] - z * u1[0]) % p
    # contacted Y has the received constant plus eps*R-eps^2*S+eps^3*T.
    js[0] = 0
    for j in range(1, order):
        contacted = raw_r if j == 1 else (-raw_s if j == 2 else
                    (raw_t if j == 3 else 0))
        js[j] = (contacted - u0[j] - z * u1[j]) % p

    # V=R-U0'(x+eps)-Z*U1'(x+eps).
    vs = [0] * order
    vs[0] = (raw_r - u0[1] - z * u1[1]) % p
    for j in range(1, order):
        factor = j + 1
        vs[j] = (-factor * (u0[j + 1] + z * u1[j + 1])) % p \
            if j + 1 < order else 0

    # A=-2*S-U0''(x+eps)-Z*U1''(x+eps).
    aas = [0] * order
    aas[0] = (-2 * raw_s - 2 * (u0[2] + z * u1[2])) % p
    for j in range(1, order):
        factor = (j + 1) * (j + 2)
        aas[j] = (-factor * (u0[j + 2] + z * u1[j + 2])) % p \
            if j + 2 < order else 0

    nd = [((j + 1) * ns[j + 1] if j + 1 < order else 0) % p
          for j in range(order)]
    ndd = [((j + 1) * (j + 2) * ns[j + 2]
            if j + 2 < order else 0) % p for j in range(order)]
    c1 = add(mul(nd, js, p, order),
             scale(mul(ns, vs, p, order), -1, p), p)
    n2 = mul(ns, ns, p, order)
    c2 = add(mul(n2, aas, p, order),
             scale(mul(mul(ns, nd, p, order), vs, p, order), -2, p), p)
    c2 = add(c2, scale(n2, 4 * raw_s, p), p)
    bracket = add(scale(mul(nd, nd, p, order), 2, p),
                  scale(mul(ns, ndd, p, order), -1, p), p)
    c2 = add(c2, mul(bracket, js, p, order), p)
    return (js[1], c1[2] if len(c1) > 2 else 0,
            c2[3] if len(c2) > 3 else 0)


def make_instance(seed, p, n, gcount):
    rng = random.Random(seed)
    assert (p - 1) % n == 0
    root = pow(primitive_root(p), (p - 1) // n, p)
    nodes = [pow(root, i, p) for i in range(n)]
    rng.shuffle(nodes)
    agreement = nodes[:gcount]
    errors = nodes[gcount:]
    e = len(errors)
    w = n // 2 - 1
    gamma = rng.randrange(1, p)
    H = product_linear(agreement, p)
    N = [(-1) % p] + [0] * (n - 1) + [1]

    Psel = [rng.randrange(p) for _ in range(w + 1)]
    # Cycle through every admissible top valuation.  ``deg Eres=d`` gives
    # ``deg Q=g+d`` and reversed valuation ``e-1-d``; in particular seed 0
    # tests the critical edge ``deg Q=g``, valuation ``M-1``.
    residual_degree = seed % e
    Eres = [rng.randrange(p) for _ in range(residual_degree + 1)]
    Eres[-1] = rng.randrange(1, p)
    Q = add(Psel, mul(H, Eres, p), p)
    assert degree(Q) >= gcount and degree(Q) < n

    # Keep the whole received projective pencil above the scaled high cut.
    # U1 full degree makes this overwhelmingly likely; retry deterministically
    # inside the seed until the finite projective-line check passes.
    high_cut = (133120 * n + 262143) // 262144
    while True:
        U1 = [rng.randrange(p) for _ in range(n)]
        U1[-1] = rng.randrange(1, p)
        U0 = add(Q, scale(U1, -gamma, p), p)
        projective_degrees = [degree(U1)]
        projective_degrees += [degree(add(U0, scale(U1, lam, p), p))
                               for lam in range(p)]
        if min(projective_degrees) >= high_cut:
            break

    assert trim(add(U0, scale(U1, gamma, p), p), p) == trim(Q, p)
    assert all(eval_poly(Psel, x, p) == eval_poly(Q, x, p)
               for x in agreement)
    outsiders = [x for x in range(1, p) if x not in set(nodes)]
    alpha = rng.choice(outsiders)
    return dict(rng=rng, nodes=nodes, agreement=agreement, errors=errors,
                e=e, w=w, gamma=gamma, H=H, N=N, Psel=Psel, Q=Q,
                U0=U0, U1=U1, alpha=alpha, high_cut=high_cut,
                residual_degree=residual_degree)


def build(seed, *, p=193, n=32, gcount=22, k=3,
          boundary_mode="bothzero"):
    inst = make_instance(seed, p, n, gcount)
    rng = inst["rng"]
    e = inst["e"]
    m = e
    over = 7 * n - 10 * gcount
    assert over >= 0 and m + over + 1 < n
    qrows = m + over + 1
    zrows = k + 2
    cols = 4 * (m + 1) * (k + 1)
    top_rows = qrows * zrows
    error_rows = e
    total_rows = top_rows + error_rows + 4
    entries = [[0] * cols for _ in range(total_rows)]

    def col(i, aq, az):
        return (i * (m + 1) + aq) * (k + 1) + az

    def top_row(qr, zr):
        return qr * zrows + zr

    # g(q,Z) is the reversal of U0+Z*U1 in ambient degree n-1.
    gs = [[0, 0] for _ in range(qrows)]
    for r in range(qrows):
        d = n - 1 - r
        gs[r][0] = inst["U0"][d] if d < len(inst["U0"]) else 0
        gs[r][1] = inst["U1"][d] if d < len(inst["U1"]) else 0

    # Exact normalized reversed-top faces.
    for aq in range(m + 1):
        for az in range(k + 1):
            for r, pair in enumerate(gs):
                for gz, value in enumerate(pair):
                    if not value:
                        continue
                    if aq + 1 + r < qrows:
                        entries[top_row(aq + 1 + r, az + gz)][
                            col(0, aq, az)] = -value % p
                    if aq + 2 + r < qrows:
                        entries[top_row(aq + 2 + r, az + gz)][
                            col(1, aq, az)] = -(r + 1) * value % p
                    if aq + 3 + r < qrows:
                        entries[top_row(aq + 3 + r, az + gz)][
                            col(2, aq, az)] = -(r + 1) * (r + 2) * value % p
            entries[top_row(aq, az + 1)][col(3, aq, az)] = 1

    # One literal epsilon^7 row per actual error node.  We sample the raw
    # local R,S,T values but keep Z equal to the actual direction gamma.
    for j, x in enumerate(inst["errors"]):
        z = inst["gamma"]
        raw_r, raw_s, raw_t = (rng.randrange(p) for _ in range(3))
        j1, c12, c23 = covariant_leads(
            inst["N"], inst["U0"], inst["U1"], x, z,
            raw_r, raw_s, raw_t, p)
        n1 = eval_poly(deriv(inst["N"], p), x, p)
        weights = [pow(n1, 6, p) * j1,
                   pow(n1, 5, p) * c12,
                   pow(n1, 4, p) * c23,
                   pow(n1, 7, p) * z]
        assert any(v % p for v in weights)
        rr = top_rows + j
        for i in range(4):
            for aq in range(m + 1):
                xv = pow(x, m - aq, p)
                for az in range(k + 1):
                    entries[rr][col(i, aq, az)] = (
                        weights[i] * xv * pow(z, az, p)) % p

    # Exact raw (S,Y,R,Z) gradients at the compatible fresh boundary J=0.
    x = inst["alpha"]
    z = inst["gamma"]
    N0 = eval_poly(inst["N"], x, p)
    N1 = eval_poly(deriv(inst["N"], p), x, p)
    N2 = eval_poly(deriv(deriv(inst["N"], p), p), x, p)
    U0v = eval_poly(inst["U0"], x, p)
    U1v = eval_poly(inst["U1"], x, p)
    U0p = eval_poly(deriv(inst["U0"], p), x, p)
    U1p = eval_poly(deriv(inst["U1"], p), x, p)
    U0pp = eval_poly(deriv(deriv(inst["U0"], p), p), x, p)
    U1pp = eval_poly(deriv(deriv(inst["U1"], p), p), x, p)
    received_slope = (U0p + z * U1p) % p
    received_curvature = (U0pp + z * U1pp) % p
    if boundary_mode == "bothzero":
        Vchosen = 0
        raw_r = received_slope
        raw_s = received_curvature * pow(2, -1, p) % p
    elif boundary_mode == "c1zero":
        Vchosen = 0
        raw_r = received_slope
        raw_s = rng.randrange(p)
        while (2 * raw_s - received_curvature) % p == 0:
            raw_s = rng.randrange(p)
    elif boundary_mode == "c2zero":
        Vchosen = rng.randrange(1, p)
        raw_r = (received_slope + Vchosen) % p
        raw_s = ((received_curvature +
                  2 * N1 * pow(N0, -1, p) * Vchosen) *
                 pow(2, -1, p)) % p
    elif boundary_mode == "generic":
        raw_r, raw_s = rng.randrange(p), rng.randrange(p)
        Vchosen = (raw_r - received_slope) % p
    else:
        raise ValueError(boundary_mode)
    # y=U0+zU1, hence J=0.
    V = (raw_r - U0p - z * U1p) % p
    C1 = (-N0 * V) % p
    Avec = (-2 * raw_s - U0pp - z * U1pp) % p
    C2 = (N0 * N0 * Avec - 2 * N0 * N1 * V +
          4 * N0 * N0 * raw_s) % p
    if boundary_mode in ("bothzero", "c1zero"):
        assert C1 == 0
    if boundary_mode in ("bothzero", "c2zero"):
        assert C2 == 0
    if boundary_mode == "bothzero":
        assert C1 == 0 and C2 == 0
    dJ = [0, 1, 0, -U1v % p]
    dV = [0, 0, 1, -U1p % p]
    dA = [-2 % p, 0, 0, -U1pp % p]
    dC1 = [(N1 * dJ[h] - N0 * dV[h]) % p for h in range(4)]
    bracket = (2 * N1 * N1 - N0 * N2) % p
    dC2 = [(N0 * N0 * dA[h] - 2 * N0 * N1 * dV[h] +
            (4 * N0 * N0 if h == 0 else 0) + bracket * dJ[h]) % p
           for h in range(4)]
    bases = [0, pow(N0, 5, p) * C1 % p,
             pow(N0, 4, p) * C2 % p, pow(N0, 7, p) * z % p]
    grads = [[pow(N0, 6, p) * v % p for v in dJ],
             [pow(N0, 5, p) * v % p for v in dC1],
             [pow(N0, 4, p) * v % p for v in dC2],
             [0, 0, 0, pow(N0, 7, p)]]
    assert N0 != 0
    for i in range(4):
        for aq in range(m + 1):
            xv = pow(x, m - aq, p)
            for az in range(k + 1):
                cc = col(i, aq, az)
                peval = xv * pow(z, az, p) % p
                pz = (az * xv * pow(z, az - 1, p)) % p if az else 0
                for h in range(4):
                    entries[top_rows + error_rows + h][cc] = (
                        peval * grads[i][h] +
                        (pz * bases[i] if h == 3 else 0)) % p

    top = nmod_mat(entries[:top_rows], p)
    top_error = nmod_mat(entries[:top_rows + error_rows], p)
    joint = nmod_mat(entries, p)
    scalar_h_val = next(r for r, pair in enumerate(gs)
                        if (pair[0] + inst["gamma"] * pair[1]) % p)
    return dict(seed=seed, p=p, n=n, g=gcount, e=e, M=m, K=k,
                over=over, cols=cols, top_rows=top_rows,
                error_rows=error_rows, scalar_h_valuation=scalar_h_val,
                residual_degree=inst["residual_degree"],
                boundary_mode=boundary_mode,
                top_rank=top.rank(), top_error_rank=top_error.rank(),
                joint_rank=joint.rank(), high_cut=inst["high_cut"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=int, default=20)
    ap.add_argument("--p", type=int, default=193)
    ap.add_argument("--n", type=int, default=32)
    ap.add_argument("--g", type=int, default=22)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--boundary-mode", choices=(
        "bothzero", "c1zero", "c2zero", "generic"), default="bothzero")
    args = ap.parse_args()
    failures = []
    for seed in range(args.seeds):
        out = build(seed, p=args.p, n=args.n, gcount=args.g, k=args.k,
                    boundary_mode=args.boundary_mode)
        out["error_increment"] = out["top_error_rank"] - out["top_rank"]
        out["boundary_increment"] = out["joint_rank"] - out["top_error_rank"]
        if (out["error_increment"] != out["error_rows"] or
                out["boundary_increment"] != 4):
            failures.append(out)
        print(out)
    print({"tested": args.seeds, "failures": len(failures),
           "first_failure": failures[0] if failures else None})


if __name__ == "__main__":
    main()
