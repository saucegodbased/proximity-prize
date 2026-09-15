#!/usr/bin/env python3
"""Literal finite-field matrices for consecutive-jet contact interpolation.

This is deliberately a *small-instance* oracle, not a production counter.
For jets V_0,...,V_k and a received value u at a node x, it expands

  X   -> x + T
  V_0 -> u + E + sum_{h=1}^k (-1)^(h+1) T^h/h! V_h
  V_h -> V_h, h > 0

in the quotient with contact weight wt(T)=1, wt(E)=k+1 and truncation
q+(k+1)b < m.  Rows are literal quotient monomials at every node.  The
resulting modular rank tests both the one-node Hilbert formula and whether
the usual sum of per-node ranks hides useful cross-node dependencies.

Only tiny parameters are intended: sparse dictionaries are expanded exactly
and Gaussian elimination is performed over the prime field F_p.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import factorial
import argparse
import random


Mon = tuple[int, ...]  # (T,E,V1,...,Vk,Z)


def add_poly(a: dict[Mon, int], b: dict[Mon, int], p: int) -> dict[Mon, int]:
    out = dict(a)
    for mon, coeff in b.items():
        value = (out.get(mon, 0) + coeff) % p
        if value:
            out[mon] = value
        else:
            out.pop(mon, None)
    return out


def mul_poly(a: dict[Mon, int], b: dict[Mon, int], m: int, k: int,
             p: int) -> dict[Mon, int]:
    out: dict[Mon, int] = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            mon = tuple(x + y for x, y in zip(ma, mb))
            if mon[0] + (k + 1) * mon[1] >= m:
                continue
            out[mon] = (out.get(mon, 0) + ca * cb) % p
    return {mon: c for mon, c in out.items() if c}


def pow_poly(a: dict[Mon, int], e: int, m: int, k: int,
             p: int) -> dict[Mon, int]:
    one = (0,) * (k + 3)
    out = {one: 1}
    base = a
    while e:
        if e & 1:
            out = mul_poly(out, base, m, k, p)
        e //= 2
        if e:
            base = mul_poly(base, base, m, k, p)
    return out


def translated_column(xpow: int, exps: tuple[int, ...], zpow: int,
                      x: int, u0: int, u1: int, m: int, k: int,
                      p: int) -> dict[Mon, int]:
    """Expand X^a prod_h V_h^e_h Z^z with anchor u0+Z*u1."""
    zero = (0,) * (k + 3)
    t = [0] * (k + 3)
    t[0] = 1
    e = [0] * (k + 3)
    e[1] = 1
    xpoly = {zero: x % p, tuple(t): 1}
    zmon = [0] * (k + 3)
    zmon[-1] = 1
    v0 = {zero: u0 % p, tuple(zmon): u1 % p, tuple(e): 1}
    for h in range(1, k + 1):
        mon = [0] * (k + 3)
        mon[0] = h
        mon[1 + h] = 1
        sign = 1 if h % 2 == 1 else -1
        coeff = sign * pow(factorial(h), -1, p)
        v0[tuple(mon)] = coeff % p
    out = pow_poly(xpoly, xpow, m, k, p)
    out = mul_poly(out, pow_poly(v0, exps[0], m, k, p), m, k, p)
    for h in range(1, k + 1):
        vh = [0] * (k + 3)
        vh[1 + h] = 1
        out = mul_poly(out, pow_poly({tuple(vh): 1}, exps[h], m, k, p),
                       m, k, p)
    out = mul_poly(out, pow_poly({tuple(zmon): 1}, zpow, m, k, p), m, k, p)
    return out


def support(D: int, w: int, k: int, total_cap: int,
            caps: tuple[int, ...] | None = None,
            include_z: bool = True) -> list[tuple[int, tuple[int, ...], int]]:
    """Weighted simplex, optionally with individual caps on V_1,...,V_k."""
    if caps is None:
        caps = (total_cap,) * k
    out = []
    for exps in product(range(total_cap + 1), repeat=k + 1):
        if sum(exps) > total_cap:
            continue
        if any(exps[h] > caps[h - 1] for h in range(1, k + 1)):
            continue
        weight = sum((w - h) * exps[h] for h in range(k + 1))
        zmax = total_cap - sum(exps) if include_z else 0
        for z in range(zmax + 1):
            for a in range(max(0, D - weight)):
                out.append((a, exps, z))
    return out


def flag_support(D: int, w: int, k: int, jet_cap: int, total_cap: int,
                 derivative_cap: int) -> list[tuple[int, tuple[int, ...], int]]:
    """Consecutive-jet flag used by consecutive_jet_flag_6900.py."""
    out = []
    for exps in product(range(jet_cap + 1), repeat=k + 1):
        d = sum(exps)
        if d > jet_cap or sum(exps[1:]) > derivative_cap:
            continue
        weight = sum((w - h) * exps[h] for h in range(k + 1))
        for z in range(total_cap - d + 1):
            for a in range(max(0, D - weight)):
                out.append((a, exps, z))
    return out


def modular_rank(columns: list[dict[object, int]], p: int) -> int:
    """Column rank by sparse incremental elimination with normalized pivots."""
    pivots: dict[object, dict[object, int]] = {}
    for source in columns:
        v = {r: c % p for r, c in source.items() if c % p}
        while v:
            pivot = min(v, key=repr)
            if pivot not in pivots:
                inv = pow(v[pivot], -1, p)
                v = {r: c * inv % p for r, c in v.items() if c * inv % p}
                pivots[pivot] = v
                break
            coeff = v[pivot]
            old = pivots[pivot]
            for r, c in old.items():
                value = (v.get(r, 0) - coeff * c) % p
                if value:
                    v[r] = value
                else:
                    v.pop(r, None)
    return len(pivots)


@dataclass(frozen=True)
class Result:
    n: int
    w: int
    agreements: int
    k: int
    m: int
    cap: int
    derivative_caps: tuple[int, ...]
    columns: int
    one_node_rank: int
    sum_rank_bound: int
    global_rank: int
    nullity: int


def run_instance(n: int, w: int, agreements: int, k: int, m: int, cap: int,
                 derivative_caps: tuple[int, ...], p: int,
                 seed: int = 1) -> Result:
    D = m * agreements
    cols = support(D, w, k, cap, derivative_caps)
    rng = random.Random(seed)
    xs = list(range(1, n + 1))
    u0s = [rng.randrange(1, p) for _ in xs]
    u1s = [rng.randrange(1, p) for _ in xs]
    local_columns = [translated_column(a, e, z, xs[0], u0s[0], u1s[0],
                                       m, k, p)
                     for a, e, z in cols]
    one = modular_rank(local_columns, p)
    global_columns: list[dict[object, int]] = []
    for a, e, z in cols:
        merged: dict[object, int] = {}
        for node, (x, u0, u1) in enumerate(zip(xs, u0s, u1s)):
            for mon, coeff in translated_column(
                    a, e, z, x, u0, u1, m, k, p).items():
                merged[(node, mon)] = coeff
        global_columns.append(merged)
    rank = modular_rank(global_columns, p)
    return Result(n, w, agreements, k, m, cap, derivative_caps, len(cols),
                  one, n * one, rank, len(cols) - rank)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=12)
    parser.add_argument("--w", type=int, default=6)
    parser.add_argument("--agreements", type=int, default=8)
    parser.add_argument("--kmax", type=int, default=3)
    parser.add_argument("--mmax", type=int, default=7)
    parser.add_argument("--capmax", type=int, default=4)
    parser.add_argument("--prime", type=int, default=1009)
    args = parser.parse_args()
    for k in range(1, args.kmax + 1):
        for m in range(1, args.mmax + 1):
            for cap in range(args.capmax + 1):
                for caps in product(range(cap + 1), repeat=k):
                    result = run_instance(args.n, args.w, args.agreements, k,
                                          m, cap, caps, args.prime)
                    if result.nullity or result.global_rank < min(
                            result.columns, result.sum_rank_bound):
                        print(result)


if __name__ == "__main__":
    main()
