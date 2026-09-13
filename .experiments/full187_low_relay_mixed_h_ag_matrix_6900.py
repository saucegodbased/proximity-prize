#!/usr/bin/env python3
"""Exact weighted associated-graded matrix for the low mixed-H relay rows.

Normalise U=V=1 at the chosen simple error and put x = V-1 (weight 1),
z = H^3 Z J1/U (weight 3).  The six legal pure-seed-cancelling rows are

  R_n : (1+x)^n - z (1+x)^(n-2)                 n = 57,58,59,60
  Phi2: (1+x)^60 - 2z(1+x)^58 + z^2(1+x)^56
  Phi3: (1+x)^60 - 3z(1+x)^58 + 3z^2(1+x)^56 - z^3(1+x)^54.

This file intentionally works over Z, before reduction modulo the Full187
characteristic p = 2130706433.  All displayed nonzero certificates are below
p, hence remain nonzero in the actual target field.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Dict, Iterable, List, Sequence, Tuple

P = 2_130_706_433
Monomial = Tuple[int, int]  # x exponent, z exponent
Poly = Dict[Monomial, int]


def weight(m: Monomial) -> int:
    return m[0] + 3 * m[1]


def add(*polys: Poly) -> Poly:
    out: Poly = {}
    for poly in polys:
        for monomial, coefficient in poly.items():
            out[monomial] = out.get(monomial, 0) + coefficient
    return {m: c for m, c in out.items() if c}


def scale(poly: Poly, coefficient: int) -> Poly:
    return {m: coefficient * c for m, c in poly.items() if coefficient * c}


def zshift(poly: Poly, power: int) -> Poly:
    return {(i, j + power): c for (i, j), c in poly.items()}


def vpow(exponent: int, cutoff: int) -> Poly:
    """(1+x)^exponent, retaining monomials of weighted degree at most cutoff."""
    return {(i, 0): comb(exponent, i) for i in range(min(exponent, cutoff) + 1)}


def truncate(poly: Poly, cutoff: int) -> Poly:
    return {m: c for m, c in poly.items() if weight(m) <= cutoff}


def relay(n: int, cutoff: int) -> Poly:
    return add(vpow(n, cutoff), scale(zshift(vpow(n - 2, cutoff), 1), -1))


def phi2(cutoff: int) -> Poly:
    return add(
        vpow(60, cutoff),
        scale(zshift(vpow(58, cutoff), 1), -2),
        zshift(vpow(56, cutoff), 2),
    )


def phi3(cutoff: int) -> Poly:
    return add(
        vpow(60, cutoff),
        scale(zshift(vpow(58, cutoff), 1), -3),
        scale(zshift(vpow(56, cutoff), 2), 3),
        scale(zshift(vpow(54, cutoff), 3), -1),
    )


def monomials(cutoff: int) -> List[Monomial]:
    return [(i, j) for d in range(cutoff + 1) for j in range(d // 3 + 1)
            for i in [d - 3 * j]]


def matrix(cutoff: int) -> Tuple[List[Monomial], List[str], List[List[int]]]:
    rows = monomials(cutoff)
    labels = ["R57", "R58", "R59", "R60", "Phi2", "Phi3"]
    generators = [relay(n, cutoff) for n in range(57, 61)] + [phi2(cutoff), phi3(cutoff)]
    return rows, labels, [[g.get(m, 0) for g in generators] for m in rows]


def rank(a: Sequence[Sequence[int]]) -> int:
    """Exact rational rank, with no CAS dependency."""
    a = [[Fraction(x) for x in row] for row in a]
    if not a:
        return 0
    r = 0
    ncols = len(a[0])
    for c in range(ncols):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        divisor = a[r][c]
        a[r] = [x / divisor for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                q = a[i][c]
                a[i] = [x - q * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def target(rows: Iterable[Monomial]) -> List[int]:
    # F0 normalised in this chart is V=1+x.
    return [1 if m in {(0, 0), (1, 0)} else 0 for m in rows]


def dot(left: Sequence[int], right: Sequence[int]) -> int:
    return sum(x * y for x, y in zip(left, right))


def row_combination(columns: Sequence[Sequence[int]], amplitudes: Sequence[int]) -> List[int]:
    return [sum(a * c for a, c in zip(amplitudes, row)) for row in columns]


def agreement_ledger() -> None:
    # Contact at C_G: V has order 1 and J1 has order 2.  H^3Z has order 0.
    assert [(60 - n) + n for n in range(57, 61)] == [60] * 4
    assert [(60 - n) + (n - 2) + 2 for n in range(57, 61)] == [60] * 4
    assert 56 + 2 * 2 == 60  # Phi2 = V^56 (UV^2-H^3ZJ1)^2
    assert 54 + 3 * 2 == 60  # Phi3 = V^54 (UV^2-H^3ZJ1)^3


def main() -> None:
    agreement_ledger()
    print("Full187 mixed-H associated-graded matrix over Z; p =", P)
    print("columns: R57 R58 R59 R60 Phi2 Phi3")
    print("weights: wt(x)=1, wt(z)=3; z retains the full H^3 J1 tail")
    print("agreement contact ledger: every one of the six rows has C_G order >= 60")

    for cutoff in range(0, 10):
        rows, labels, a = matrix(cutoff)
        b = target(rows)
        augmented = [row + [entry] for row, entry in zip(a, b)]
        print(f"W={cutoff}: rows={rows}; rank={rank(a)}; augmented_rank={rank(augmented)}")
        if rank(a) != rank(augmented):
            break

    rows3, _, a3 = matrix(3)
    w3 = [32509, -95816, 94164, -30856, 1, -1]
    assert row_combination(a3, w3) == target(rows3)
    print("weight-3 amplitudes [R57,R58,R59,R60,Phi2,Phi3] =", w3)

    rows4, labels4, a4 = matrix(4)
    b4 = target(rows4)
    residual = [x - y for x, y in zip(row_combination(a4, w3), b4)]
    residual_by_monomial = dict(zip(rows4, residual))
    assert residual_by_monomial[(4, 0)] == -455126
    assert residual_by_monomial[(1, 1)] == 59
    print("weight-4 residual of that lift:",
          "[x^4] =", residual_by_monomial[(4, 0)],
          "; [xz] =", residual_by_monomial[(1, 1)])

    # The W=3 kernel direction is R60 - 2 Phi2 + Phi3.  It cannot repair W=4.
    kernel = [0, 0, 0, 1, -2, 1]
    assert row_combination(a3, kernel) == [0] * len(rows3)
    assert row_combination(a4, kernel) == [0] * len(rows4)

    # A left-null certificate independent of solving: it sees only 1,x,...,x^4.
    # Ordered rows at W=4 are 1,x,x^2,x^3,z,x^4,xz.
    assert rows4 == [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (4, 0), (1, 1)]
    dual_x4 = [487635, -32509, 1653, -57, 0, 1, 0]
    assert [dot(dual_x4, [a4[i][j] for i in range(len(rows4))]) for j in range(len(labels4))] == [0] * 6
    assert dot(dual_x4, b4) == 455126
    assert 0 < 455126 < P
    print("x^4 left-null certificate on the target =", dot(dual_x4, b4), "(nonzero mod p)")

    dual_xz = [-60, 1, 0, 0, -58, 0, 1]
    assert [dot(dual_xz, [a4[i][j] for i in range(len(rows4))]) for j in range(len(labels4))] == [0] * 6
    assert dot(dual_xz, b4) == -59
    print("xz left-null certificate on the target =", dot(dual_xz, b4), "(nonzero mod p)")
    print("STOP: weight 4 is the first rank failure for this complete six-row family.")


if __name__ == "__main__":
    main()
