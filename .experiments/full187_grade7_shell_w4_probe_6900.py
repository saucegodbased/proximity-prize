#!/usr/bin/env python3
"""Exact W=4 projection and literal strip ceilings for the grade-seven shell.

This is deliberately a conditional probe.  It does not assert a target-scale
formula for c,B,A.  It records what follows exactly from the canonical shell

 V^2 Z^3 (c V^2 + B V Z + A Lambda Xi V1 Z),
 V=Y-Xi^2 Z, V1=R-2XiXi'Z,

before an unproved relation among c,B,A is supplied.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Dict, Iterable, List, Sequence, Tuple

G, E, WIDTH, P = 180_413, 81_731, 131_071, 2_130_706_433
Monomial = Tuple[int, int]  # x,z where z is the old H^3*Z*J1 quotient
Poly = Dict[Monomial, int]


def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for m, c in p.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def scale(c: int, p: Poly) -> Poly:
    return {m: c * a for m, a in p.items() if c * a}


def zshift(p: Poly, q: int) -> Poly:
    return {(i, j + q): c for (i, j), c in p.items()}


def vpow(n: int, cut: int = 4) -> Poly:
    return {(i, 0): comb(n, i) for i in range(min(n, cut) + 1)}


def relay(n: int) -> Poly:
    return add(vpow(n), scale(-1, zshift(vpow(n - 2), 1)))


def phi2() -> Poly:
    return add(vpow(60), scale(-2, zshift(vpow(58), 1)), zshift(vpow(56), 2))


def phi3() -> Poly:
    return add(vpow(60), scale(-3, zshift(vpow(58), 1)),
               scale(3, zshift(vpow(56), 2)), scale(-1, zshift(vpow(54), 3)))


def rows() -> List[Monomial]:
    return [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (4, 0), (1, 1)]


def rank(a: Sequence[Sequence[int]]) -> int:
    a = [[Fraction(x) for x in r] for r in a]
    pivot_row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(pivot_row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        d = a[pivot_row][col]
        a[pivot_row] = [x / d for x in a[pivot_row]]
        for i in range(len(a)):
            if i != pivot_row and a[i][col]:
                q = a[i][col]
                a[i] = [x - q * y for x, y in zip(a[i], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def solve(a: Sequence[Sequence[int]], b: Sequence[int]) -> List[Fraction]:
    a = [[Fraction(x) for x in row] + [Fraction(rhs)] for row, rhs in zip(a, b)]
    pivots: List[int] = []
    r, n = 0, len(a[0]) - 1
    for c in range(n):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        d = a[r][c]
        a[r] = [x / d for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                q = a[i][c]
                a[i] = [x - q * y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
    assert all(any(row[:-1]) or not row[-1] for row in a)
    out = [Fraction(0)] * n
    for i, c in enumerate(pivots):
        out[c] = a[i][-1]
    return out


def target(ms: Iterable[Monomial]) -> List[int]:
    return [1 if m in {(0, 0), (1, 0)} else 0 for m in ms]


def d4(n: int) -> int:
    return 487635 - 32509*n + 1653*comb(n, 2) - 57*comb(n, 3) + comb(n, 4)


def dz(n: int) -> int:
    return n - 60


def main() -> None:
    # Project the passive seed Z to its local unit and the leading H*V1
    # direction to x.  The old W=4 matrix only sees this quotient.
    ms = rows()
    old = [relay(n) for n in range(57, 61)] + [phi2(), phi3()]
    v4, v3, hv1v2 = vpow(4), vpow(3), {(i + 1, j): c for (i, j), c in vpow(2).items()}
    b = target(ms)
    matrix = lambda columns: [[column.get(m, 0) for column in columns] for m in ms]
    a_old, a_v4, a_v3, a_pair = matrix(old), matrix(old + [v4]), matrix(old + [v3]), matrix(old + [v4, v3])
    augrank = lambda a: rank([row + [rhs] for row, rhs in zip(a, b)])
    assert (rank(a_old), augrank(a_old)) == (5, 6)
    assert (rank(a_v4), augrank(a_v4)) == (6, 7)
    assert (rank(a_v3), augrank(a_v3)) == (6, 7)
    assert (rank(a_pair), augrank(a_pair)) == (7, 7)
    solution = solve(a_pair, b)
    assert solution == [Fraction(-5015, 81), Fraction(270928, 1485),
                        Fraction(-9853, 55), Fraction(4962214, 84645),
                        Fraction(-334, 84645), Fraction(0),
                        Fraction(-3304, 1485), Fraction(272639, 84645)]
    assert all(sum(a_pair[i][j] * solution[j] for j in range(8)) == b[i]
               for i in range(len(ms)))
    assert (d4(4), dz(4), d4(3), dz(3)) == (367290, -56, 395010, -57)
    assert d4(4)*dz(3) - d4(3)*dz(4) == 1185030
    assert 0 < 1185030 < P
    assert hv1v2 == add(vpow(3), scale(-1, vpow(2)))

    # Literal source-strip ceilings without assuming unexplained cancellation.
    # c*V^4Z^3 and B*V^3Z^4 have their minimum at the Y^0 tails.
    c_ceiling = 60*G - 8*E
    b_ceiling = 60*G - 6*E
    # A*Lambda*Xi*V1*V^2Z^4: the V1 seed tail is the restrictive one.
    a_r_ceiling = 60*G - (WIDTH-1) - G - 5*E
    a_seed_ceiling = 60*G - G - 7*E + 1
    assert (c_ceiling, b_ceiling, a_r_ceiling, a_seed_ceiling) == (
        10170932, 10334394, 10104642, 10072251)
    assert 56*G == 10103128 and 57*G == 10283541
    assert c_ceiling - 56*G == 67804
    assert b_ceiling - 57*G == 50853
    assert 56*G - a_seed_ceiling == 30877

    print("grade7 W4 quotient: V4 and V3 dual determinant = 1185030 (nonzero mod p)")
    print("ranks old/V4/V3/pair:", (5, 6), (6, 7), (6, 7), (7, 7))
    print("exact projected amplitudes [R57,R58,R59,R60,Phi2,Phi3,V4,V3] =", list(map(str, solution)))
    print("third carrier leading projection H*V1*V2 = x*V2 = V3-V2")
    print("strict source ceilings: deg(c)<10170932, deg(B)<10334394, deg(A)<10072251")
    print("naive c=L^56 and B=L^57 pass with margins 67804 and 50853; A=L^56 is red by 30877")
    print("STOP on unconditional source legality: a target-scale c,B,A relation/cancellation is still required")


if __name__ == "__main__":
    main()
