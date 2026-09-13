#!/usr/bin/env python3
"""Centered K1/K2 dual-breaker receipt for the Full187 W=4 relay STOP.

The prior six-row calculation used x=V-1 (weight one) and retained the
H^3*J1 tail z (weight three).  Its two W=4 cokernel functionals were

 D4  = (487635,-32509,1653,-57,0,1,0),
 Dz  = (-60,1,0,0,-58,0,1)

on (1,x,x^2,x^3,z,x^4,xz).  Here we test the centered pure-tail factors

 K1 = J1-H*U*Z = L*R-L'*Y,
 K2 = J2-B*Z = (2(L')^2-L*L'')*Y-2L*L'*R+L^2*S.

The equalities are literal after V=Y-H^2Z, W=R-2HH'Z and the corresponding
second derivative substitution.  Thus K1,K2 vanish at the fixed pure tail
but their source expansions are only linear in Y,R,S.  All arithmetic is
over Z before reduction modulo p=2130706433.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Dict, Iterable, List, Sequence, Tuple

M, G, E, WIDTH, P = 60, 180_413, 81_731, 131_071, 2_130_706_433
QDEG = E - 1
Monomial = Tuple[int, int]  # x,z exponents
Poly = Dict[Monomial, int]


def weight(m: Monomial) -> int:
    return m[0] + 3 * m[1]


def add(*polys: Poly) -> Poly:
    out: Poly = {}
    for poly in polys:
        for m, c in poly.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def scale(c: int, poly: Poly) -> Poly:
    return {m: c * a for m, a in poly.items() if c * a}


def zshift(poly: Poly, power: int) -> Poly:
    return {(i, j + power): c for (i, j), c in poly.items()}


def vpow(n: int, cutoff: int) -> Poly:
    return {(i, 0): comb(n, i) for i in range(min(n, cutoff) + 1)}


def relay(n: int, cutoff: int) -> Poly:
    return add(vpow(n, cutoff), scale(-1, zshift(vpow(n - 2, cutoff), 1)))


def phi2(cutoff: int) -> Poly:
    return add(vpow(60, cutoff), scale(-2, zshift(vpow(58, cutoff), 1)),
               zshift(vpow(56, cutoff), 2))


def phi3(cutoff: int) -> Poly:
    return add(vpow(60, cutoff), scale(-3, zshift(vpow(58, cutoff), 1)),
               scale(3, zshift(vpow(56, cutoff), 2)),
               scale(-1, zshift(vpow(54, cutoff), 3)))


def centered_column(b: int, kappa: int, linear: int, cutoff: int) -> Poly:
    """V^b*(kappa+linear*x), the W<=cutoff K_i error column."""
    return add(scale(kappa, vpow(b, cutoff)),
               scale(linear, {(i + 1, j): c for (i, j), c in vpow(b, cutoff).items()}))


def rows(cutoff: int) -> List[Monomial]:
    return [(i, j) for d in range(cutoff + 1) for j in range(d // 3 + 1)
            for i in [d - 3 * j]]


def rank(a: Sequence[Sequence[int]]) -> int:
    data = [[Fraction(x) for x in row] for row in a]
    if not data:
        return 0
    pivot_row = 0
    for col in range(len(data[0])):
        pivot = next((i for i in range(pivot_row, len(data)) if data[i][col]), None)
        if pivot is None:
            continue
        data[pivot_row], data[pivot] = data[pivot], data[pivot_row]
        divisor = data[pivot_row][col]
        data[pivot_row] = [x / divisor for x in data[pivot_row]]
        for i in range(len(data)):
            if i != pivot_row and data[i][col]:
                q = data[i][col]
                data[i] = [x - q * y for x, y in zip(data[i], data[pivot_row])]
        pivot_row += 1
        if pivot_row == len(data):
            break
    return pivot_row


def solve(a: Sequence[Sequence[int]], b: Sequence[int]) -> List[Fraction]:
    """One exact solution, with nonpivot variables set to zero."""
    data = [[Fraction(x) for x in row] + [Fraction(y)] for row, y in zip(a, b)]
    pivots: List[int] = []
    pivot_row = 0
    ncols = len(a[0])
    for col in range(ncols):
        pivot = next((i for i in range(pivot_row, len(data)) if data[i][col]), None)
        if pivot is None:
            continue
        data[pivot_row], data[pivot] = data[pivot], data[pivot_row]
        divisor = data[pivot_row][col]
        data[pivot_row] = [x / divisor for x in data[pivot_row]]
        for i in range(len(data)):
            if i != pivot_row and data[i][col]:
                q = data[i][col]
                data[i] = [x - q * y for x, y in zip(data[i], data[pivot_row])]
        pivots.append(col)
        pivot_row += 1
    assert all(any(row[:-1]) or not row[-1] for row in data)
    out = [Fraction(0) for _ in range(ncols)]
    for row, col in enumerate(pivots):
        out[col] = data[row][-1]
    return out


def target(ms: Iterable[Monomial]) -> List[int]:
    return [1 if m in {(0, 0), (1, 0)} else 0 for m in ms]


def dot(left: Sequence[int], right: Sequence[int]) -> int:
    return sum(x * y for x, y in zip(left, right))


# A component records the exact highest possible coefficient degree after
# collecting the centered source identity.  `i` is the Y exponent chosen
# from V^b=(Y-H^2Z)^b.  There are no hidden BZ or HUZ tails left.
def source_rows(kind: str, b: int) -> List[dict[str, int | bool | tuple[int, int, int, int]]]:
    assert kind in {"K1", "K2"} and 0 <= b <= 60
    outer = (60 - b) * G + QDEG
    if kind == "K1":
        # K1 = L*R-L'*Y.
        components = ((0, 1, 0, G, "R"), (1, 0, 0, G - 1, "Y"))
    else:
        # K2 = (2L'^2-LL'')Y-2LL'R+L^2S.
        components = ((1, 0, 0, 2 * G - 2, "Y"),
                      (0, 1, 0, 2 * G - 1, "R"),
                      (0, 0, 1, 2 * G, "S"))
    out = []
    for y_shift, r, s, degree_extra, label in components:
        for i in range(b + 1):
            y, z = i + y_shift, b - i
            degree = outer + degree_extra + 2 * E * (b - i)
            cutoff = M * G - WIDTH * y - (WIDTH - 1) * r - (WIDTH - 2) * s
            caps_ok = (y + r + s <= 82 and r + s <= 21 and s <= 10 and
                       y + r + s + z <= 2703)
            out.append({"component": label, "shape": (y, r, s, z),
                        "degree": degree, "cutoff": cutoff,
                        "margin": cutoff - degree, "caps_ok": caps_ok})
    return out


def source_ledger(kind: str, b: int) -> dict[str, int | bool | tuple[int, int, int, int]]:
    entries = source_rows(kind, b)
    worst = min(entries, key=lambda entry: int(entry["margin"]))
    return {"b": b, "minimum_margin": int(worst["margin"]),
            "worst_shape": worst["shape"], "worst_component": worst["component"],
            "all_literal_terms_legal": all(bool(row["caps_ok"]) and int(row["margin"]) > 0
                                           for row in entries)}


def first_legal(kind: str) -> dict[str, int | bool | tuple[int, int, int, int]]:
    return next(source_ledger(kind, b) for b in range(61)
                if bool(source_ledger(kind, b)["all_literal_terms_legal"]))


def dual_values(b: int) -> tuple[int, int, int, int]:
    """D4(V^b), D4(xV^b), Dz(V^b), Dz(xV^b)."""
    d4_v = 487635 - 32509 * b + 1653 * comb(b, 2) - 57 * comb(b, 3) + comb(b, 4)
    d4_xv = -32509 + 1653 * b - 57 * comb(b, 2) + comb(b, 3)
    return d4_v, d4_xv, b - 60, 1


def main() -> None:
    # Exact source legality, including each V-binomial Y/Z tail and all caps.
    k1_23, k1_24, k1_25 = (source_ledger("K1", b) for b in (23, 24, 25))
    k2_33, k2_34 = (source_ledger("K2", b) for b in (33, 34))
    assert (k1_23["minimum_margin"], k1_24["minimum_margin"], k1_25["minimum_margin"]) == (-3340, 13611, 30562)
    assert (k2_33["minimum_margin"], k2_34["minimum_margin"]) == (-14242, 2709)
    assert not bool(k1_23["all_literal_terms_legal"])
    assert bool(k1_24["all_literal_terms_legal"]) and bool(k1_25["all_literal_terms_legal"])
    assert not bool(k2_33["all_literal_terms_legal"]) and bool(k2_34["all_literal_terms_legal"])
    assert first_legal("K1") == k1_24
    assert first_legal("K2") == k2_34

    # Error values after the literal centered identities, with Y=1+x.
    # kappa and linear are respectively the constant and x coefficients.
    # K1: kappa=L*R-L', linear=-L'.
    # K2: A=2(L')^2-L*L''; kappa=A-2LL'R+L^2S, linear=A.
    d4v24, d4x24, dzv24, dzx24 = dual_values(24)
    d4v34, d4x34, dzv34, dzx34 = dual_values(34)
    assert (d4v24, d4x24, dzv24, dzx24) == (58905, -6545, -36, 1)
    assert (d4v34, d4x34, dzv34, dzx34) == (14950, -2300, -26, 1)
    # Each one-column pair has nonzero determinant, so a nonzero centered
    # linear factor cannot lie in the common kernel of D4 and Dz.
    assert 58905 - 36 * 6545 == -176715
    assert 14950 - 26 * 2300 == -44850
    assert all(0 < abs(n) < P for n in (176715, 44850))

    # The two cheapest species together have an exact generic augmented-rank
    # condition.  At kappa1=kappa2=1, linear1=linear2=0 (a valid flat local
    # specialization L=1,L'=L''=0,R=S=1), its determinant is -993330.
    flat_delta = 58905 * (-26) - 14950 * (-36)
    assert flat_delta == -993330 and flat_delta % P != 0
    def generic_delta(kappa1: int, linear1: int, kappa2: int, linear2: int) -> int:
        return ((58905 * kappa1 - 6545 * linear1) * (-26 * kappa2 + linear2)
                - (14950 * kappa2 - 2300 * linear2) * (-36 * kappa1 + linear1))
    assert generic_delta(2, 3, 5, 7) == (
        -993330 * 2 * 5 - 23895 * 2 * 7 + 155220 * 3 * 5 - 4245 * 3 * 7)

    cutoff = 4
    ms = rows(cutoff)
    assert ms == [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (4, 0), (1, 1)]
    labels = ["R57", "R58", "R59", "R60", "Phi2", "Phi3", "K1_24", "K2_34"]
    columns = [relay(n, cutoff) for n in range(57, 61)] + [phi2(cutoff), phi3(cutoff),
               centered_column(24, 1, 0, cutoff), centered_column(34, 1, 0, cutoff)]
    a = [[column.get(m, 0) for column in columns] for m in ms]
    b = target(ms)
    a_base = [row[:6] for row in a]
    a_k1 = [row[:7] for row in a]
    a_k2 = [row[:6] + [row[7]] for row in a]
    assert rank(a_base) == 5 and rank([row + [rhs] for row, rhs in zip(a_base, b)]) == 6
    assert rank(a_k1) == 6 and rank([row + [rhs] for row, rhs in zip(a_k1, b)]) == 7
    assert rank(a_k2) == 6 and rank([row + [rhs] for row, rhs in zip(a_k2, b)]) == 7
    assert rank(a) == rank([row + [rhs] for row, rhs in zip(a, b)]) == 7
    solution = solve(a, b)
    assert all(sum(a[i][j] * solution[j] for j in range(len(labels))) == b[i]
               for i in range(len(ms)))
    assert solution == [Fraction(-31630313, 2547), Fraction(61544021, 1698),
                        Fraction(-9971236, 283), Fraction(2267502127, 198666),
                        Fraction(-590249, 198666), Fraction(0),
                        Fraction(421201, 38205), Fraction(-1434349, 110370)]

    d4 = [487635, -32509, 1653, -57, 0, 1, 0]
    dz = [-60, 1, 0, 0, -58, 0, 1]
    assert dot(d4, b) == 455126 and dot(dz, b) == -59
    assert [dot(d4, [a[i][j] for i in range(len(ms))]) for j in range(6)] == [0] * 6
    assert [dot(dz, [a[i][j] for i in range(len(ms))]) for j in range(6)] == [0] * 6
    assert (dot(d4, [a[i][6] for i in range(len(ms))]), dot(dz, [a[i][6] for i in range(len(ms))])) == (58905, -36)
    assert (dot(d4, [a[i][7] for i in range(len(ms))]), dot(dz, [a[i][7] for i in range(len(ms))])) == (14950, -26)

    print("first legal centered K1 column:", k1_24)
    print("first legal centered K2 column:", k2_34)
    print("K1_24 dual pair = 58905*kappa1-6545*linear1, -36*kappa1+linear1")
    print("K2_34 dual pair = 14950*kappa2-2300*linear2, -26*kappa2+linear2")
    print("flat pair determinant =", flat_delta, "(nonzero mod p)")
    print("generic pair determinant = -993330*k1*k2-23895*k1*l2+155220*l1*k2-4245*l1*l2")
    print("flat one-breaker ranks: base+K1_24 is 6/7; base+K2_34 is 6/7")
    print("flat W<=4 augmented ranks = 7/7")
    print("flat exact amplitudes", dict(zip(labels, map(str, solution))))
    print("C_G ledger: L^36 V^24, L^35 V^25, L^26 V^34 each has order 60 before K factors")


if __name__ == "__main__":
    main()
