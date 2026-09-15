#!/usr/bin/env python3
"""Exact asymmetric second-jet source and resultant arithmetic for score 6900.

The source monomials obey

  r1 + r2 <= s,     r2 <= t,

where r1 and r2 are the exponents of P' and P''.  The old consecutive-jet
experiment was the special case t=s.  For a homogeneous jet layer d, the
one-node contact module is reduced to shifted weak Popov form over F_p[T].
The row shift is 3 times the exponent of the error coordinate E, because

  P = E + T P' - T^2/2 P'',       contact_weight(E)=3.

The resulting shifted leading degrees are the literal invariant valuations;
the truncated rank is sum_v max(m-v,0).  This avoids assuming a closed Smith
formula for the asymmetric staircase.  Small cases are checked against the
independent literal expansion in higher_jet_literal_matrix.py.

If two rows of actual P'' degrees a,b have nonzero P''-resultant, Sylvester
isobaricity says every resultant monomial contains a+b coefficient factors
and has total eliminated-index weight a*b.  For equal caps a=b=t this gives
the exact cumulative Fin4 controls

  weighted = 2*t*D - (w-2)*t^2
  total    = 2*t*L - t^2
  middle   = 2*t*M - t^2
  slope    = 2*t*s - t^2.

"""

from __future__ import annotations

from dataclasses import dataclass
from functools import cache
from math import comb
import argparse


N = 262_144
W = 131_071
A = 180_413
P = 1_000_003

Row = tuple[int, int, int]       # (E exponent, P' exponent, P'' exponent)
Term = tuple[Row, int]           # row and T degree
Vector = dict[Term, int]


def _leading(v: Vector) -> tuple[Row, int, int, int]:
    """Return the lowest contact term (row, T degree, coefficient, weight)."""
    (row, degree), coefficient = min(
        v.items(), key=lambda item: (item[0][1] + 3 * item[0][0][0], item[0][0]))
    return row, degree, coefficient, degree + 3 * row[0]


def _sub_shifted(v: Vector, b: Vector, shift: int, scale: int) -> None:
    for (row, degree), coefficient in b.items():
        key = (row, degree + shift)
        value = (v.get(key, 0) - scale * coefficient) % P
        if value:
            v[key] = value
        else:
            v.pop(key, None)


def _generator(d: int, r1: int, r2: int) -> Vector:
    """Expand P^(d-r1-r2) (P')^r1 (P'')^r2 in the contact chart."""
    r0 = d - r1 - r2
    inv2 = pow(2, -1, P)
    out: Vector = {}
    for e in range(r0 + 1):
        for c in range(r0 - e + 1):
            b = r0 - e - c
            coefficient = comb(r0, e) * comb(r0 - e, c)
            coefficient = coefficient * pow(-inv2, c, P) % P
            row = (e, b + r1, c + r2)
            degree = b + 2 * c
            key = (row, degree)
            out[key] = (out.get(key, 0) + coefficient) % P
    return {key: value for key, value in out.items() if value}


@cache
def invariant_valuations(q: int, t: int) -> tuple[int, ...]:
    """Shifted weak-Popov valuations for the d=q asymmetric jet layer."""
    t = min(q, t)
    basis: dict[Row, Vector] = {}
    for r2 in range(t + 1):
        for r1 in range(q - r2 + 1):
            v = _generator(q, r1, r2)
            while v:
                row, degree, coefficient, _ = _leading(v)
                if row not in basis:
                    basis[row] = v
                    break
                bvec = basis[row]
                _, bdegree, bcoefficient, _ = _leading(bvec)
                if degree < bdegree:
                    basis[row], v = v, bvec
                    bvec = basis[row]
                    _, bdegree, bcoefficient, _ = _leading(bvec)
                scale = coefficient * pow(bcoefficient, -1, P) % P
                _sub_shifted(v, bvec, degree - bdegree, scale)
    expected = sum(q - r2 + 1 for r2 in range(t + 1))
    assert len(basis) == expected
    values = sorted(_leading(v)[3] for v in basis.values())
    return tuple(values)


def derivative_count(q: int, t: int) -> int:
    t = min(q, t)
    return sum(q - r2 + 1 for r2 in range(t + 1))


def derivative_moment(q: int, t: int) -> int:
    """Sum of r1+2*r2 over r1+r2<=q, r2<=t."""
    t = min(q, t)
    return sum(
        (q - r2) * (q - r2 + 1) // 2 + 2 * r2 * (q - r2 + 1)
        for r2 in range(t + 1))


def local_rank_layer(m: int, d: int, s: int, t: int) -> int:
    q = min(d, s)
    shift = d - q
    return sum(max(m - shift - value, 0) for value in invariant_valuations(q, t))


def column_layer(m: int, d: int, s: int, t: int) -> int:
    base = m * A - W * d
    assert base > 0
    q = min(d, s)
    return derivative_count(q, t) * base + derivative_moment(q, t)


@dataclass(frozen=True)
class Source:
    m: int
    s: int
    t: int
    M: int
    L: int
    columns: int
    local_rank: int
    margin: int

    @property
    def weighted(self) -> int:
        return 2 * self.t * self.m * A - (W - 2) * self.t * self.t

    @property
    def total(self) -> int:
        return 2 * self.t * self.L - self.t * self.t

    @property
    def middle(self) -> int:
        return 2 * self.t * self.M - self.t * self.t

    @property
    def slope(self) -> int:
        return 2 * self.t * self.s - self.t * self.t

    @property
    def flag(self) -> tuple[int, int, int]:
        return (self.total - self.middle,
                self.middle - self.slope,
                self.slope)


def source_at(m: int, s: int, t: int, M: int, L: int) -> Source:
    columns = rank = 0
    for d in range(M + 1):
        multiplicity = L - d + 1
        columns += multiplicity * column_layer(m, d, s, t)
        rank += multiplicity * local_rank_layer(m, d, s, t)
    return Source(m, s, t, M, L, columns, rank, columns - N * rank)


def minimum_seed_height(m: int, s: int, t: int,
                        minimum_margin: int = 2) -> list[Source]:
    """For every interior jet cap M, return its least green L>=M."""
    dmax = (m * A - 1) // W
    gap_sum = weighted_gap_sum = 0
    column_sum = rank_sum = 0
    weighted_columns = weighted_rank = 0
    out: list[Source] = []
    for d in range(dmax + 1):
        c = column_layer(m, d, s, t)
        r = local_rank_layer(m, d, s, t)
        g = c - N * r
        column_sum += c
        rank_sum += r
        weighted_columns += d * c
        weighted_rank += d * r
        gap_sum += g
        weighted_gap_sum += d * g
        # margin(L)=(L+1)*gap_sum-weighted_gap_sum.
        if gap_sum > 0:
            required = (weighted_gap_sum + minimum_margin + gap_sum - 1) // gap_sum - 1
            L = max(d, required)
            margin = (L + 1) * gap_sum - weighted_gap_sum
            if margin >= minimum_margin:
                columns = (L + 1) * column_sum - weighted_columns
                rank = (L + 1) * rank_sum - weighted_rank
                out.append(Source(m, s, t, d, L, columns, rank,
                                  columns - N * rank))
        elif (d + 1) * gap_sum - weighted_gap_sum >= minimum_margin:
            columns = (d + 1) * column_sum - weighted_columns
            rank = (d + 1) * rank_sum - weighted_rank
            out.append(Source(m, s, t, d, d, columns, rank,
                              columns - N * rank))
    return out


def flag_mixed(p:tuple[int,int,int], q:tuple[int,int,int],
               r:tuple[int,int,int]) -> int:
    z,y,a=p; Z,Y,Aa=q; zz,yy,aa=r
    return (a*Aa*aa +
      (z*Aa*aa+Z*a*aa+zz*a*Aa) +
      (y*Aa*aa+Y*a*aa+yy*a*Aa) +
      (a*Y*yy+Aa*y*yy+aa*y*Y) +
      (z*Y*aa+z*yy*Aa+Z*y*aa+Z*yy*a+zz*y*Aa+zz*Y*a))


def hybrid_cost(p:tuple[int,int,int]) -> int:
    z,y,a=p
    s=a; middle=y+a; total=z+y+a
    sharp=(2*(total-middle)*131072,
           1+(2*(middle-s)-1)*131072,
           (2*s-1)*131072)
    rational=(131074*(total-middle),
              131074*(middle-s-1)+2,
              131074*(s-2)+3)
    hcoord=(rational[0],rational[1]+65536,rational[2]+196608)
    mfiber=(total-middle,middle-s,s+1)
    mcut=(rational[0],rational[1]+131072,rational[2]+262144)
    return flag_mixed(p,sharp,hcoord)+131072*flag_mixed(p,mfiber,mcut)


def controls() -> None:
    # The asymmetric algorithm at t=q is the closed Smith formula
    # d-q+3*b with multiplicity q-b+1.
    for q in range(8):
        expected = sorted(3*b for b in range(q+1) for _ in range(q-b+1))
        assert list(invariant_valuations(q,q)) == expected
    # Explicit asymmetric multisets independently recovered by the literal
    # truncated matrices (see log and higher_jet_literal_matrix.py).
    assert invariant_valuations(4,0) == (0,2,4,6,8)
    assert invariant_valuations(4,1) == (0,0,2,3,4,5,6,7,9)
    assert invariant_valuations(4,2) == (0,0,0,2,3,3,4,5,6,7,8,10)


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,default=150)
    parser.add_argument("--s",type=int,default=41)
    parser.add_argument("--tmin",type=int,default=0)
    parser.add_argument("--tmax",type=int,default=10)
    args=parser.parse_args()
    controls()
    print("CONTROLS_OK")
    for t in range(args.tmin,args.tmax+1):
        rows=minimum_seed_height(args.m,args.s,t)
        if not rows:
            print("RED",args.m,args.s,t)
            continue
        best=min(rows,key=lambda row:(hybrid_cost(row.flag),row.total,row.middle,row.slope))
        print("GREEN",best,"weighted",best.weighted,"cumulative",
              (best.total,best.middle,best.slope),"flag",best.flag,
              "hybrid",hybrid_cost(best.flag))


if __name__=="__main__":
    main()
