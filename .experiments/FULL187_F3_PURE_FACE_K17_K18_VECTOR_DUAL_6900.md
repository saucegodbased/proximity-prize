# Full187 F3 pure face: exact coupled k17/k18 vector gate

Date: 2026-09-14

## Scope

This is the first genuinely coupled dual gate after the scalar Euler
projections in `FULL187_F3_PURE_FACE_GRAPH_TRANSFORM_6900.md`.  It decides
whether the three legal correction lanes `A2,A29,A72` already cover the two
Euler rows at orders 17 and 18.  It is a necessary-face/local coverage test,
not a construction of the full F3 lift.

The computation uses the literal target prime and locators.  It never forms
the `98684 x 41999` coefficient matrix.

## Literal coefficient correction

Let

```text
P18(t)=product_(n=30)^71(t-n),
P17(t)=(t-29)P18(t).
```

Direct products in `Fp`, `p=2130706433`, give

```text
P17(2)  =  842546268,   P17(72) = 1616860076,
P18(2)  = 1389265538,   P18(72) = 1276384207,
P18(29) = 1276384207.
```

Their literal `q,a` determinant is `865507203`, inverse `471227111`.
Normalize the rows by their `a` entries:

```text
a1=P17(2)/P17(72)=931238467,
a2=P18(2)/P18(72)= 95217577,
rows on (q,a,r): (a1,1,0), (a2,1,1).
```

The normalized determinant is `a1-a2=836020890`, nonzero.  The previously
reported rows `(-27,43,0),(1,1,1)` were invalid: they implicitly equated
`P18(2)` and `P18(72)`.  They are not used here.

## Exact 41,999-variable dual

Let `M=E^18`, and embed the order-17 dual by `x=E*g17`; write `y=g18`.
Residue pairing with the three lanes gives

```text
gA = x+y,
gQ = a1*x+a2*y,
deg(G^31 y mod M) < 40240,
deg gA < 83490,
deg(G^58 gQ mod M) < 1372474.
```

The first two degree conditions uniquely parameterize

```text
r0 in W_40240, z in W_1759,
y  = G^-31 r0 mod M,
gA = (y mod E)+E*z,
gQ = a1*gA+(a2-a1)*y.
```

Thus the last condition is an exact `41999 -> 98684` structured map.  The
equation surplus `56685` agrees with the primal surplus
`(98684+1387668+1430918)-(17E+18E)=56685`.

## Exact polynomial kernel and reciprocal PM-basis formulation

The 18-adic lift can be eliminated before computation.  Put

```text
y0 = y mod E,
G^31*y0 - E*c0 = r,             deg r < 40240.
```

Writing `y=y0+E*h` gives `G^31*h=-c0 mod E^17`; therefore

```text
E*G^58*h = -E*G^27*c0 mod E^18.
```

Consequently a dual kernel is exactly a bounded solution of

```text
(G^31 mod E)*y0 - E*c0 - r = 0,
a2*G^58*y0 + (a1-a2)*E*G^27*c0 + a1*E*G^58*z - w = 0 mod E^18,
```

with strict bounds in the direct formulation

```text
deg(y0,c0,z,r,w,s) < (81731,81731,1759,40240,1372474,81731),
```

where `s` is the quotient in the second equation.  A literal `6 x 2`, order
1,552,889 encoding is exact but exceeded the 4 GiB experiment cap inside
LinBox.  It was stopped and is not used as evidence.

Instead reverse the first equation at degree `2E-1` and the second at degree
`18E+E-1`.  The free low remainders disappear.  With fixed-length reversed
unknowns `(Y,C,Z,S)` of bounds `(81731,81731,1759,81731)`, the two effective
orders are

```text
o1 = 2E-40240 = 123222,
o2 = E+98684  = 180415.
```

Multiplying the first series column by `x^(o2-o1)=x^57193` turns this into one
ordinary `4 x 2`, order-180415 PM-basis call.  Its initial shift is
`(0,0,79972,0)` and candidate threshold `81730`.  The first column has exact
valuation 57193 and the second is primitive independently, so the expected
approximant determinant degree/shift gain is

```text
(o2-57193)+o2 = o1+o2 = 303637.
```

This reciprocal system is bijectively equivalent to the bounded direct
kernel; it changes neither a coefficient window nor a CRT tail.

## Decision

**GREEN: the coupled dual is injective.**  LinBox returned shifted row degrees

```text
(95902,95903,95902,95902),
```

where every row is at least 14,172 above the candidate threshold 81,730.
Thus the `41999 -> 98684` dual map has zero kernel.  Equivalently, the
restricted three-lane primal map is surjective on these two coupled Euler
rows.

An independent FLINT pass checked all eight basis-times-series products
vanish modulo `x^180415`, the exact shift gain is `303637=o1+o2`, and the
shift-leading determinant is 1.  Receipts:

```text
input bytes                       4,330,048
input sha256  ed9fef599c7906fcc7bc3faadd7ae23e613081094726af88686bc20ea362efb5
basis bytes                       6,518,132
basis sha256  6db05c2fccbd24330df52b99f2aaec0c0f3119b6d2d2aa87c3e532f3b1eb732f
PM-basis peak RSS                   954,224 KiB
independent verifier peak RSS        64,812 KiB
```

This is a local coverage result, not full pure-face membership.  In
particular it does not claim that the exact 60-component boundary residue is
globally covered.  Because the coupled left kernel is zero, there is no
`k17/k18` dual with which to obstruct that residue; a stronger test must add
another Hasse/Euler row (next: `k=19`) or test the exact residue directly.

## Reproduction

```bash
python3 -B \
  .experiments/full187_f3_pure_face_k17_k18_vector_dual_6900.py \
  --generate

g++ -O3 -std=c++17 \
  .experiments/full187_f3_pure_face_k17_k18_vector_dual_6900.cpp \
  -o /tmp/full187_f3_pure_face_k17_k18_vector_dual_6900 \
  $(pkg-config --cflags --libs linbox)

prlimit --as=4294967296 --cpu=900 -- \
  /tmp/full187_f3_pure_face_k17_k18_vector_dual_6900

python3 -B \
  .experiments/full187_f3_pure_face_k17_k18_vector_dual_6900.py \
  --verify-basis
```
