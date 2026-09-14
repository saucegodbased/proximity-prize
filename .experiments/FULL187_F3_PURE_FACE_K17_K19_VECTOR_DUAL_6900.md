# Full187 F3 pure face: exact coupled k17--k19 vector gate

Date: 2026-09-14

## Scope and dimensions

This strengthens the exact `k=17,18` gate by adding an Euler row at `k=19`.
Choose

```text
P19(t)=(t-29)*product_(n=31)^70(t-n).
```

It roots all 39 correction lanes individually onto `Fp[X]/E^19`, plus lanes
29 and 31.  Retain only the four legal lanes `A2,A29,A71,A72`, whose widths
are

```text
98684 + 1430918 + 1518739 + 1387668 = 4436009.
```

The three codomains have `17E+18E+19E=4413474` rows, so this restricted
primal map has surplus 22,535.  Unlike a single scalar projection, this is a
genuinely coupled three-row test.

## Literal rows

The exact target-field values are

```text
P17(2),P17(72)          = 842546268,1616860076,
P18(2),P18(29),P18(72) = 1389265538,1276384207,1276384207,
P19(2),P19(29),P19(71),P19(72)
                         = 13670302,0,1174437213,1661892046.
```

Normalize at `A72,A29,A71`, respectively.  On `(A2,A29,A71,A72)` the rows
are

```text
(a1,0,0,1), (a2,1,0,1), (a3,0,1,c3),
(a1,a2,a3,c3)=(931238467,95217577,570758121,558042203).
```

## Exact dual compression

In `M=E^19`, embed the three duals as `x=E^2*g17`, `y=E*g18`, `z=g19`.
The `A29,A71,A72` annihilator conditions imply

```text
z in W_34150,
y=E*(G^-31*r0 mod E^18),       r0 in W_40240,
gA=E*hbar+c3*z+E^2*u,          u in W_1759,
hbar=(E^-1*y) mod E.
```

Thus only `40240+34150+1759=76149` dual variables remain for the 98,684
terminal `A2` equations; their difference is again 22,535.

Put `(G^31 mod E)hbar-E*c0=r0`.  Eliminating the remaining 18-adic lift gives
the exact output

```text
G^58*gQ =
  a2*E*G^58*hbar
  +(a1-a2)*E^2*G^27*c0
  +a3*G^58*z
  +a1*E^2*G^58*u                  mod E^19.
```

The `c3` term cancels identically.  Reversing the low-remainder equation and
this output congruence yields a `5 x 2` PM-basis instance with effective
orders

```text
o1=123222, o2=180415,
first-column shift=57193,
unknown bounds (81731,81731,34150,1759,81731),
initial shift (0,0,47581,79972,0), threshold=81730.
```

The expected determinant degree is `o1+o2=303637`.  Exact non-palindromic
test polynomials check both reversal orientations before the instance is
written.

## Resource go/no-go

The generated series file is 5,051,716 bytes and generation peaks at 459,496
KiB.  Extrapolating from the certified `4 x 2` predecessor (954,224 KiB), the
`5 x 2` basis is safely below the requested 3 GiB cap, so the exact run is
authorized.  A dense `98684 x 76149` matrix is never materialized.

## Decision

**GREEN: the three-row dual is injective.**  LinBox returned the perfectly
balanced shifted row degrees

```text
(86238,86238,86238,86238,86238),
```

all 4,508 above the candidate threshold 81,730.  Therefore the exact
`76149 -> 98684` dual map has zero kernel.  Equivalently, the four retained
lanes are already surjective on all three coupled Euler rows.

The independent FLINT verifier checked all ten basis-times-series products,
the exact shift gain `303637`, and shifted leading determinant `-1` modulo
the target prime.  Receipts:

```text
input bytes                       5,051,716
input sha256  6f4f43aa939bdb833c8fdf3f9b68b554327dcde4557c424acbe04f2e9bff8dbd
basis bytes                       9,132,860
basis sha256  05ddafb3e2fe90d08abeb962bd60faa35c4a5554d37f9ff361d0edc264f90e0c
PM-basis peak RSS                 1,417,268 KiB
independent verifier peak RSS        62,120 KiB
```

Because this left kernel is zero, the exact fixed-boundary residue cannot be
obstructed by these three rows: it is covered for every right-hand side on
this projection.  This remains a local projected-coverage result, not a full
pure-face membership certificate.

## Reproduction

```bash
python3 -B \
  .experiments/full187_f3_pure_face_k17_k19_vector_dual_6900.py \
  --generate

g++ -O3 -std=c++17 \
  .experiments/full187_f3_pure_face_k17_k19_vector_dual_6900.cpp \
  -o /tmp/full187_f3_pure_face_k17_k19_vector_dual_6900 \
  $(pkg-config --cflags --libs linbox)

prlimit --as=3221225472 --cpu=900 -- \
  /tmp/full187_f3_pure_face_k17_k19_vector_dual_6900

python3 -B \
  .experiments/full187_f3_pure_face_k17_k19_vector_dual_6900.py \
  --verify-basis
```
