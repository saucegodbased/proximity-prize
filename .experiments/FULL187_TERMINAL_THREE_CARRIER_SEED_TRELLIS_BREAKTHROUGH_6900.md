# Full187 terminal three-carrier seed-trellis breakthrough

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Verdict

The opaque F101 grade-seven closure compresses exactly to **three explicit
terminal rows**, one for each of `F0,F1,F2`. Adding those three rows to the
grade-at-most-six source kills the three individual bordered defects and the
joint defect. None of the other 308 grade-seven monomial columns is needed.

The rows expose a scalable three-carrier recurrence. Put

```text
Q = Xi^2,
V = Y-QZ,
V1 = R-Q'Z,
b = J+1-m,
J1 = Lambda V1-Lambda' V.
```

For coefficient polynomials `A,B,c`, the terminal row is

```text
S(A,B,c)
 = V^(m-2) Z^b (c V^2 + B V Z + A Lambda Xi V1 Z).       (S)
```

The exact F101 coefficients satisfy

```text
B + A Xi Lambda' = Lambda C,                              (G)
B0 = B-cQ+2A Lambda Xi'.                                  (T)
```

Consequently `(S)` is equivalently the sum of the three honest agreement
cycles

```text
c V^m Z^b
+ C Lambda V^(m-1) Z^(b+1)
+ A Xi V^(m-2) J1 Z^(b+1).                               (3C)
```

It is also equivalently the raw four-term seed recurrence

```text
V^(m-2) Z^b [
    c Y^2
  + (B0-cQ-2A Lambda Xi') YZ
  + A Lambda Xi RZ
  - B0 Q Z^2 ].                                          (RAW)
```

The boundary-zero coefficient in `(RAW)` is exactly

```text
-B0 Q^(m-1),                                             (ZERO)
```

not the individually much larger tails of the three centered summands.
This cancellation is what makes the recurrence fit the literal tapered
source.

The target width audit is completely green, with four critical families
ending exactly at `D-1`. Every passive shift `Z^k S`, `0<=k<=2620`, remains
legal, giving a 2621-layer trellis from grade 83 through the load-bearing
final grade 2703. The remaining issue is the **iteration theorem** saying
that these layers propagate each forced `d=1,z=0` head to zero complete error
contact. That theorem is still open, so this is not yet a 6900 proof.

One must not extrapolate the one-layer F101 closure to one target layer. The
target cumulative margin through grade 82 is `-334311837024` and becomes
positive only at grade 2703. All 2621 shifted layers, not just grade 83, are
load-bearing in the target argument.

## 1. Why the three displayed carriers are agreement cycles

At every agreement node, `V` has contact order one. The first transvectant

```text
J1 = Lambda V1-Lambda' V
```

has contact order two. `Lambda` has contact order one and `Xi` is a unit on
the agreement set. Thus the three terms in `(3C)` have contact orders

```text
m,
1+(m-1)=m,
(m-2)+2=m.
```

This proves `C_G S=0` without relying on cancellation against lower source
grades. Since every raw term of `S` has total source grade `J+1`, its
boundary-one terms have positive passive seed exponent. Hence its exact
polynomial `J_YRS` normal is zero as well.

Condition `(G)` is exactly what turns the compact `A,B,c` formula into the
three agreement cycles: substitute `B=Lambda C-A Xi Lambda'` into `(S)` and
collect `V`.

Condition `(T)` uses `Q'=2 Xi Xi'`. Expanding the inner bracket in raw
variables gives `(RAW)` by a ring identity. In particular, setting `Y=R=0`
leaves `-B0 Q Z^2`; multiplication by `V^(m-2)` then gives `(ZERO)`.

These are coupled identities. Bounding `B V^(m-1)` and
`A Lambda Xi V1 V^(m-2)` separately loses their cancellation and produces a
false width failure.

## 2. Exact F101 closure with only three terminal rows

The faithful chamber is

```text
F101,
(n,w,g,m,D,s,t,J,L)=(11,5,8,4,32,1,1,6,10),
G={0,...,7}, E={8,9,10}, Q=Xi_E^2.
```

The exact solve in `f101_grade7_correction_factor_probe_6900.py` gives, for
all three RHS,

```text
(deg A,deg B,deg c,deg B0,deg C)=(4,14,0,13,6).
```

The new reproducer rebuilds the three polynomials, expands `(S)` into the
literal source, and checks independently:

* every raw monomial is source-legal;
* every term has grade seven;
* `C_G S=0` exactly;
* `J_YRS S=0` exactly;
* `(G)`, `(T)`, and `(ZERO)` are exact polynomial identities;
* the boundary-zero coefficient has degree `31=D-1` for every RHS.

The actual bordered ranks are

| source | columns added | rank | individual defects | joint defect |
|---|---:|---:|:---:|---:|
| grades `<=6` | 1463 | 1461 | `1,1,1` | 3 |
| grades `<=6` plus the three rows `(S)` | 3 | 1464 | `0,0,0` | 0 |

Thus the three terminal rows are independent modulo the lower-grade image
and close precisely the three requested RHS. This is stronger than the old
statement that all 311 grade-seven columns close the border.

For each `Fi`, bordered membership gives a source element `Ki` with

```text
C Ki=0,    J_YRS Ki=J_YRS Fi.
```

Therefore `Ki-Fi` is an exact `J_YRS=0` row, is zero on all agreement
contacts, and cancels the complete error contact of the forced centered
`Fi` head. This is the requested finite coupled head-to-correction receipt;
it is not merely a value-endpoint check.

The three terminal source hashes are

```text
F0 8343c51254f0481d8657c2cda6ee8c49a4e3d8d09b3c66f55236a49fdb0c3af8
F1 8e4611cfd9bcea935ea57f6b213a7546ec502a490d1564667fd17fddc5c8d8e4
F2 f1ec511fd326af3451f10d12fb38e62c32f3b0fb4322762d05505983af76fc20
```

Each terminal row has 66 nonzero error-contact coordinates, 22 at each of
the three errors. Its source support is respectively `157,157,158`.

## 3. Exact coefficient-existence parameterization

The agreement congruence does not require guessing `B`. Given `A,c` and a
free polynomial `H`, let

```text
P  = cQ+A Xi Lambda',
r  = P mod Lambda,
B0 = -r+Lambda H,
B  = B0+cQ-2A Lambda Xi'.                               (PARAM)
```

Then

```text
B+A Xi Lambda'
 = (P-r)+Lambda H-2A Lambda Xi'
```

is divisible by `Lambda`, so `(G)` holds. Conversely, every solution of
`(G)` is represented by this congruence class. This gives an explicit
coefficient producer for every terminal agreement cycle; it is not a
dimension-only existence claim.

At the target, `deg Lambda=g=180413`. If

```text
deg H < 1000109,
```

then `deg(Lambda H)<=1180521`, while `deg r<g`, so `(PARAM)` guarantees

```text
deg B0 <=1180521.
```

There is room for twelve independent Hermite coefficients at every error:

```text
12e = 980772 < 1000109.
```

This is useful interpolation room, but by itself it does not prove that the
lower-grade residual asks for only those twelve jets.

## 4. Literal target widths

Use the worst target stratum

```text
(N,w,g,e,m,D,J,L)
 =(262144,131071,180413,81731,60,10824780,82,2703),
deg Q=2e=163462,
b=J+1-m=23.
```

Choose the inclusive coefficient-degree caps

```text
deg A  <=  950769,
deg B0 <= 1180521,
deg c  <= 1049450.                                     (CAP)
```

Expanding `V^58` in `(RAW)`, the exact maximum of
`coefficient degree + literal source weight` over every raw `Y` strip is:

| raw family | `Y` range | maximum | margin to strict `D` |
|---|---:|---:|---:|
| `A Lambda Xi R Z V^58` | `0..58` | 10824779 | 1 |
| `-2A Lambda Xi' Y Z V^58` | `1..59` | 10824779 | 1 |
| `-B0 Q Z^2 V^58` | `0..58` | 10824779 | 1 |
| `B0 Y Z V^58` | `1..59` | 10792388 | 32392 |
| `c Y^2 V^58` | `2..60` | 10792388 | 32392 |
| `-c Q Y Z V^58` | `1..59` | 10824779 | 1 |

The margin improves by exactly

```text
2e-w = 32391
```

for every step away from the dangerous low-`Y` endpoint. The active degree
is at most `60<=82`, the slope degree is at most `1<=21`, curvature is zero,
and every term has total grade

```text
60+23=83<=2703.
```

So there is no target inequality failure. Four families saturate `D-1`,
which also means the coupled cancellation cannot be weakened casually.

Multiplication by an additional `Z^k` changes no `X` degree, active degree,
slope, or curvature. It changes the total grade from 83 to `83+k`. Hence all

```text
k=0,...,2620
```

are legal and give exactly the source grades `83,...,2703`. On the error
side this is a lower-triangular passive-seed recurrence: `Z^k` shifts the
lowest output seed by `k`, while direction-mismatch terms can only leak to
higher seed. Proving that the full diagonal block has the required image is
the remaining contact theorem.

The raw coefficient spaces under `(CAP)` have dimensions

```text
A:  950770,
B0: 1180522,
c: 1049451,
total: 3180743.
```

Imposing a degree-`g` congruence costs at most `180413`, leaving at least
`3000330` dimensions. Even the subfamily with constant `c` leaves at least

```text
950770+1180522+1-180413 = 1950880 > 4e=326924.
```

These counts certify room; they do not substitute for the target contact-map
surjectivity statement.

## 5. Smallest exact completion lemma

The result reduces the Full187 producer to the following statement.

> **Shifted three-carrier trellis lemma (OPEN).** For each of the three forced
> locator normals `Fi`, there exist a literal source row `Li` of total grade
> at most 82 and target-legal coefficient polynomials `Ai,k,ci,k,Hi,k` for
> `0<=k<=2620`, satisfying `(CAP)` and `(PARAM)` layerwise, such that, with
> `Si,k=Z^k S(Ai,k,Bi,k,ci,k)`,
> ```text
> (C,J_YRS)(Li + sum_k Si,k)=(0,J_YRS Fi).
> ```

Equivalently, the seed-lower-triangular PC/HRS recurrence starting from the
forced `d=1,z=0` head must be solvable through its final seed layer, using
the explicit three-carrier diagonal family `(3C)` at every step.

This is the only unproved **THREE-RHS bridge within this source route**. The
terminal family itself
is an honest `C_G=0`, `J_YRS=0` source family; the exact F101 analogue closes
all three RHS using only three members; its coefficient congruence has an
explicit solution; and every target source inequality is now checked. What
is not yet justified is surjectivity of the full 2621-layer target contact
trellis. A single grade-83 layer cannot suffice by the exact target margin.
Even after this lemma, the independent `Z1` direction and the downstream
typed Full187 producer/allocation into the benchmark claim must still be
completed; this note makes no end-to-end 6900 claim.

## Reproduction

```text
python3 -m py_compile \
  .experiments/f101_terminal_seed_trellis_three_carrier_6900.py
python3 -B \
  .experiments/f101_terminal_seed_trellis_three_carrier_6900.py

.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187TerminalSeedTrellisWidth6900.lean
```

Python canonical receipt:

```text
ce2b6053f625bd6bf08ee0d700e0fe78c802814dd4f3e7607c7bb833785fcf8f
```

The Lean width audit builds under the four-GiB cap. Its printed axioms are
only standard `propext`, `Quot.sound`, and (for finite arithmetic packaging)
`Classical.choice`; there is no `sorry`, `decide`, or `native_decide`.
