# Full187 pure-V fat-point product and rounding audit

Date: 2026-09-13 UTC. Scope: lower-6900 research only. This note adds no
production source, claim, score, or submission change.

## Result

The full passive-`R` pure-`V` contact has a clean exact bivariate model, but
the desired coefficient-independent injectivity theorem does **not** follow
from only

```text
wt(X)=1, wt(V)=2e,    2e < g < 3e.
```

An exact small Groebner computation gives a counterexample inside that
chamber. Consequently this work cannot honestly close the target pure-`V`
source. It does close a modelling gap: the (b=66) lane is real, has width
36,288, and is included in the all-lane finite control rather than rounded
away.

## Exact ideal model

Let `A` be the passive coefficient ring (for the literal passive direction,
take `A=K[R]`) and work in `A[X,V]`.  Put

```text
I_G = (L,V)^m,                 I_E = (H,V-1)^m.
```

`R` is passive here: it remains in the coefficient ring, so the identity is
unchanged coefficientwise in every passive-`R` degree.  This is precisely
the bivariate part of full passive-`R` contact, rather than a fixed-degree or
single-packet simplification.

The underlying ideals are comaximal without a locator assumption, since
`V in (L,V)` and `1-V in (H,V-1)`. Their powers are comaximal as well, hence

```text
I_G ∩ I_E = I_G I_E.                                      (1)
```

For the literal ladder, set `D=mg`, `B=floor((D-1)/(2e))`, and

```text
S = direct_sum_(b=2)^B L^max(m-b,0) K[X]_<w_b V^b,
w_b = D - 2e*b - g*max(m-b,0).
```

Thus `S` is the complete source-shaped weighted strip inside `I_G`; it is
not a chosen schedule.  The desired `F0` correction asks for `h in S` such
that

```text
h - L^(m-1)V in I_E.                                     (2)
```

Since `L^(m-1)V` is already in `I_G`, (2) makes the difference an element of
the product in (1). Therefore a genuine filtered-product initial-degree
theorem would imply the full pure-`V` STOP in one stroke. This is the exact
place where the unproved theorem is needed.

## Exact target rounding ledger

At the target

```text
(e,g,m) = (81731,180413,60),
D = 10824780,  2e = 163462,
B = floor((D-1)/(2e)) = 66.
```

The last unsaturated lane is `b=60`; its width is `b(g-2e)`. The six
high lanes have widths

```text
b = 61,62,63,64,65,66
w = 853598,690136,526674,363212,199750,36288.
```

`b=67` has width zero. The 65 lanes `b=2,...,66` total exactly
33,673,037 coefficients. The `b=66` width is less than `deg H=81,731`, but
that fact alone is not a divisibility proof.

`Full187PureVFatPointArithmeticGate6900.lean` checks this ceiling, the
strict `b=67` failure, the total source count, and the corrected degree-`e`
fixed-inverse endpoint inequality. It contains no axiom or unproved
algebraic injectivity assertion.

## Small exact Groebner evidence and its limitation

The companion Singular script computes `std(I_G*I_E)`, independently
computes `std(intersect(I_G,I_E))`, reduces both ways, and reports leading
exponents for the indicated weighted order.

| fixture | chamber | `m g` | least weighted leading degree | interpretation |
|---|---:|---:|---:|---|
| `e=3,g=7,m=8`, over F_101 | `6<7<9` | 56 | 62 | filtered product empty below the cutoff |
| `e=2,g=5,m=6`, over F_101 | `4<5<6` | 30 | 30 | sharp at the strict cutoff |
| `e=10,g=29,m=4`, over F_1009 | `20<29<30` | 116 | 114 | **counterexample** to the chamber-only theorem |

In the counterfixture the leading monomial is `X^94 V`, whose weight is
`94+20=114`. It belongs to `I_G^4 I_E^4=I_G^4 intersect I_E^4`, so it is a
nonzero product element strictly below `mg=116`. This is an exact algebraic
counterexample, not a rank heuristic. A target theorem needs a stronger
hypothesis than the two stated chamber inequalities, or a target-specific
approximant/duality argument.

## Complete-ladder finite control with the missing high lanes

`full187_pure_v_fatpoint_injectivity_control_6900.py` evaluates all Hasse
jets of total order `<m` at all error nodes. A kernel vector is exactly a
source-shaped element of `S intersect I_E`; the augmented column tests (2).
It includes every legal `b`, not a fixed homogeneous degree or selected
packet.

The deep ratio-near control is

```text
(e,g,m)=(5,11,61),  wt(V)=10,  B=67=m+6,
field F_101.
```

It uses the whole `b=2,...,67` source, 2,046 columns and 9,455 error-jet
rows. Its exact ranks are `2046/2047` (matrix/augmented), so its intersection
kernel is zero and `L^60 V` is not in the full source image. It completed
under `--as=4294967296`, peak RSS 787,528 KiB. This is useful evidence that
the `m+6` rounding tail does not itself create a finite-field escape; it is
not a target-field theorem.

## Actual-domain inverse correction

For the actual NTT locator `Omega=X^N-1`, one has

```text
Omega' = N X^(N-1),
A = N^(-1) X H',
1 - L A = -Omega + (N^(-1) X L') H.
```

Hence `LA=1 mod H`, and `deg A=e`, not `e-1`. This corrects the earlier
constant-derivative surrogate and strengthens any natural inverse-packet
endpoint estimate by one degree. It does not prove the arbitrary
cross-`H`-stratum product injectivity missing above.

## Reproduction receipts

```text
python3 -m py_compile .experiments/full187_pure_v_fatpoint_injectivity_control_6900.py
prlimit --as=4294967296 --cpu=180 -- Singular -q \
  .experiments/full187_pure_v_fatpoint_groebner_6900.sing
prlimit --as=4294967296 --cpu=900 -- python3 \
  .experiments/full187_pure_v_fatpoint_injectivity_control_6900.py --case rounding
python3 .experiments/full187_pure_v_fatpoint_injectivity_control_6900.py --case target
```

The canonical SHA256 values recorded on this workspace are:

```text
Singular complete output: c1ad1312d0457999b310f1c68ad766a4e057f7eb0eed136808fbeec9e307ee7f
small all-lane control:  60ba00ad93a3f7dad219fafd5797f7550217fea620d8f8fafdd4f655a406e819
deep m+6 control:        ce3e2de2e07f754b4211fa1ae43bb4a659d77f6d02dcb966a8b0c3322cefca94
target rounding ledger:  6152aff8d20b779514896a3ef3e2e110a33a22cdedcae2f7c980dcfd3950d235
```

## Honest conclusion

The requested bivariate model, product equality, target `b=66` arithmetic,
and an all-lane `m+6` finite control are complete. The proposed universal
weighted-initial-degree theorem is false as stated, and no replacement
coefficient-independent target theorem is proved here. Therefore this is a
research STOP on the chamber-only proof route, not a proof that the target
pure-`V` source is closed.
