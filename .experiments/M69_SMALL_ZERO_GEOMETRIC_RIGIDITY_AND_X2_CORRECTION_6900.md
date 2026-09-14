# m69 small-zero geometric rigidity and the corrected dual recurrence

Date: 2026-09-14 UTC. Scope: lower target 6900 only. No production source,
claim, score, candidate, or submission is changed.

## Decision

The alternating high/low m69 route yields a real structural reduction, but
it does not yet close 6900.

1. The physical prefix map gives the recurrence

   ```text
   N0^2 K_j = E0^2 K_(j+1)   on the NTT domain.
   ```

   There is **no `X^2` factor**. The `X^2` in
   `M69RationalTwoPowerGate6900.lean` and the first many-zero draft was an
   unadapted conditional premise, not a consequence of the advertised
   source `sum_t (N0/E0)^t F_<f_t`. A 16-node exact countergate satisfies the
   physical no-`X` relation and falsifies the old `X^2` relation at 14 nodes.

2. Deleting that spurious factor does not hurt the numerator-root backward
   argument. Every one of the 6,930 deficient shapes has at least 13 paired
   high/low channels, its last high dual cap is at most 3,276, and
   `deg E0>=2151`. Thus 1,125 numerator roots still kill the last kernel and
   propagate zero backwards. The complementary branch really is

   ```text
   z = #{NTT roots of N0} <= 1124.
   ```

3. In this small-zero branch, all nonzero kernel chains are geometric in the
   polynomial UFD. If the chain is indexed `0,...,m`, then

   ```text
   K_j = C A^(m-j) B^j,       gcd(A,B)=1.
   ```

   The exact all-shape caps give `deg A<=95`, `deg B<=93`, and the stronger
   joint bounds `deg A+deg C<=1126`, `deg B+deg C<=1124`.

4. The corrected last-pair relation is no-wrap for every shape through
   `deg N0<=130508`, improving the old direct-square cutoff `129449` by
   1,059 degrees. The literal first defect closes through `130537`.

5. Above that cutoff, all 12--33 recurrences collapse to one near-global
   cyclic Padé/Pell equation

   ```text
   (Omega / gcd(Omega,C)) | (N0^2 A - E0^2 B),
   Omega = X^262144 - 1.
   ```

   At `deg N0=149776`, its remaining quotient can still have degree 38,534.
   Pure degree counting therefore stops. This equation, or additional actual
   DataEleven structure, is the honest next discriminator.

This is a useful narrowing, not a submission-readiness result. The full
remaining band is `130509..149776` (and `130538..149776` for the literal
first defect), plus the separate simultaneous source-allocation/confluence
obligation.

## Why the recurrence has no `X^2`

For the ordinary Reed--Solomon prefix

```text
F_<f = { eval(A) : deg A < f }
```

on all `N` roots of unity, every dual word has the fixed representation

```text
lambda(x) = x H(x),       deg H < N-f.
```

The anchor `x` is independent of `f`. If the `t`th physical channel is
`W^t F_<f_t`, where `W=N0/E0`, its dual condition is

```text
lambda(x) W(x)^t = x H_t(x).
```

At the next channel this gives

```text
N0 H_t = E0 H_(t+1)
```

at every node. After a high/low pair is below the cyclic modulus,
coprimality gives

```text
H_high,j = E0 K_j,
H_low,j  = N0 K_j.
```

Passing from one pair to the next therefore gives exactly

```text
N0^2 K_j = E0^2 K_(j+1)
```

on nodes. The fact that the next high prefix is two coordinates longer is
already reflected in its dual cap dropping by two. It does not move the
fixed RS-dual anchor.

`m69_rs_dual_anchor_x2_countergate_6900.py` verifies this convention without
symbolic ambiguity. Over `F_97` on 16th roots, take

```text
W=X^-1,  E=X,  N=1,
source = F_<8 + X^-1 F_<8 + X^-2 F_<8,
lambda = X^3.
```

Then `lambda` annihilates all three channels and

```text
H0=X^2, H1=X, H2=1,
N H0=E H1,
N H1=E H2,
N^2 H0=E^2 H2.
```

But `N^2 H0=X^2 E^2 H2` is false at 14 of the 16 nodes. This is a RED for
the old adapter premise, not for the corrected recurrence.

## Exact all-shape ledger

`m69_small_zero_geometric_chain_audit_6900.py` independently reconstructs
the frozen defect census and obtains the same shape receipt

```text
e789d4d983053ed615c9c706c87a004f6c96f2c66cc51d6625507cafb0dedeeb.
```

For each physical shape it computes all high-prefix indices followed by a
low prefix. Across two powers the high fringe rises by 2, so its complement
and the corresponding `K` cap drop by 2. Exact global values are

```text
deficient shapes                         6930
high/low pair count                      13..34
last high complement                     3218..3276
last K exclusive cap at deg(E0)=2151     <=1125
penultimate K exclusive cap              <=1127
maximum individual deg(A)                95
maximum individual deg(B)                93
maximum joint deg(A)+deg(C)               1126
maximum joint deg(B)+deg(C)               1124
```

The worst large-zero threshold is attained by the low-fringe shape
`(y,r,s)=(0,0,0)`. Its 34 high caps are `3342,3340,...,3276`, giving
`K` caps `1191,1189,...,1125`.

The literal first defect `(39,14,10)` has 15 high caps
`3246,3244,...,3218`, hence `K` caps `1095,1093,...,1067`.

## Geometric UFD reduction

Assume the chain is not already zero. Two consecutive corrected recurrences
give, pointwise,

```text
K_j K_(j+2) = K_(j+1)^2.
```

Both sides have degree below 2,384, far below 262,144, so this is a
polynomial identity. Write the first ratio in lowest terms as

```text
K_1 / K_0 = B/A,       gcd(A,B)=1.
```

All adjacent minors show `K_j/K_0=(B/A)^j`. Since `K_m` is a polynomial,
`A^m | K_0`; writing `K_0=C A^m` gives

```text
K_j=C A^(m-j) B^j.
```

The endpoint degree bounds are

```text
deg C + m deg A < cap(K_0),
deg C + m deg B < cap(K_m).
```

The executable optimizes these inequalities separately for all 6,930 exact
chains. The worst individual factor bounds are 95 and 93; combining
independent maxima would be unsound, so it also optimizes the joint bounds
and obtains 1,126 and 1,124.

Substitute the normal form into each recurrence. Away from roots of `C`, the
first and last multipliers cannot both vanish because `gcd(A,B)=1`. Hence

```text
N0^2 A = E0^2 B
```

at every domain node outside `Z(C)`. Equivalently,

```text
Omega/gcd(Omega,C) | N0^2 A-E0^2 B.
```

At a numerator root outside `Z(C)`, denominator root-freeness forces `B=0`.
Thus every numerator root lies in `Z(CB)`, and

```text
z <= deg C+deg B <=1124.
```

This recovers the exact complementary threshold structurally; it does not
make the remaining Padé equation vanish as a polynomial.

## Corrected no-wrap extension

Use the last recurrence, where

```text
deg K_(m-1) <=1126,
deg K_m     <=1124.
```

If `deg N0<=130508`, then

```text
deg(N0^2 K_(m-1)) <= 2*130508+1126 = 262142 <262144.
```

The other side has degree at most

```text
2*18414+1124 <262144.
```

Nodal equality is therefore polynomial equality. Since `gcd(E0,N0)=1`, it
forces `E0^2 | K_(m-1)`, impossible for a nonzero kernel because

```text
2 deg E0 >=4302 >1126.
```

So the last pair is zero; denominator root-freeness and the at least 112,368
non-numerator-root nodes propagate zero through the whole chain. At degree
130,509 the same uniform left-degree bound is exactly 262,144, so this proof
stops sharply.

`M69CorrectedDualRecurrence6900.lean` kernel-checks the corrected nodal
definition, the rank-one minor, the UFD/coprime short relation, and the exact
`130508` late-pair theorem. Its printed axiom sets are only
`[propext, Classical.choice, Quot.sound]`.

## Exact small controls

Two exhaustive controls looked for an immediate counterexample to the
geometric route, rather than assuming rigidity from dimensions.

`m69_small_zero_sign_pade_control_6900.py` works over `F_97` on all 16th
roots, with the scaled high-numerator parameters `deg E=1`, `deg N<=9`.

* all 65,536 sign words `W(x) in {+1,-1}` were exhausted;
* 68 admit a degree-one Padé denominator before validity filters;
* 128 projective cases put a denominator root on the domain;
* 324 valid nonconstant-denominator cases retain a common factor;
* zero reduced counterexamples survive;
* among all 6,561 ordered domain-root-free monic linear ratios `B/A`, the
  only 81 which are squares at every base-field node have `A=B`.

`m69_small_zero_one_exception_pade_control_6900.py` leaves one of the 16
nodes unconstrained and exhausts all 32,768 sign assignments on the other
15. It solves the resulting bilinear Padé system exactly. Again all 324
valid nonconstant-denominator cases retain a common factor and zero reduced
counterexamples survive.

These controls support continuing the structural route, but they are much
too small to prove the benchmark theorem. In particular the real
`ExtensionField` permits pointwise square roots which need not be rational
squares in `F(X)`.

## Honest remaining blocker and route rule

For `130509<=deg N0<=149776`, pure UFD degree arguments leave

```text
N0^2 A-E0^2 B = (Omega/gcd(Omega,C)) R,
deg R <=38534.
```

There is no current theorem forcing `R=0`. Long-chain minors do not give
independent equations after the geometric reduction; they all become
polynomial multiples of this same equation. Thus blindly adding more powers
or enumerating more m69 shapes is duplicate work.

The next high-value test is one of:

1. classify the near-half-degree rational square roots of low-degree `B/A`
   on all but at most 1,124 points of the `2^18`-root subgroup;
2. use the actual four DataEleven source equations/Frobenius coupling to
   exclude the non-rational-square branch;
3. construct a genuine reduced counterexample to the displayed Padé equation
   in the exact benchmark field, which would kill the universal prefix route.

Until one of these succeeds, the result is structural progress and a
20,327-degree uncertainty band reduced by 1,059 degrees, not a 6900 proof.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=536870912 --cpu=120 -- \
  python3 -B .experiments/m69_small_zero_geometric_chain_audit_6900.py
prlimit --as=536870912 --cpu=180 -- \
  python3 -B .experiments/m69_small_zero_sign_pade_control_6900.py
prlimit --as=536870912 --cpu=180 -- \
  python3 -B .experiments/m69_small_zero_one_exception_pade_control_6900.py
python3 -B .experiments/m69_rs_dual_anchor_x2_countergate_6900.py
env LEAN_NUM_THREADS=1 lake env lean -j1 -M3500 \
  .experiments/M69CorrectedDualRecurrence6900.lean
```

Recorded source hashes after the bounded runs:

```text
m69_small_zero_geometric_chain_audit_6900.py
  d1bae37187b2a8629ff965541b832f20c55b156fa448b07b8f21bb7fbb47ff16
m69_small_zero_sign_pade_control_6900.py
  fc1aa52a357938e248ecbe4c5e1f336ba644ff28383854c9614e0db50866f848
m69_small_zero_one_exception_pade_control_6900.py
  76b50fc4193ae9ac8d27517a61c84d3aaa5547166a5cc67606ddb421ff89963f
m69_rs_dual_anchor_x2_countergate_6900.py
  91949beec9046f972ada04d18a28e157de6af8709829dfc5f8f64ce653f2c8b2
M69CorrectedDualRecurrence6900.lean
  92b3a01cf936ec1f1ba81d4021c8fdea23c37f46c38aea9a7ee9fe039aa53210
```
