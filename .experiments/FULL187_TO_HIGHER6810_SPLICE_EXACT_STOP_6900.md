# Full187/P5 to accepted Higher6810: exact splice audit

Date: 2026-09-14 UTC. Target: 6900 only. This is a bounded GO/STOP audit of
the accepted `Higher*6810` factor/affine consumer at upstream commit
`09d8a2a`. It does not change a submission file and does not claim 6900.

## Verdict

**STOP for the literal splice.** There is one real numerical GO signal: if the
accepted actual-factor affine cap could be applied at the formerly binding P5
flag `(r,v,z)=(9,46,2920)`, it would beat the target allowance by
`17,093,586,103,008,888`. However, the accepted theorem cannot be instantiated
at target 6900, and `OriginalPassiveSeedSource6900` produces a moving
five-variable/seed carrier rather than the one fixed four-variable carrier
consumed by Higher6810.

The residual support is *not* the obstruction. Full187 has

```text
(slope,middle,total) = (21,82,2703),
```

which lies well inside Higher's `wideSupport=(37,164,8865)` and
`wholeSupport=(34,156,8865)`. The first exact obstruction is the producer type
and quantifier order, followed immediately by the hard-coded agreement.

## 1. Exact producer/consumer mismatch

The Full187 producer is

```text
Q : SeedPoly K = Polynomial (MvPolynomial (Fin 4) K),
Q != 0,
forall gamma P support,
  ... -> passiveJetSpecialization P gamma Q = 0.
```

Here

```text
passiveJetSpecialization P gamma Q
  = localJetSpecialization2 P (seedEvaluation gamma Q).
```

Thus the four-variable carrier supplied at candidate parameter `gamma` is

```text
H_gamma = seedEvaluation gamma Q.
```

It moves with `gamma`. Nonzeroness of `Q` does not make any fixed coefficient
of `Q` vanish after specialization: the zero identity is for the diagonal sum
`sum_z gamma^z * coeff_z(Q)`, and cancellation between seed coefficients is
allowed.

In contrast, the accepted Higher architecture fixes one

```text
H : P4 = MvPolynomial (Fin 4) K
```

before ranging over `Gamma`. For example,
`HigherAssembly6810.selected_pair_count_le` sets

```text
H := gcd12 S.QA S.QB
```

and `HigherRegularBridge6810.regular_count` factors this same `H` and uses the
same `RegularIndex H` over every `gamma in Gamma`. Likewise
`HigherSingletonGeometry6810.factor_count_le_affine` takes a fixed `Q : P4`
and `F : RegularIndex Q`.

The smallest missing adapter is therefore a diagonal-to-fixed-carrier lemma of
the following shape:

```text
exists H : P4,
  H != 0 /\ ResidualSupportData wideSupport H /\
  forall gamma in Gamma,
    specialization (selected gamma) gamma H = 0.
```

The present Full187 theorem proves only the corresponding statement with
`H_gamma=seedEvaluation gamma Q`. This implication is false for an arbitrary
polynomial family (the toy diagonal identity `H_t(X)=X-t`, evaluated at
`X=t`, is the minimal counterpattern), so this is not a coercion or a routine
coefficient extraction. A valid route needs new content/primitive-factor,
resultant, or bounded family-factor structure. Taking a product over all
candidate parameters is fixed but multiplies the support by `|Gamma|` and is
not the accepted cap regime.

This also explains why the P5 retained proper helper does not automatically
unlock the affine table. For the retained helper

```text
H_F = (C/F)^j * a_(n_F)
```

properness gives `F does not divide H_F`, whereas the affine theorem's factor
argument has type `F : RegularIndex Q`, which includes `F divides Q`. One may
instead take `Q=C`, but then the retained helper is unused and one still needs
a fixed target-valid Higher source/phase proof for `C`.

## 2. The accepted theorem is hard-coded to 6810

Even after postulating a fixed carrier, both entry points in
`HigherInitial6810.lean` require

```text
hagreement : forall gamma in Gamma,
  181294 <= agreementFiber(gamma).card,
hno : NoLargeSelectedPencil ... 131071 80850.
```

These are the hypotheses of both `initialA_nonuniversal_count` and
`initialA_universal_singleBound`; the latter calls
`HigherSingletonGeometry6810.factor_count_le_affine`, which repeats the same
constants. Target 6900 supplies only agreement `180413` and error count
`81731`. There is no monotonic weakening from `180413` to `181294`.

The independent retarget audit in commit `a7d7645` already shows why changing
only these constants is not enough: every fixed accepted source kernel becomes
nonpositive at the target. Hence the exact missing proof is not a wrapper
around the accepted theorem; it needs a new positive target source feeding the
affine phase interfaces.

## 3. The affine cap really would fix the old retained arithmetic

This part is a conditional numerical discriminator, not a proof application.
The accepted table gives

```text
rate(9,46) = 17,833,120,542,407,246,
cap(rate,9,2920)
  = 26,000,000,000,000*2920 + 9*rate(9,46)
  = 236,418,084,881,665,214.

target remaining allowance
  = 253,511,670,984,674,102,
conditional slack
  = +17,093,586,103,008,888.
```

The previous collision-safe retained-top replay was about `326.36e15`, so the
actual-factor affine shape is numerically strong enough at its reported worst
state. This makes a target-valid fixed-carrier/source adapter worth pursuing;
it does **not** authorize taking a minimum with the retained charge today.

## 4. Direct Full187 row -> accepted A-kernel is numerically impossible

A second possible splice is to turn a Full187 coefficient/specialization into
a row of the accepted A kernel. Even under the favorable grant that it is a
nonzero ambient P4 row with Full187 contact and no denominator cost, it fails
the main box first.

Full187 has contact `60` and strict main cutoff

```text
D = 60*180413 = 10,824,780.
```

The accepted A kernel has contact `113` and strict main box
`20,486,222`. Restoring the missing 53 contacts with the full-node locator
costs `262144*53`, so the resulting strict cutoff is

```text
10,824,780 + 262144*53 = 24,718,412,
box slack = 20,486,222 - 24,718,412 = -4,232,190.
```

Extracting one more contact-losing source variable cannot help: the greatest
available main-weight saving is `w=131071`, while one locator costs `262144`,
so every such order worsens the deficit by at least

```text
262144-131071 = 131073.
```

For completeness, the accepted A box's extra `99,553` main units relative to
`113*180413` creates exactly two formal complete-layer fit points for the
target-native `k=1,n0=2` promoted-P5 cutoff:

```text
(m,h)=(115,2), slack +50,209;
(m,h)=(116,3), slack +865.
```

There are no other `h>=2` fits. Exhausting the published closed-form source
receipt with the cap-matched choice `s=h` makes both points source-negative:

```text
m=115,s=2: best margin -259,058,649,485 at (B,U,L)=(4,121,121)
m=116,s=3: best margin -463,295,187,361 at (B,U,L)=(6,125,125).
```

The uniqueness is an unbounded integer argument, not an inference from the
checker's finite loop. Put `d=m-113`. If `m>=113` and `h<=d`, the exact slack
is

```text
148897-180413*d+131069*h <= 148897-49344*d,
```

so `d<=3`, and direct enumeration leaves only `(d,h)=(2,2),(3,3)`. If
`h>d`, the slack is

```text
148897+81731*d-131075*h;
```

using `h>=d+1` makes it negative for `d>=1`, while `d=0,h>=2` is also
negative. Finally, for `m<113` and `q=113-m>=1`, the slack is

```text
148897-81731*q-131075*h < 0
```

for every `h>=2`.

So the direct coefficient-layer-to-A-row repair is stopped independently of
the moving-carrier issue. This last scan is scoped to the standard complete
top-layer certificate `s=h`; it does not rule out an unproved sparse-layer
rank theorem.

## 5. Reproduction

Run:

```bash
g++ -std=c++17 -O2 -Wall -Wextra -pedantic \
  .experiments/p5_higher6810_splice_gate_6900.cpp \
  -o /tmp/p5_higher6810_splice_gate_6900
/tmp/p5_higher6810_splice_gate_6900
```

The checker asserts the two complete-layer fits, exhausts both cap-matched
source windows using exact `__int128` arithmetic, checks the Full187 locator
deficit, and checks the conditional affine margin. Peak memory is negligible.

## Recommendation

Do not formalize a literal Full187-to-`HigherInitial6810` adapter. Preserve the
affine cap as a quantitative target: pursue only a construction that outputs a
**fixed** P4 carrier over all candidate parameters and supplies target-positive
phase sources at agreement `180413`. Without those two properties, the
accepted 6810 affine theorem is numerically attractive but type-inapplicable.
