# W=133225 identity terminal L-shape: conditional GREEN

## Decision

The nonrectangular terminal split

```text
(J <= 211 and D <= 55) or (J <= 212 and D <= 54)
```

is useful.  The only omitted integer corner is `(J,D)=(212,55)`.  The
existing factorwise cheap-incidence mechanism can charge a **nonsingleton**
corner product without enlarging every factor's agreement flag.  The exact
extra terminal cost is `459,609,023,370,914`, and the resulting complete
cheap-plus-minimum-primary-cleanup ledger remains green by
`293,703,028,276,199` before helper exits.

A **singleton** corner cannot use that cheap argument, but the same J-heavy
helper profile already found by the exhaustive scan has a very large joint
`J=212,D=55` band margin.  Therefore the exact mutually exclusive terminal
case split has no numerical corner obstruction.  The remaining bottleneck is
the shared exit charge for the J-heavy and D-heavy recursive branches, not the
terminal corner.

This is not by itself a complete 6900 proof.  The W=133225 helper sources and
the two-helper/shared-primary aggregation still have to be assembled.

## Why the nonsingleton corner is cheap

Let `s` be the remaining subset of normalized positive-T irreducible factors,
and suppose

```text
card(s) >= 2
jetDegree(product s) <= 212
derivativeDegree(product s) <= 55.
```

Every positive-T factor has positive jet degree.  Exact weighted-degree
additivity on the nonzero squarefree product then implies that every individual
factor has jet degree at most `211`: another factor contributes at least one
unit to the total `212`.

Thus each original factor can still use the old reduced agreement flag

```text
qA = honestReducedAgreementFlag 133225 211 55 27
   = (41,432,976, 7,593,825, 6,927,700).
```

Only the cumulative exact source flag changes:

```text
pA = (156,28,27)  -- total J=211, middle D=55, T=27
pC = (157,28,27)  -- total J=212, middle D=55, T=27.
```

`aggregate_scaled_flags` is linear in the source flag and therefore charges
the single extra `zOnly` unit once across all factors.  It does not replace
every agreement cut by the full corner agreement flag.

The formal theorem

```text
nonsingleton_corner_remainder_card_le
```

consumes the actual `Q`, `s`, `Gamma`, nodes, received word, injectivity,
degree/agreement hypotheses, and hereditary common-node cap.  Its conclusion
is a bound on the sum of the original factor regular families, exactly in the
form needed by the batch partition.

## Exact terminal arithmetic

At `N=262143`, `v=68763`, and `a=180413`:

```text
arm A: p=(156,28,27), q=qA
  flagMixed = 82,448,135,047,096,675
  cap       = 247,335,521,894,435,962

arm B: p=(158,27,27), q=honestReducedAgreementFlag 133225 212 54 27
  flagMixed = 81,150,690,383,165,475
  cap       = 243,443,327,693,811,957

nonsingleton corner: p=(157,28,27), q=qA
  flagMixed = 82,601,343,557,291,675
  cap       = 247,795,130,917,806,876

full rectangular corner: p=(157,28,27),
  q=honestReducedAgreementFlag 133225 212 55 27
  flagMixed = 82,913,653,212,689,175
  cap       = 248,732,026,234,678,355.
```

Consequently

```text
nonsingleton increment over arm A =    459,609,023,370,914
minimum primary cleanup             = 15,522,723,255,702,274
corner cheap + cleanup              =263,317,854,173,509,150
retained core floor                 =263,611,557,201,785,349
pre-helper headroom                 =    293,703,028,276,199.
```

By contrast, blindly enclosing the L-shape in the full `J212/D55` rectangle
is red by `643,192,288,595,280`.  That loss is an artifact of raising the
agreement flag for every factor.

## Singleton corner and the joint helper band

If `s={F}` and its product is at `(212,55)`, the factor itself has jet degree
`212`; the old `J<=211` cut is unavailable.  Charging it with the full corner
agreement flag is the red rectangular calculation above.

The correct mutually exclusive branch is instead to exit that sole factor
with the J-heavy helper, leaving an empty cheap remainder.  For the already
identified J-heavy profile

```text
k=1172, m=10499
B=1,894,156,087, M=14,217, Dsource=4,688
helper flag=(9,529,2,344,2,344)
formal conservative source-kernel lower=83,769,136,551,706,925,
```

the simultaneous actual product bounds give

```text
mainDegree >= (133225-2)*212
derivativeDegree >= 55.
```

The exact finite stage-band is `57,099,071,594,019,745`.  The verifier-friendly
relaxed-triangle upper bound is `57,100,381,355,460,300`, still below the
formal kernel lower by

```text
26,668,755,196,246,625.
```

This source also passes its intended `J>=213` heavy branch.  In the singleton
corner branch one pays its helper exit cap, `699,681,872,154,479`, but pays no
terminal cheap cap because the remainder is empty.  Even together with the
minimum primary cleanup, that branch uses only
`16,222,405,127,856,753`, far below the retained floor.

The C++ receipt computes both the literal exact band and the relaxed upper
bound without constructing a matrix:

```text
g++ -O2 -std=c++17 \
  .experiments/weighted_helper_exact_corner_w133225_6900.cpp \
  -o /tmp/weighted_helper_exact_corner_w133225_6900
/tmp/weighted_helper_exact_corner_w133225_6900 1172 10499
```

## Exact integration shape

Case-split the fixed ambient `positiveTFactors Q` through a terminal predicate
with these mutually exclusive outcomes:

1. `J<=211,D<=55`: old arm-A cheap consumer.
2. `J<=212,D<=54`: arm-B cheap consumer; its cap is below arm A.
3. `J=212,D=55` and at least two factors: the proved nonsingleton corner
   consumer with `pC,qA`.
4. `J=212,D=55` and one factor: attach the joint-band J-helper certificate to
   that factor and recurse to the empty remainder.
5. `J>=213`: J-heavy helper.
6. `D>=56`: D-heavy helper.

The tight terminal cap is case 3, not the full rectangle.  Its available
recursive-helper allowance is `293,703,028,276,199`.

## Remaining load-bearing work

* Formalize the W=133225 J-heavy and D-heavy source/kernel producers.
* Formalize the joint `(212,55)` stage-band lemma for the J-heavy source.  The
  relaxed bound above leaves 26.7 quadrillion of margin, so this is mechanical
  arithmetic rather than a new inequality.
* Prove the terminal case split and aggregate the two helper-exit families
  against their disjoint shares of the original primary factor flag.  Charging
  each helper against the entire primary flag separately remains too costly;
  this shared-factor step is still the substantive global gap.

## Verification

`WeightedIdentityLShapeCornerW1332256900.lean` was compiled under the local
6 GiB allocator cap.  Its endpoint theorems print only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `native_decide` or additional
axiom.
