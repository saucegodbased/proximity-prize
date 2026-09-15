# W=133225 one-exception identity helper: fixed-cap exhaustive STOP

## Scope and result

This audit asks whether shortening the identity-node helper to `N=262143`
(one exceptional domain node) repairs the weighted helper while keeping the
current primary cut thresholds

```text
J = 211, D = 55, T = 27.
```

It does not: **no admissible weighted helper profile clears both product
bands**.  This is exhaustive within the existing finite-prefix weighted
source family.  The conclusion is deliberately only a fixed-primary-cap
STOP; it does not claim that `(J,D)=(211,55)` is globally optimal over all
primary profiles.

The audit also carries every contribution in the one-exception list-count
ledger.  Thus a helper is not called green merely because of a kernel/band
margin.

## Why the previous scan was incomplete

The old `focus` mode sorted profiles by a certified D55 upper margin.  Its
exact loop then stopped as soon as

```cpp
upperD <= bestD
```

and normally considered at most 500 records.  At `N=262143`, the first exact
record `(k,m)=(1306,11809)` has positive D55 margin but negative J211 margin.
The loop records its positive `bestD` and stops after one profile, leaving
5426 further D-feasible profiles unchecked.  Optimizing one band cannot prune
the search for simultaneous positivity of two bands.

`weighted_helper_n262143_joint_filter_6900.cpp` instead applies independent
certified lower bounds to *both* bands before exact expansion.  It never
prunes using the best value observed at a different profile.

## Complete semantic domain

The generic source APIs require

```text
1 <= m,
m*180413 < 2130706433,
4*k <= floor(m*180413/133223)+1.
```

Consequently `m<=11810`, `k<=3998`.  Direct integer enumeration gives exactly

```text
23,609,180 admissible (k,m) pairs.
```

They split without overlap as

```text
m < 8*k : 14,896,352
m >= 8*k:  8,712,828
```

(`m=8*k-1` is in the clipped pass, even though its low-rank expression is
already at the unclipped equality boundary.)

## Certified pruning

For fixed `k`, both the exact target-rank cap and the source-column count are
monotone in `m`.  On a clipped interval `[lo,hi]`, the adaptive pass computes

```text
U = columnsUpper(hi*180413,k) - 262143*exactRank(lo,k).
```

The column upper bound follows from the exact residue identity

```text
2W*widthSum(W,b) = b^2+W*b+W*r-r^2,
r=b mod W,
W*r-r^2 <= floor(W^2/4).
```

Therefore `U` bounds the kernel at every integer point of the interval.  An
interval is discarded only when `U<=0`; otherwise it is bisected.  At a
singleton, the exact clipped low-rank formula is used.  This covered the
clipped chamber with

```text
adaptive blocks        949,698
points block-rejected 14,871,210
exact singleton points    25,142
source-upper-positive      25,142
D55-necessary survivors         0
```

The exact clipped evaluator is the inclusion-exclusion lattice formula in
`weighted_helper_unrestricted_m_w133225_6900.cpp`; its `selfcheck` agrees with
the literal four-loop definition for every `k<=6,m<=60`.

In the unclipped chamber the retained low-rank expression is exact.  Every
source-upper-positive point is first charged a certified D55 band lower bound.
The 5427 D-feasible points are then charged an independent J211 band lower
bound.  Results:

```text
tested                    8,712,828
source-upper-positive     1,899,829
D55-necessary survivors       5,427
both-band-necessary survivors     0
```

The band bound is termwise: for every exact stage,

```text
columns(C,E)-columns(C-delta,E)
  >= delta*activeFibresLower(C-delta,E),
delta = 180413-133225+2 = 47190,
```

and `activeFibresLower` drops only nonnegative quotient-carry indicators.
Thus a nonpositive upper margin is a proof of numeric impossibility, not a
sampling heuristic.

The least-negative simultaneous upper margin in the high chamber is at
`(k,m)=(1312,11803)`:

```text
certified J211 upper margin  -236,948,777,002,448
```

Literal evaluation at that profile is

```text
B             2,129,414,639
M                    15,983
D                     5,248
rank        314,035,306,764,501
columns  82,455,672,153,104,845,000
kernel      133,514,731,938,259,357
D55 margin        2,527,364,513,065
J211 margin      -240,747,821,586,566
```

So the old early exit hid many profiles, but none of them repairs J211.

## Full one-exception list ledger

The candidate core loses at most one seed, hence its exact floor is

```text
263,611,557,201,785,349.
```

Using `n=262143`, `a=180413`, `w=133225`, `v=68763`, and
`small=1453806`, the complete fixed contributions are

```text
cheap regular aggregate           247,335,521,894,435,962
positive-T cleanup                  15,606,365,842,399,170
T-free regular cleanup                 264,025,132,882
T-free singular cleanup                    362,328
---------------------------------------------------------
fixed cap                          262,942,151,762,330,342
helper-exit allowance                  669,405,439,455,007
```

The shortened-Johnson inequality remains strictly valid at `n=262143`.
For a helper flag `q`, the remaining term is

```text
ceil((262143-68763)*flagMixed(primary,q,primaryAgreement)
     /(180413-68763)).
```

It fits the complete ledger exactly only if

```text
flagMixed(primary,q,primaryAgreement) <= 386,488,350,993,647.
```

For the closest joint-band profile above,

```text
helper flag       (10735,2624,2624)
mixed cost          455,069,826,732,134
helper exit cap         788,189,906,793,194
full ledger        263,730,341,669,123,536
ledger deficit         118,784,467,338,187.
```

Thus that profile is independently red at both the J211 band and the complete
list ledger.  Smaller helpers can fit the ledger, but the exhaustive joint
band audit rules every one of them out before the list consumer.

`WeightedIdentityOneExceptionLedgerW1332256900.lean` certifies these ledger
constants, the Johnson gate, the exact mixed-cost threshold, and the closest
profile's deficit with no `decide` or `native_decide`.

## Reproduction

```text
g++ -O3 -march=native -fopenmp -std=c++20 \
  .experiments/weighted_helper_n262143_joint_filter_6900.cpp \
  -o /tmp/weighted_helper_n262143_joint_filter_6900

/tmp/helper_w133225_n262143 selfcheck
OMP_NUM_THREADS=16 /tmp/weighted_helper_n262143_joint_filter_6900 adaptive
OMP_NUM_THREADS=16 /tmp/weighted_helper_n262143_joint_filter_6900 \
  8000 12000000
```

The Lean ledger builds under a 6 GiB allocator cap.  Its printed axioms are
only `propext`, `Classical.choice`, and `Quot.sound` (the purely numeric fixed
ledger itself needs only `propext`).

## Decision and next gate

**STOP** for every helper paired with the current `J211/D55` primary split at
`N=262143`.  Residual uncertainty inside this fixed-cap family is zero.

The only relevant reopening is a joint optimization over the primary profile
and helper profile, recomputing both band thresholds and the complete list
ledger.  This note must not be cited as a global W133225 impossibility before
that joint audit is done.
