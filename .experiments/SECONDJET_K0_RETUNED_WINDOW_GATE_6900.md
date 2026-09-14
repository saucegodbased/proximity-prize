# k=0 retuned-window source gate for lower 6900

Date: 2026-09-14 UTC. This is a source/consumer arithmetic receipt and a
process correction, not a rank theorem, candidate, or submission.

## Exact positive profile

For target agreement `A=180413`, word degree `w=131071`, and `N=262144`,
use the second-jet support profile

```text
(m,B,s,U,L,k,n0) = (47,16,8,64,3757,0,1).
```

Because `k=0`, every curvature layer has cutoff `47*A`; no differentiated
source is claimed. The literal support/rank formulas give

```text
source columns                 65,061,789,117,960
one-node relaxed rank bound           248,191,020
N times rank bound             65,061,786,746,880
source margin                           2,371,080
middle-cap slack in every h-layer               0
```

The C++ replay is `k0_rank4_source_search_6900.cpp`; the fixed profile was
independently reevaluated with the literal Python formulas in
`higher6810_secondjet_retarget_exact.py`. The accompanying Lean file checks
the resulting exact integers and all consumer inequalities. It deliberately
does not disguise the executable support sum as a Lean source theorem.

## Retuning removes the extra-agreement degree obstruction

For a source cutoff `D=47*G0`, a full four-normal determinant at a candidate
with `G0+r` actual agreements has residual X-degree cap

```text
3*(A-w)-1-(4*m-3)*r = 148025-185*r.
```

It can therefore remain nonzero for `0<=r<=800`; `r=801` is the first
degree-forced zero. Partition the possible agreement cardinalities into 103
windows of width 801, starting at

```text
A, A+801, ..., A+102*801.
```

Indeed `N-A=81731 < 103*801=82503`. In each window, rebuild the same contact
space with cutoff `47*G0`. Increasing the cutoff only adds source columns,
while the local rank bound and all non-X caps are unchanged. Thus the first
window's positive dimension certificate is the numerical worst case.

This is the useful delta over the archived fixed-cutoff Global-O2 route: no
candidate is sent to an unpriced high-agreement fallback merely because all
four-minors are degree-forced to vanish.

## Consumer arithmetic

At `(J,L)=(64,3757)`, the existing conservative 52-chart formulas give

```text
one-window cost                  1,546,270,015,488
103-window cost                159,265,811,595,264
target MCA allowance       254,684,620,614,660,120
```

The active and inactive projection caps are respectively below the target
characteristic (the larger displayed check is `141,643,776 < 2,130,706,433`).
The repeated-window cost is only about 0.063% of the allowance. Arithmetic,
characteristic, and aggregate chart count are not the blocker.

### Exact-cardinality simplification

The same ledger is cheap enough to discard the width-801 grouping entirely.
There are exactly 81,732 possible maximal actual agreement cardinalities, and

```text
81,732 * 1,546,270,015,488
  = 126,379,740,905,865,216
  < 254,684,620,614,660,120,
remaining allowance = 128,304,879,708,794,904.
```

Thus the producer may be rebuilt at the exact maximal agreement size `g`,
with cutoff `D=47*g`, for every stratum.  This is a substantial semantic
simplification: every node outside `G` then has a genuinely nonzero residual,
the full-`G` locator rows fit the source exactly, and no nominal error block
contains extra zero-residual agreements.  Source positivity is worst at the
smallest `g`; increasing `g` only increases every X strip width.  This does
not prove rank-defect recovery, but it removes the extra-agreement/window
case from that theorem without exceeding the existing post-scalar MCA
allowance.

The kernel-checked arithmetic is in
`SecondJetK0RetunedWindowArithmetic6900.lean`.

The raw last terminal strip also has

```text
47*A - w*(16+47+1) = 90,867 > N-A = 81,731.
```

This is only a necessary error-CRT width check.

## Exact remaining theorem and stop boundary

The profile does **not** solve the archived source-completeness problem.
For the actual all-node contact kernel in one window, one still needs

```text
full conormal rank < 4
  -> a base-field polynomial h of degree <= w
     interpolates U1 on the supplied bad agreement set.
```

Then
`GlobalO2BadRowConormalBridge6900.no_direction_interpolant_of_bad` gives the
contradiction and full rank four. Generic small-field rank four is evidence,
not this implication.

The raw width `90,867` must not be promoted to an error-peeling proof. If one
centers by the automatic degree-`<A` agreement interpolant, each active jet
factor can cost another `A-w-1=49,341` in X degree. This is the same
passive-seed centering obstruction already recorded in
`GlobalO2CoupledSchurRank.lean`. Centering only by the degree-`w` polynomial
on `w+1` anchors is source-safe, but proving that rank defect kills every
remaining Newton discrepancy is exactly the missing rank-defect-recovery
theorem, not a shortcut around it.

Decision: use exact-cardinality strata, not 801-wide windows, in further
theorem work.  Do not spend time assembling the 81,732 wrappers until a fixed
symbolic bordered-minor/dual recurrence proves the first extra Newton
identity. The next progress must change that theorem status, not optimize
another profile.

## Lean replay

```sh
env LEAN_NUM_THREADS=1 lake env lean -j1 -M8000 \
  .experiments/SecondJetK0RetunedWindowArithmetic6900.lean
```

The replay completes in about four seconds and prints only `propext`,
`Classical.choice`, and `Quot.sound`. It contains no `sorry`, `decide`, or
`native_decide`.
