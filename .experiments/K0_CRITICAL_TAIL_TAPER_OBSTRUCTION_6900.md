# k0 critical tail: exact taper obstruction and seed correction

Date: 2026-09-14 UTC. Scope: lower-6900, full m47 exact-G source. This is
an exact obstruction/triage receipt. It changes no production file,
candidate, score, or submission root.

## Verdict

Two facts are now separated cleanly.

1. The proposed correlation “the critical passive seed must reach the
   Newton-quotient degree” is **false**. A generic exact m5 retest has
   `deg T=0`, but seed zero is injective and the prefix `Z^0,Z^1` first
   closes the fourth boundary direction. An independent axis trade closes
   with `Y^m S,Y^(m+1)S`. The robust local packet therefore needs one
   adjacent critical cell, not `z=deg T`.
2. The naive global polynomial lift of the local nilpotent identity is
   **not repaired by the two-step X/R/S connection coefficientwise**. Its
   worst direction-power terms overflow exactly the lower-Y bands
   `y=0,1,2`. Even two ordinary X derivatives leave all three outside the
   strict source taper.

Thus there is no passive-cap obstruction: the target profile has vastly
more than the required seed width. But there is a real X-taper obstruction.
The surviving route must use the complete causal PC/CRT confluence across
adjacent Y or Z cells; it cannot globalize the node-local binomial by simply
inserting the exact-G interpolant and applying `delta` twice.

## Exact target arithmetic

At the smallest exact stratum,

```text
m=47, g=180413, w=131071, D=mg=8479411.
```

For the raw shape `S Y^y`, the legal strict X width is

```text
W(y)=D-wy-(w-2).
```

If `Q` has its maximal allowed degree `g-1=180412`, the coefficient of
`S Y^y Z^(47-y)` in the direct binomial lift can have degree

```text
N(y)=(47-y)(g-1).
```

The first four rows are:

| y | strict width W(y) | possible degree N(y) | status |
|---:|---:|---:|:---|
| 0 | 8,348,342 | 8,479,364 | overflow by 131,023 monomials |
| 1 | 8,217,271 | 8,298,952 | overflow by 81,682 monomials |
| 2 | 8,086,200 | 8,118,540 | overflow by 32,341 monomials |
| 3 | 7,955,129 | 7,938,128 | fits, with 17,001 degrees to spare |

The margin improves by `g-w-1=49,341` each time y increases. Hence every
row `3<=y<=47` fits, and exactly `y=0,1,2` can overflow.

The raw connection

```text
delta = d/depsilon + 2S d/dR + 3T d/dS
```

turns coefficient commutators into ordinary X derivatives. Two connection
steps can lower `N(y)` by at most two. The compiled inequalities are

```text
W(0) <= N(0)-2,
W(1) <= N(1)-2,
W(2) <= N(2)-2.
```

This is not merely a loose degree upper bound. Over `Q`, the concrete
monomial `X^8479364` has a nonzero second derivative of degree `8479362`,
still far beyond `W(0)=8348342`. The formal lemma is parameterized by the
nonvanishing falling-factorial coefficient, so the same obstruction applies
in any field where that coefficient survives.

This is a hard **NO** to the narrow question “does the two-step connection
span the high-Q tail coefficientwise?” It is not a counterexample to the
complete target PC recurrence, whose adjacent-cell finite controls remain
positive.

## Passive seed is not the issue

Commit `806558b` proves the exact local relations for both adjacent choices:

```text
Y^47 S Z^0 + its causal lower staircase,
Y^47 S Z^1 + its Z-shifted causal lower staircase,
Y^48 S     + its Y-shifted causal lower staircase.
```

For the two-seed packet the lower seed exponent is `zLower+zCrit` with
`zLower<=47-y` and `zCrit<=1`. Thus the coefficient seed degree is at most
48 and the full passive total `S+Y+Z` is at most 49. Both live profiles

```text
(s,L)=(8,3757), (6,5107)
```

contain the packet by orders of magnitude. The possible Newton quotient
degree `49340` never appears as a required raw Z exponent in this identity.

## What remains open

The strongest proved statements are now:

- the literal local critical nilpotent staircase and both adjacent-cell
  shifts are exact contact-order-m relations;
- all their raw monomials are target-legal;
- isolated tapered CRT strip cokernels are exactly low-degree remainders;
- the direct global Q-substitution overflows only three bands; and
- the raw two-step connection does not by itself remove those three tails.

The unresolved theorem is narrower but still genuinely global: show that
the complete boundary-compatible PC transpose uses the adjacent critical
cell and the `{1,R}`/subcritical-S prefix to cancel the three illegal tails
*between shapes*, including agreement cancellation and the error boundary
right side. A proof that differentiates each coefficient independently
cannot close this gate.

## Formal artifact

```text
.experiments/K0CriticalTailTaperObstruction6900.lean
```

It proves:

```text
target_three_bad_bands_and_first_good_band
naive_tail_bad_below_three_good_from_three
two_connection_steps_do_not_repair_first_three_bands
natDegree_second_derivative_X_pow
monomial_second_derivative_still_outside_taper
shifted_critical_passive_degree_le_48
```

The file compiles in about three seconds under the task-local 8 GiB cap.
Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx`, `native_decide`, or finite-rank oracle occurs.
