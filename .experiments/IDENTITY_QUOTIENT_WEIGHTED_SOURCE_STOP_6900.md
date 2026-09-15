# Near-total identity quotient versus the weighted finite-prefix source: STOP

Date: 2026-09-15 UTC. Scope: lower 6900, only the branch with at least
`262143` fixed identity nodes. This audit does not alter a candidate or a
submission.

## Verdict

**STOP this quotient rescue.** There are two natural meanings of “quotient by
the known affine identity,” and neither produces a new usable source.

1. On the identity nodes, quotienting the joint selected/scalar second-jet
   algebra by the affine identity and its two derivative prolongations simply
   eliminates the selected jet. The scalar jet remains completely arbitrary.
   The quotient is therefore the one-word scalar jet algebra already used by
   the existing weighted finite-prefix source. It is not a new source and has
   no extra target-rank saving.
2. In the heterogeneous seed-coefficient source, removing the explicit
   locator-masked identity multiples leaves a **certified residual
   rank-nullity lower bound of zero**. At the most optimistic node count
   `N=262143`, the raw surplus is only `4257`, while the smallest multiplier
   space indicated by the sharp ancestral degree bounds has `525759`
   directions. Increasing seed width makes this comparison worse.

If denominator clearing is instead represented as repeated multiplication by
a polynomial factor, the first quotient step is definitionally the existing
`powerStage` cut and pays the existing `stageBand`. The complete `N=262143`
joint primary/helper audit has already rejected every ledger-feasible
rectangular cap in that same finite-prefix family. Thus there is no hidden
dimension refund after quotienting.

The formal receipt is
`IdentityQuotientWeightedSourceStop6900.lean`. It builds in about 4.6 seconds
under the established capped library shim. All five printed roots depend only
on `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`,
`decide`, or `native_decide`.

## 1. The identity quotient is triangular, not restrictive

For one retained seed, write the fixed polynomial identity as

```text
E P = A + B S,
```

where `P` is the selected polynomial, `S` is its associated scalar
polynomial, and `E=E0` is root-free at every benchmark node. At a node, denote
the values of a polynomial and its first two derivatives by subscripts
`0,1,2`. The identity and its first two prolongations are

```text
E0 P0                         = A0 + B0 S0,
E0 P1 + E1 P0                = A1 + B1 S0 + B0 S1,
E0 P2 + 2 E1 P1 + E2 P0      = A2 + B2 S0 + 2 B1 S1 + B0 S2.
```

Because `E0 != 0`, this is triangular with pivot `E0` in every row. For every
triple `(S0,S1,S2)` there is a unique triple `(P0,P1,P2)`. Consequently

```text
K[P0,P1,P2,S0,S1,S2] /
  (identity, first prolongation, second prolongation)
```

localized at `E0` is just `K[S0,S1,S2]`. In the global source notation these
are exactly the `Y,R,T` coordinates of
`WeightedSourceIndex6900`; `X` remains the coefficient variable. The quotient
does not impose any equation on `(S,S',S'')`.

The Lean theorems

```text
affine_identity_allows_arbitrary_second_jet
affine_identity_second_jet_unique
```

prove existence and uniqueness over an arbitrary field. This complements the
already formal value-level discriminator
`LargeIdentityLocusActualSourceTautologyStop6900.free_fixed_centre_satisfies_literal_actual_rows`,
which shows that even all-node identity rows permit an arbitrary pointwise
centre function.

There is a useful interpretation guardrail here. A nonzero polynomial in the
existing scalar weighted source is not automatically an affine-identity
multiple; scalar jet coordinates embed faithfully in the localized quotient.
But this is exactly the source we already have, not a newly recovered source.
Its nontriviality and all of its factor-escape costs have already been charged.

## 2. Exact heterogeneous quotient arithmetic

At `W=133225`, agreement threshold `T=180413`, selected degree `w=131071`,
and seed width `r=18`, the three coefficient blocks have total dimension

```text
18 * (180413 + (180413-131071) + (180413-133225))
  = 4,984,974.
```

Deleting the sole possible exceptional node entirely is the most favorable
possible treatment. The remaining `262143` nodes cost

```text
262143 * (18+1) = 4,980,717,
```

so the raw rank-nullity surplus is

```text
4,984,974 - 4,980,717 = 4,257.
```

The fixed relation has seed degree one. The ancestral numerator bounds give
common X-multiplier width

```text
49342 - deg(E0).
```

Using the worst permitted `deg(E0)<=18414` and paying a degree-one locator for
the sole exceptional node still leaves at least

```text
49342 - 18414 - 1 = 30,927
```

X multipliers for each of the remaining `r-1=17` seed coefficients. Thus the
masked family has at least

```text
17 * 30,927 = 525,759
```

slots, over 123 times the raw surplus. Accordingly the generic lower bound on
the quotient-kernel dimension is

```text
max(4,257 - 525,759, 0) = 0.
```

This is not a claim that the actual quotient kernel has dimension zero. It is
the exact statement needed to kill this proposed **dimension proof**: the
available rank-nullity theorem certifies no nonidentity class.

The failure is uniform in seed width. For every `r>=18`, the optimistic raw
surplus at `N=262143` is

```text
14,800*r - 262,143,
```

while the masked multiplier count is at least

```text
30,927*(r-1).
```

Their difference in favor of the masked family is

```text
30,927*(r-1) - (14,800*r-262,143)
  = 16,127*r + 231,216 > 0.
```

`endpoint_raw_gap_and_mask_capacity` and
`every_positive_width_gap_is_swallowed` formally certify these integers.
As in the earlier heterogeneous-source note, turning the ancestral multiplier
count into a typed subspace still requires restoring the omitted numerator
degree fields. Even granting that strongest intended interpretation does not
yield a positive quotient dimension, so formalizing that missing adapter
cannot rescue this route.

## 3. Why polynomial clearing pays the old power band

One might avoid localization and clear powers of `E0` (or another polynomial
identity factor) inside the finite weighted box. This is not free. For a
nonzero factor `F`, source box `(B,W,D)`, and source kernel `V`, the exact
divisible part is controlled by the guarded quotient box from
`WeightedSourceBoxQuotient6900`. The first division step is

```text
dim V <= stageBand(B,W,D,mainDegree(F),derivativeDegree(F),delta,0)
         + dim(powerStage(V,F,...,1)).
```

The new theorem `first_identity_quotient_pays_stageBand` is a direct wrapper
around the already checked `powerStage_finrank_step`; it also rewrites stage
zero back to the original `V`. Hence clearing the identity factor invokes the
same finite column difference used throughout helper deflation. There is no
separate “identity quotient refund.”

This matters because the completed `N=262143` audit is global over the current
finite-prefix family. Its exact best primary cleanup is

```text
k=61, m=547, M=740, D=244, T=122,
cleanup = 15,522,723,255,702,274.
```

The complete ledger forces every viable rectangular helper cut into one of

```text
D <= 54,
D = 55 and J <= 211,
56 <= D <= 110 and J <= 203.
```

Every region has zero necessary helper survivors in the exhaustive clipped
and unclipped scans. The tempting `(J,D)=(212,55)` helper really has positive
bands, but cheap count plus minimum primary cleanup is already red by
`643,192,288,595,280` before paying its helper-exit incidence. This is the
same obstruction after quotienting because the quotient source is the same
scalar weighted source and factor clearing uses the same bands.

## 4. Process decision

Do not spend more time on:

* widening the heterogeneous seed source before quotienting the affine
  identity;
* treating the affine identity as a target-rank reduction for scalar jets;
* clearing `E0` and counting the divided box as a free source; or
* retuning another rectangular finite-prefix helper at `N=262143`.

A reopen would need a genuinely new nonrectangular/shared-factor consumer, or
an algebraic-support theorem coupling the supplied agreement sets across
seeds. It cannot come from quotienting the already-known affine identity.

