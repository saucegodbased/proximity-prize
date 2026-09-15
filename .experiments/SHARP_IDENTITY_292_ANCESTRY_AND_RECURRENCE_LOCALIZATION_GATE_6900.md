# Sharp identity locus with at most 292 outside nodes: ancestry and recurrence gate

Date: 2026-09-15 UTC. Lower 6900 only. No production or candidate edit.

## Verdict

The branch

```text
|Z| >= 261852, hence |Z^c| <= 292
```

is **not ruled out by any existing actual-source or realization theorem**.
The normalized-source ancestry makes the two fixed rows tautologies on the
covered nodes; the exact DataNine/primitive-conic four-row operator also
recombines to the zero equation at every node.  Thus replaying `Realizes`,
the aligned cross, or the four source equations cannot exclude a large `Z`.

There is nevertheless one genuine improvement over the older large-identity
audit: with only 292 outside nodes, original-recurrence localization now fits
comfortably.  The new compiled theorem gives a nonzero localization factor of
degree at most 18706 and carries every degree-81731 recurrence into grade
100437, leaving exactly 30635 shifts.  The previous 6020-degree deficit is
gone in this branch.

This is a **frontier advance, not a count**.  No existing consumer proves that
any of the 30635 substituted equations is independent of the already-used
normalized source.  The exact off-fibre target remains

```text
875068543039973,
```

and this gate currently proves no numerical upper bound toward it.

## Earliest exact full-leaf hypothesis absent from the countercontrol

The scaled seven-node countercontrol in
`W133225FullHypothesisBoundaryCountercontrol6900.lean` simultaneously has:

* selected agreement and selected badness;
* projective-highness in every nonzero received direction;
* agreement-locator factorizations with nonzero short residuals;
* the two fixed residual rows zero on every node;
* two distinct scalar top fibres;
* the literal cross equation and all four source equations; and
* scaled content/grade bounds.

Reading the fields of
`TwoSourceSharpProjectiveHighEIncidenceLeaf` in declaration order, its first
failure is the first field, `toWeightedLeaf`: the control does not construct
the exact target `DataEleven U`, target `PrimitiveConicData`, and their
target-domain realization/provenance.  It does **not** first fail at
`projectiveHigh`, `selected_bad`, the residual factorization, or the aligned
source identities; those all have literal checked analogues.

That structural field boundary must not be mistaken for evidence that
DataEleven ancestry excludes the control.  Two exact in-repository facts point
the other way:

1. `selected_family_fixed_scalar_producer` chooses

   ```text
   a = V0 + c*Q0,
   b = V1 + d*Q0,
   Q*centre = f-Q0
   ```

   on covered nodes.  Substitution makes both fixed identity rows vanish
   without a root count.
2. `actual_moving_operator_received_word_identity` applies to the same exact
   `DataNine` and `PrimitiveConicData` source and proves that the four restored
   source rows recombine to zero at every original node and every seed.

The in-repository reciprocal profile audit additionally checks that the named
DataNine numerical/profile conditions are compatible with an all-node
identity source; it does not construct the enormous family.  Therefore the
first genuinely unmodeled ingredient is target-size **same-family incidence**,
not a known source/Realizes contradiction.

## Exact recurrence-localization receipt

The hard branch and sharp high-E package give

```text
outside nodes       <= 292
deg E0              <= 18414
localization cost   <= 18706
original grade      <= 81731
localized grade     <= 100437
last allowed shift  = 30634
number of shifts    = 30635.
```

The new Lean module proves the exact arithmetic and the algebraic transport:

```text
q in recurrenceSpace(L,131071,81731)
  =>
(E0 * locator(Z^c)) * q
  in recurrenceSpace(L,131071,100437).
```

It also proves the localized product is nonzero whenever `E0` and `q` are
nonzero.  In the exact leaf, `E0 != 0` is a sharp-package field, while
`nullity >= 7459` supplies a nonzero recurrence.  Mapping `E0` and the domain
nodes into the target generic-seed field preserves degree and nonzeroness, so
the target adapter is mechanical; the small generic module avoids loading the
large leaf import graph under the 4 GiB audit cap.

## Consumer/provenance audit

The only existing theorem which consumes all 30635 shifts automatically is
the defining membership theorem for `recurrenceSpace` (plus polynomial
multiplication).  `PuncturedNodalRecurrence.evaluatedRecurrence_removed_locator`
rewrites the same equations using punctured nodal weights; it does not prove
that a substituted centre functional is nonzero.  No existing theorem takes

```text
localized nonzero q
+ fixed identity rows
+ target-size retained scalar family
```

and returns either a nonzero centre constraint, a rank lower bound, or a
candidate-count upper bound.

The distinction is load-bearing.  The recurrence space is constructed from
the received rows `U`, so its vectors may adapt to the arbitrary fixed centre.
Substituting

```text
E0*U0 = a + Q*c*centre,
E0*U1 = b + Q*d*centre
```

into a recurrence derived from those same rows is an algebraic rewrite, not
an independent equation.  The archived reciprocal actual-source control has
an arbitrary pointwise base-fixed centre and a large original recurrence
space while both identity rows hold everywhere.  Hence nonzero localized
`q` alone does not certify a nonzero projection on the centre.

## Falsifiable re-entry theorem

This route should be reopened only by proving an exact same-witness theorem
of the following form:

```text
NonzeroIdentityCoreRecurrenceProjection:
  for the exact sharp leaf and |Z^c|<=292,
  some q in the actual grade-81731 recurrence space and some r<=30634
  have a nonzero post-substitution projection on the retained scalar/centre
  data, with a quantified rank or fibre bound.
```

Merely restating localized recurrence membership, the cross determinant, or
the four source rows fails this test.  A valid theorem must use the enormous
same-family incidence in its nonzeroness proof, because the source-only
countercontrol satisfies the other premises.

## Verification

Compiled file:

```text
.experiments/SharpIdentity292RecurrenceLocalizationGate6900.lean
```

It was checked with `.experiments/run_lean_4g_capped.sh` under Lean's 3.5 GiB
allocator cap in about 2.8 seconds.  Printed axioms for every theorem are only
`propext`, `Classical.choice`, and `Quot.sound`.  There is no `sorry`, `admit`,
`native_decide`, or `unsafe` declaration.

