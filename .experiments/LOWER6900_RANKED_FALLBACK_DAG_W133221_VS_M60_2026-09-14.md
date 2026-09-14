# Lower 6900 ranked fallback DAG: strengthened leaf versus literal m60 CS4

Date: 2026-09-14 UTC. Scope: route selection only; no production or
submission file was changed.

## Binary recommendation

Rank the **direct same-witness DataEleven leaf** first and the **literal m60
exact-g CS4** second.  The first route begins at the benchmark endpoint's
already proved caller and can close the benchmark with one genuine no-leaf
theorem.  The m60 route is semantically attached to the literal source, but
still lacks both a concrete boundary-map definition/source CS4 theorem and a
downstream isolated-component producer.

Neither route is close to submission.  The endpoint route is the better
information bet, not a high-confidence proof path.

## Threshold correction before either route is cited

The new `W=133221` stack proves the scalar alternative

```text
small family OR deg(canonical received-direction interpolant) >= 133222.
```

The checked-in universal projective theorem and the structure
`ProjectiveHighDataElevenHighEClosedLeaf` are still the old `133120` versions.
Therefore the statement "every projective direction has degree at least
133222" is not yet an existing theorem.  It needs the mechanical retarget of
the old pole-deletion/projective-scalarization proof from the W=133119 stack
to `WeightedScalarListW1332216900`.  Numerically the one deleted pole is safe:

```text
250960796897672558 + 1 < 254684620614660120.
```

There is also a known import seam: the W133221 finite-prefix stack imports a
newer Mathlib valuation module which collides with the legacy declaration in
`V6`.  A generic adapter exists, but the same-file DataEleven join has not
been compiled.  This is mechanical packaging risk, not the structural
mathematics below, but it must be closed before reporting the 133222
projective leaf as formal.

## Rank 1: directly eliminate the strengthened same-witness leaf

### DAG

```text
actual selected bad family
  -> target_bad_family_small_or_dataEleven_high_e_closed_leaf       GREEN
  -> W133221 projective retarget, same U/Gamma/agreement/selected   OPEN-mechanical
  -> projective degree >=133222 in every nonzero direction          expected
  +  canonical wedge wrap: max(deg V0,deg V1)>=237212+ell           GREEN
  +  every existing weighted/pole/no-corner field of the same leaf  GREEN
  -> no strengthened DataElevenHighEClosedLeaf                      OPEN-structural
  -> Gamma.card < MCA
  -> SelectedBadGivenSetsBound -> ProtocolClaim 6900                GREEN callers
```

Here `V_r` is the canonical all-node interpolant of the actual received row
`U r`, and `ell=max(deg L,deg M)` for the leaf's stored aligned cross.

### Narrowest exact theorem

After defining the 133222 predicate, the theorem should be stated directly
on the existing leaf rather than on a new abstract A57 object:

```lean
def CanonicalHighTailDirectionIndependent133222
    (nodes : I ↪ K) (U : Fin 2 → I → K) : Prop :=
  ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) →
    133222 ≤
      (receivedDirectionInterpolant nodes
        (fun i ↦ a * U 0 i + b * U 1 i)).natDegree

theorem no_projectiveHigh133222_dataElevenHighEClosedLeaf
    {U Gamma agreement selected}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected)
    (hhigh : CanonicalHighTailDirectionIndependent133222
      IRSProfile.domain U) : False
```

This statement has the correct actual caller and retains every potentially
load-bearing same-family field.  Any stronger source/A57 theorem should be
justified only if it gives a shorter proof of this exact statement.

### A57 calibration and falsifier

The favorable monomial pair suggested by the new bounds,

```text
(V0,V1)=(X^237212,X^133222),
```

does make the enlarged 300-channel direct A57 cyclic interval envelope cover
all 262144 coefficients.  This is a useful positive calibration.  It proves
only support coverage for independently variable residual windows; it does
not prove rank of the actual correlated physical source.

More importantly, the two endpoint degree consequences do **not** force that
favorable pair.  The kernel-checked countergate uses

```text
(V0,V1)=(X^262143,X^262142).
```

Every nonzero constant direction has degree at least 262142, hence at least
133222.  Its maximum row degree satisfies `237212+ell` for every feasible
`ell<=24931`.  Nevertheless even the enlarged direct envelope misses the
whole cyclic interval

```text
208036 .. 262097
```

of dimension 54062.  In particular coefficient 208036 is zero on all 300
independently enlarged channels.  The formal artifact is
`Full187A57WedgeHighEndpointMonomialCountergate6900.lean`; it compiles with
only standard axioms.  The independent exact interval replay, including the
favorable-pair full-coverage calibration, is
`full187_a57_wedge_high_endpoint_interval_falsifier_6900.py`.

**Thirty-minute kill criterion.** Reject any proposed leaf/A57 bridge if its
proof uses only projective-high degree and the wedge-wrap degree inequality.
Within thirty minutes it must name and use at least one additional actual
leaf field--for example `cross_fixed_scalar`, `cross_weighted_low_window`,
`cross_no_adjacent_hard_corner`, or a retained-family incidence field--to
rule out the hostile pair or constrain the actual A57 right hand side.  If it
cannot, stop the A57-degree lane and return to direct same-family incidence.

### Hidden attachment gap

There is currently no theorem-level arrow from the A57 local block to
Full187/CS4:

* commit `8b1b1fc` added only a Markdown note and a Python computation;
* no Lean definition packages the literal A57 quotient map on the Full187
  source;
* no A57 theorem returns `Function.Surjective`,
  `CoupledSchurGainFour`, or `NoNonzeroDualContactRelation`;
* the universal stop files deliberately enlarge independent channel windows
  and are negative envelopes, not constructors of correlated source rows.

Thus interval coverage at `(237212,133222)` cannot be called an attached
Full187 breakthrough.  The first honest bridge would have to define the
literal A57 quotient map with source provenance and show that the actual
packet/right-hand side lies in its range.

## Rank 2: literal m60 exact-g CS4

### DAG

```text
C_g = globalPassiveArrayConstraint
      K I 60 (60*g) 131071 82 21 10 2703 ...                    GREEN literal
  -> exactGGroundContact and coefficient base change             GREEN
  -> K_g = ker(baseChangedContact C_g)                            GREEN type
  -> concrete four-boundary map beta_gamma on K_g                NOT DEFINED
  -> forall gamma, Surjective(beta_gamma)                         OPEN CS4
  -> four common literal exact-g rows                             GREEN conditional
  -> exact source support + direct contact zero + graph forcing   GREEN
  -> isolated component/allocation producer per exact g           OPEN
  -> sum over 81732 exact-g strata + bad-family protocol          GREEN arithmetic/callers
```

This route is attached to the true source: the domain is exactly

```text
PassiveSourceIndex (60*g) 131071 82 21 10 2703 -> K,
```

and base-change naturality plus literal graph root forcing have been proved.
Its hidden mismatch is later: every existing common-row theorem accepts an
arbitrary caller-supplied `boundary : Gamma -> K_g -> Fin 4 -> L`.  No file
defines the intended four coefficient/jet functionals from the actual
candidate graph.

### Narrowest exact theorem

First define `literalBoundaryAt` over `L=RatFunc K` (or the chosen equivalent
fraction field) from the literal four boundary coefficient functionals.
Then the source theorem is exactly:

```lean
theorem literal_exactG_full187_CS4
    {I K Gamma} [Fintype I] [Field K] [Finite Gamma]
    (g : Nat) (hg : 180413 ≤ g)
    (nodes values0 values1 : I → K)
    (candidate : Gamma → CandidateGraphData ...)
    (hretainedBad : ∀ gamma, RetainedBad ... (candidate gamma)) :
    ∀ gamma,
      Function.Surjective
        (literalBoundaryAt g nodes values0 values1
          (candidate gamma) :
          BaseChangedCompleteKernel
            (K := K) (L := RatFunc K)
            (Target := PassiveGlobalConstraintTarget K I 60 82 21 10 2703)
            (exactGGroundContact I g nodes values0 values1) →ₗ[RatFunc K]
              (Fin 4 → RatFunc K))
```

The ellipses cannot honestly be erased yet: `CandidateGraphData`,
`RetainedBad`, and especially `literalBoundaryAt` are precisely the missing
concrete definitions.  Once supplied, the conclusion matches
`exists_four_common_literal_exactG_rows` definitionally.

### Thirty-minute falsifier

The highest-information small test is the already isolated strengthened-m60
first-gap continuation, at exact `g=181250`: construct the literal grade-19
quotient, project only the three Y/R/S boundary right-hand sides, and compute
the proposed 3x3 minor from the three legal rows

```text
(b,e)=(0,8), (1,8), (0,7)
```

in total layer `d=42,q=21,t=8`, including centering and all lower-layer
leakage.  Kill this continuation subroute immediately if any row is not in
the literal source, if its projected column is not well-defined after earlier
pivots, or if the determinant is zero in one target-faithful finite-field
instance.  Because local prolongation, automatic holonomy, and the full
cokernel locator block have already been falsified, failure of this 3x3 gate
leaves no current concrete m60 producer and should demote the whole route.

## Scheduling decision and honest estimates

1. Spend one short slot compiling the W133221 projective retarget and same-
   witness join.  This removes the stale 133120 interface and packaging
   uncertainty.
2. Spend the main breakthrough slot on a full-leaf consequence which uses a
   named global same-family field.  Do not spend it on degree-only A57 maps.
3. In parallel, allow one bounded m60 3x3 continuation test.  Do not rebuild
   common-row/base-change/root-forcing wrappers.

Estimated end-to-end completion is roughly 15--20% on either route and
uncertainty remains about 80--90%.  The direct leaf route ranks first because
its input and terminal caller are exact; the m60 route has more local
infrastructure but two independent unfilled arrows after CS4.  There is no
honest submission ETA from either current DAG.
