# k=0 accepted-recurrence splice for exact-G lower 6900

Date: 2026-09-14 UTC. Scope: lower 6900 only. This is a bounded source-proof
audit plus two small abstract Lean lemmas. It is not a candidate, a target
rank theorem, or a submission change.

## Verdict

There is no already-formalized recurrence which can be instantiated directly
to turn the two tiny bordered determinants into the target rank-four theorem.
The closest reusable proof is a **two-level triangular splice**:

1. use the strong-induction shape of the accepted 6810
   `TriangularKernel.eq_zero_of_triangular` / `SecondJetBasis.pack_initial_coeff`
   for the first live agreement-Newton coefficient and then for the ordered
   error mismatches; and
2. inside each error step use the current reverse-Hasse product recurrence and
   descending-moment closure to remove all product-rule tails and localize one
   chosen error.

The first level is not linear: the tiny raw minor contains a positive power of
the mismatch. `K0MismatchTriangularCover6900.lean` proves the required
nonlinear strong-induction wrapper. The second level now has a compiled
singleton endpoint in `K0HrsErrorLocalizationSplice6900.lean`.

What remains is not an induction lemma. It is the literal-source theorem that
identifies the rank-defect cofactors with a compatible family of bounded
reverse-Hasse multiplier equations and proves their agreement-Newton leading
term. Without that theorem, the accepted recurrence and the HRS recurrence do
not meet.

## 1. Closest mechanism in the accepted 6810 proof

Commit `09d8a2a` is the accepted 6810 submission. The relevant general theorem
is in `ProximityPrize/SubmissionLower/LowerGeometry.lean`:

```lean
theorem TriangularKernel.eq_zero_of_triangular
    (F : (forall i, V i) ->ₗ[K] (forall i, W i))
    (D : forall i, V i ->ₗ[K] W i)
    (hD : forall i, Function.Injective (D i))
    (hdiag : forall v i, (forall j, j.val < i.val -> v j = 0) ->
      F v i = D i (v i))
    (v : forall i, V i) (hv : F v = 0) : v = 0
```

It is used by `SecondJetBasis.truncate_pack_injective`. The key extraction is

```lean
theorem SecondJetBasis.pack_initial_coeff ...
    (hp : forall j, j.val < r.val -> p j = 0) :
    (pack v a b p).coeff r.val =
      sum h, X^h.val * C (v^(a r h + b r h) * p r h)
```

and the diagonal multiplication is injective because `v != 0`. This is the
right formal pattern for “earlier Newton slots vanish, so the first live slot
survives with a nonzero diagonal.” It says nothing by itself about the target
contact map.

The accepted `BoundaryTailRecurrence.refined_monomial_step`, together with
`BoundaryTailRepresentation.refinedCoefficientStep_represents` and
`BoundaryTailCoefficientFacts.refinedCoefficients_zero_recurrence`, is not the
needed recurrence. Its induction variable is the differential/contact
multiplicity `m`; its three bands shift the exponent of `polyG`, `polyH`, and
`boundaryJ`. It does not order physical error nodes, does not mention the
values `U1(i)-Q_G(i)`, and does not extract agreement Newton coefficients.
The `Higher*6810` phase recurrences are numerical phase/charge ledgers and are
likewise not a source identity.

## 2. Closest current HRS mechanism

The useful local identity is

```lean
HrsU0PoleCancellation6900.reversedHasse_mul :
  reversedHasse alpha depth (U*g) i =
    U.eval alpha * reversedHasse alpha depth g i +
      reversedHasseUpperTail alpha depth U g i
```

`HrsU0PCInteriorOrdering6900.intrinsic_term_earlier_or_unit_diagonal`
places every PC/contact/Hasse term strictly earlier in the intrinsic key or on
the exact unit diagonal, and
`reversedHasse_mul_intrinsic_upper_triangular` places every product-rule tail
at a larger reversed-Hasse index. The compiled global closure is

```lean
theorem all_reversedMoments_eq_zero_of_all_multiplier_equations
    (nodes : I -> K) (depth w : Nat) (g : I -> K[X])
    (hsource : forall i, i < depth -> forall V : K[X],
      V.natDegree < w ->
        (sum x, reversedHasse (nodes x) depth (V * g x) i) = 0) :
    forall i, i < depth -> forall V : K[X], V.natDegree < w ->
      reversedMoment nodes depth i g V = 0
```

from `HrsGlobalDescendingMomentClosure6900`. It feeds
`selected_sum_eq_zero_of_all_source_equations`. The new singleton wrapper is

```lean
theorem singleton_reversedHasse_eq_zero_of_all_multiplier_equations
    (nodes : I -> K) (depth w : Nat) (g : I -> K[X])
    (U : K[X]) (selected : I) (i : Nat) (hi : i < depth)
    (hU : U.natDegree < w)
    (hselected : U.eval (nodes selected) != 0)
    (hroot : forall x, x != selected -> U.eval (nodes x) = 0)
    (hsource : forall k, k < depth -> forall V : K[X],
      V.natDegree < w ->
        (sum x, reversedHasse (nodes x) depth (V * g x) k) = 0) :
    reversedHasse (nodes selected) depth (g selected) i = 0
```

For the exact-G profile, apply this with `I` equal to the error set, not the
full 262144-node set. If `e = 262144-g`, then `e <= 81731`, and the simple
complement locator for one error has degree `e-1 <= 81730 < w=131071`.
Injectivity of the evaluation domain makes its value at the selected error
nonzero. Thus, once `hsource` has actually been derived, localization costs no
depth-fold locator and works at every reverse-Hasse coordinate.

Taking `I` to be all nodes is incompatible with this argument: a strict
degree-`w` polynomial cannot vanish on the other 262143 distinct nodes. The
agreement contributions must first be eliminated from the literal all-node
contact relation.

## 3. Exact theorem splice to prove

Fix one exact maximal agreement set `G`, `G.card=g`, the profile

```text
(m,B,s,U,L) = (47,16,8,64,3757),  D=47*g,
w=131071,  E=G^c,  E.card<=81731.
```

Let `QG` be the unique degree-`<g` interpolant of `U1` on `G`. The target
rank-defect recovery follows from the following three source statements.

### A. Agreement first-live-coordinate theorem

Choose ordered anchors `H subset G`, `H.card=w+1`, let `qH` interpolate `U1`
on `H`, and expand

```text
T = (QG-qH)/Lambda_H
```

in the Newton basis on `G\H`. Formalize:

```lean
theorem k0_first_live_agreement_newton
    (hnotLow : not (exists q : K[X], q.natDegree <= w /\
      forall i in G, q.eval (domain i) = U 1 i)) :
    exists r a,
      (forall j, j < r -> newtonCoeff T j = 0) /\
      newtonCoeff T r = a /\ a != 0
```

The Newton division/evaluation facts are elementary, but the source-facing
statement must additionally prove that later coefficients occur only in
earlier/off-diagonal target keys. The tiny chamber has constant `T=a`; the
target `T` can have degree up to `g-w-2`, so its `a^17` factor cannot simply be
copied from the chamber.

### B. Literal PC/HRS error recurrence

For every ordered error, extract from the rank-defect cofactor data one local
polynomial family `gerr : E -> K[X]` and prove all legal equations:

```lean
theorem k0_literal_pc_error_moments
    (hrank : Module.finrank L (LinearMap.range normal) < 4) :
    exists depth (gerr : E -> K[X]),
      (forall k, k < depth -> forall V : K[X],
        V.natDegree < w ->
          (sum x : E,
            reversedHasse (domain x) depth (V * gerr x) k) = 0) /\
      ErrorCofactorRepresentation depth gerr
```

`ErrorCofactorRepresentation` must identify a chosen localized coordinate,
after earlier mismatches vanish, with an actual fixed raw bordered numerator:

```lean
certificate eps i =
  coefficient eps i * eps i ^ power i,
0 < power i,
coefficient eps i != 0.
```

Here

```text
eps_i   = U1(i)-QG(domain i),
delta_i = P(domain i)-U0(i)-gamma*U1(i) != 0.
```

The coefficient may contain positive powers of the first live agreement
coefficient `a`, of `delta_i`, and nonzero Vandermonde factors. Exact
maximality of `G` supplies `delta_i != 0`. Do not hard-code the chamber
exponents `22,17,22`: they are evidence for positivity and factor shape, not
a target formula.

Rank defect makes every four-bordered raw minor zero. The compiled nonlinear
wrapper then gives `eps=0`:

```lean
theorem eq_zero_of_power_triangular
    (certificate coefficient : (Fin n -> K) -> Fin n -> K)
    (power : Fin n -> Nat) (mismatch : Fin n -> K)
    (hcoefficient : forall i, earlierZero mismatch i ->
      coefficient mismatch i != 0)
    (hdiagonal : forall i, earlierZero mismatch i ->
      certificate mismatch i =
        coefficient mismatch i * mismatch i ^ power i)
    (hzero : certificate mismatch = 0) : mismatch = 0
```

The HRS singleton lemma closes the inner reverse-Hasse tail after the first
conjunct of `k0_literal_pc_error_moments`; the power-triangular lemma closes
the outer ordered-error induction after `ErrorCofactorRepresentation`.

### C. Globally matched adjacent-carrier theorem

On `eps=0`, `U1` equals `QG` on every node. Prove that the adjacent unshifted
carrier gives a nonzero four-border certificate whenever the first live
agreement coefficient is nonzero:

```lean
theorem k0_globally_matched_border_nonzero
    (hnotLow : not LowMatch) (heps : eps = 0) :
    matchedCertificate eps != 0
```

and the formal rank implication

```lean
theorem k0_rankDefect_kills_matched_border
    (hrank : Module.finrank L (LinearMap.range normal) < 4) :
    matchedCertificate eps = 0
```

Together A--C instantiate the compiled theorem

```lean
rankDefect_implies_lowMatch_of_power_triangular_cover
```

to obtain the source-facing endpoint

```lean
theorem k0_rankDefectRecovery_on_original_agreement
    (hrank : Module.finrank L (LinearMap.range normal) < 4) :
    exists h : K[X], h.natDegree <= w /\
      forall i in A, h.eval (domain i) = U 1 i
```

Take `h=QG` after `LowMatch`; since the supplied bad agreement `A` is
contained in the maximal exact agreement `G`, restriction gives the displayed
conclusion. This is exactly the premise consumed by the already compiled
`GlobalO2BadRowConormalBridge6900.full_rank_four_of_bad_and_rank_defect_recovery`.

## 4. Precise incompatibilities / load-bearing gaps

1. **Determinant versus linear HRS data.** HRS is linear in the local dual
   numerators. A raw bordered determinant is nonlinear in received values.
   A cofactor/adjugate construction must turn rank defect into one compatible
   global HRS family and prove that its localized coordinate is the selected
   raw minor. None of the current HRS files supplies that construction.
2. **All-node to error-only.** `LITERAL-PC-MOMENTS` has to be proved after
   complete agreement PC/carrier elimination. Merely classifying omitted
   terms as `intrinsicKeyEarlier` does not prove the equations required by
   `hsource`.
3. **Two different triangular orders.** HRS closes Hasse indices inside one
   intrinsic target coordinate. It does not order error nodes or agreement
   Newton coefficients. Those are the two outer inductions above.
4. **The existing centered shell diagonal is the wrong scalar.** In
   `HrsCenteredShellUnit6900.centeredLocalShell_lowest_coeff`, the lowest
   coefficient is a power of the nonzero value residual `delta`; mismatch
   terms occur above that pivot. It therefore cannot supply the positive
   power of `eps` seen by the first bordered minor.
5. **Old exact-G F3 modules are profile-mismatched.** The compiled
   `HrsP4RHSAllExactG6900` and `HrsP4RHSErrorResidualGate6900` use the old
   order-60 profile. Their agreement-contact and one-syndrome interfaces are
   useful templates, but they do not establish legality or correction for
   `(47,16,8,64,3757)`.
6. **The Full187 local recurrences are insufficient.** The exact identities
   `local_locator_rs_recurrence` and
   `local_received_direction_recurrence` lead to global Hermite divisibility,
   but they do not imply the special adjacent-carrier annihilator or rank
   four; existing exact counterexamples already separate those claims.
7. **Accepted Higher6810 is not a hidden shortcut.** Its fixed four-variable
   carrier and hard-coded agreement 181294 do not accept the moving seed
   carrier or agreement 180413, as recorded in
   `FULL187_TO_HIGHER6810_SPLICE_EXACT_STOP_6900.md`.

Thus the decisive next theorem is B plus its cofactor representation, with A
as the necessary agreement-side leading-term companion. More profile scans,
ambient error-surjectivity, and target-sized dense minors do not address this
splice.

## 5. Lean receipts

The two new files compile under the task-local 8 GiB cap. Their printed axioms
are only `propext`, `Classical.choice`, and `Quot.sound`:

```text
.experiments/K0MismatchTriangularCover6900.lean
  eq_zero_of_power_triangular
  rankDefect_implies_lowMatch_of_power_triangular_cover

.experiments/K0HrsErrorLocalizationSplice6900.lean
  singleton_reversedHasse_eq_zero_of_all_multiplier_equations
```

No broad grid or target-sized dense matrix was run.
