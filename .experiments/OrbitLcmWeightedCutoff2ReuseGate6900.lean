import TwoSourceSharpProjectiveHighEIncidenceFrontier6900
import WeightedCutoff2ScalarListW1332256900
import QuotientFixedCentreObstruction6900

/-!
# Orbit-LCM versus the formal weighted cutoff-two scalar decoder

This file records the exact endpoint arithmetic, the same-witness evaluation
formula after orbit-LCM division, and the precise adapter that would be enough
to reuse the existing scalar decoder.  It deliberately does not identify a
moving quotient centre with a fixed received word.
-/

namespace ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900

open Polynomial
open WeightedCutoff2RepresentativeLedgerW1332256900
open ProximityPrize.Benchmark SupportRecurrence6900.Target
open TwoSourceSharpProjectiveHighEIncidenceFrontier6900
open TwoSourceSharpProjectiveResidualPackage6900
open QuotientFixedCentreObstruction6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-! ## Exact endpoint arithmetic -/

/-- An adjacent coprime pair gives an orbit-LCM saving of at least `2e`.
At the first uncovered allowance `W = 133382`, the quotient cap is `128760`.
-/
theorem quotient_cap_k2
    (e t q W ell d : Nat)
    (hWdef : W = ((131071 + e) - t) - q)
    (hwindow : e + t + q ≤ 18705)
    (hW : 133382 ≤ W)
    (hell : 2 * e ≤ ell)
    (hd : d ≤ W - ell) :
    d ≤ 128760 := by
  omega

/-- Adjacent plus shift-two coprimality gives three pairwise-coprime orbit
factors and hence an orbit-LCM saving of at least `3e`. -/
theorem quotient_cap_k3
    (e t q W ell d : Nat)
    (hWdef : W = ((131071 + e) - t) - q)
    (hwindow : e + t + q ≤ 18705)
    (hW : 133382 ≤ W)
    (hell : 3 * e ≤ ell)
    (hd : d ≤ W - ell) :
    d ≤ 126449 := by
  omega

/-- If shifts one, two, and three are all coprime, all six conjugate factors
are pairwise coprime and the quotient loses at least `6e` degrees. -/
theorem quotient_cap_k6
    (e t q W ell d : Nat)
    (hWdef : W = ((131071 + e) - t) - q)
    (hwindow : e + t + q ≤ 18705)
    (hW : 133382 ≤ W)
    (hell : 6 * e ≤ ell)
    (hd : d ≤ W - ell) :
    d ≤ 119516 := by
  omega

/-- All three numerical caps lie strictly inside the formal `W=133225`
scalar engine. -/
theorem orbit_quotient_caps_fit_cutoff2 :
    128760 ≤ w ∧ 126449 ≤ w ∧ 119516 ≤ w := by
  norm_num [w]

/-- The three bounds are sharp from only `W≥133382` and the indicated
LCM-degree lower bound: equality occurs at `e=2311,t=q=0`. -/
theorem orbit_quotient_lower_endpoint_exact :
    ((131071 + 2311 : Nat) = 133382) ∧
      (133382 - 2 * 2311 = 128760) ∧
      (133382 - 3 * 2311 = 126449) ∧
      (133382 - 6 * 2311 = 119516) := by
  norm_num

/-! ## What division does to the received word -/

/-- Exact same-node formula.  Dividing a fixed-centre scalar `B` by a
root-free orbit LCM does *not* give the quotient the fixed centre `f/Λ`:
the remainder contributes the seed-dependent term `-R/Λ`. -/
theorem quotient_eval_eq_movingCentre
    {K : Type*} [Field K]
    (Lambda B C R : K[X]) (x f : K)
    (hdecomp : B = Lambda * C + R)
    (hvalue : B.eval x = f)
    (hroot : Lambda.eval x ≠ 0) :
    C.eval x = (f - R.eval x) / Lambda.eval x := by
  apply (eq_div_iff hroot).2
  rw [← hvalue, hdecomp]
  simp only [eval_add, eval_mul]
  ring

/-- Euclidean division alone can destroy seed injectivity: any two distinct
remainders below the divisor degree have the same zero quotient.  Root
freeness at evaluation nodes does not alter this coefficient fact. -/
theorem quotient_collision_of_distinct_small_remainders
    {K : Type*} [Field K]
    (Lambda R₀ R₁ : K[X])
    (hLambda : Lambda ≠ 0)
    (hne : R₀ ≠ R₁)
    (hdeg₀ : R₀.degree < Lambda.degree)
    (hdeg₁ : R₁.degree < Lambda.degree) :
    R₀ ≠ R₁ ∧ R₀ / Lambda = R₁ / Lambda := by
  refine ⟨hne, ?_⟩
  rw [(Polynomial.div_eq_zero_iff hLambda).2 hdeg₀,
    (Polynomial.div_eq_zero_iff hLambda).2 hdeg₁]

/-- Even retaining a common received value at a root-free node does not
repair the quotient collision.  This is the local logical countergate to
reusing scalar injectivity after division. -/
theorem common_value_and_rootFree_still_allow_quotient_collision
    {K : Type*} [Field K]
    (Lambda R₀ R₁ : K[X]) (x f : K)
    (hLambda : Lambda ≠ 0)
    (_hroot : Lambda.eval x ≠ 0)
    (hne : R₀ ≠ R₁)
    (hdeg₀ : R₀.degree < Lambda.degree)
    (hdeg₁ : R₁.degree < Lambda.degree)
    (hvalue₀ : R₀.eval x = f)
    (hvalue₁ : R₁.eval x = f) :
    (R₀.eval x = f ∧ R₁.eval x = f) ∧
      R₀ / Lambda = R₁ / Lambda := by
  exact ⟨⟨hvalue₀, hvalue₁⟩,
    (quotient_collision_of_distinct_small_remainders
      Lambda R₀ R₁ hLambda hne hdeg₀ hdeg₁).2⟩

/-- Strong same-witness countergate.  For the literal sharp retained family,
division by *any* degree-at-most-`112230` multiple of its own `E0` cannot
leave all quotient polynomials agreeing with one seed-independent received
word on their original agreement sets.  Every possible orbit LCM has degree
at most `6 * 18414 = 110484`, so this applies to the proposed divisor once
its construction is supplied.

This is stronger than observing that the displayed centre formula moves: a
fixed quotient centre would force the proper, low-degree remainders into a
list of cardinality at most twelve, contradicting the sharp retained mass.
-/
theorem sharp_division_quotient_no_common_received_word
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected)
    (D : ExtensionField[X])
    (hED :
      leaf.sharpPackage.toSharpProjectiveResidualPackage.E0 ∣ D)
    (hD : D ≠ 0)
    (hDdegree : D.natDegree ≤ 112230)
    (quotientWord : Index → ExtensionField) :
    let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
    ¬ (∀ gamma ∈ P.Good, ∀ i ∈ agreement gamma,
      (P.scalar gamma / D).eval (IRSProfile.domain i) = quotientWord i) := by
  classical
  dsimp only
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  intro hquotient
  have hEpositive : 0 < P.E0.natDegree := by
    have hW := P.scalar_allowance_ge
    dsimp only [P] at hW ⊢
    omega
  have hdet : IsCoprime P.E0
      (P.a * leaf.toWeightedLeaf.cross.d -
        P.b * leaf.toWeightedLeaf.cross.c) := by
    rw [P.numerator_bezout]
    exact P.reduced_factor
  have hdecomp : ∀ gamma ∈ P.Good,
      P.scalar gamma = P.scalar gamma % D + D * (P.scalar gamma / D) := by
    intro gamma hgamma
    have hdivision := EuclideanDomain.div_add_mod (P.scalar gamma) D
    simpa only [add_comm] using hdivision.symm
  have hEdegree : P.E0.natDegree ≤ D.natDegree :=
    Polynomial.natDegree_le_of_dvd hED hD
  have hDpositive : 0 < D.natDegree := hEpositive.trans_le hEdegree
  have hdegree : ∀ gamma ∈ P.Good,
      (P.scalar gamma % D).natDegree ≤ 112229 := by
    intro gamma hgamma
    have hmod := Polynomial.natDegree_mod_lt (P.scalar gamma)
      (Nat.ne_of_gt hDpositive)
    omega
  have hsmall : P.Good.card ≤ 12 :=
    proper_residual_quotient_common_word_card_le_twelve
      P.Good Finset.univ IRSProfile.domain P.centre quotientWord
      IRSProfile.domain.injective.injOn
      (by norm_num [Index, IRSProfile.Index])
      P.E0 P.Q P.a P.b leaf.toWeightedLeaf.cross.c
      leaf.toWeightedLeaf.cross.d D selected P.scalar
      (fun gamma ↦ P.scalar gamma % D)
      (fun gamma ↦ P.scalar gamma / D)
      hEpositive hdet hED
      (fun gamma hgamma ↦ (P.scalar_data gamma hgamma).2.2.1)
      hdecomp hdegree agreement
      (fun gamma hgamma i hi ↦ Finset.mem_univ i)
      (fun gamma hgamma ↦
        leaf.agreement_card gamma (P.good_subset hgamma))
      (fun gamma hgamma i hi ↦
        (P.scalar_data gamma hgamma).2.2.2 i hi)
      hquotient
  have hlarge := P.retained_card_ge
  norm_num [TwoSourceSharpFixedScalarRetarget6900.sharpRetainedBudget] at hlarge
  omega

/-! ## The exact missing adapter -/

/-- This is the literal safe reuse boundary for the existing decoder.  A
correction may depend on the seed, but one must separately prove that the
*corrected quotient* is injective, remains below degree `w`, and agrees with
one seed-independent received word.  Orbit division supplies none of these
three facts automatically. -/
theorem corrected_quotient_family_card_lt_retained
    {Seed : Type*} {K I : Type} [Field K] [Fintype I]
    [CharP K 2130706433]
    (nodes received : I → K) (hnodes : Function.Injective nodes)
    (hI : Fintype.card I ≤ n)
    (selected : Finset Seed)
    (quotient correction : Seed → K[X])
    (hinj : Set.InjOn (fun s ↦ quotient s + correction s)
      (↑selected : Set Seed))
    (hdegree : ∀ s ∈ selected,
      (quotient s + correction s).natDegree ≤ w)
    (hagreement : ∀ s ∈ selected, a ≤
      (Finset.univ.filter fun i ↦
        (quotient s + correction s).eval (nodes i) = received i).card) :
    selected.card < retained := by
  classical
  exact WeightedCutoff2ScalarListW1332256900.scalarized_seed_family_card_lt_retained
    (K := K) (I := I) nodes received hnodes hI selected
      (fun s ↦ quotient s + correction s) hinj hdegree hagreement

end
end ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900

#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.quotient_cap_k2
#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.quotient_cap_k3
#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.quotient_cap_k6
#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.quotient_eval_eq_movingCentre
#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.quotient_collision_of_distinct_small_remainders
#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.sharp_division_quotient_no_common_received_word
#print axioms ProximityPrize.SubmissionLower.OrbitLcmWeightedCutoff2ReuseGate6900.corrected_quotient_family_card_lt_retained
