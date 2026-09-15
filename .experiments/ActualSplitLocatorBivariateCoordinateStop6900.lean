import InjectiveBivariateGridFamilyCount6900

/-!
# Actual split locator in two prime-field seed coordinates: exact stop ledger

Keeping the two coordinates of the quadratic-extension seed independent does
avoid the immediate `Z -> (Z,Z^p)` degree multiplication.  It also changes the
finite-grid zero count from `degree` to `p * totalDegree`.  This file records
that distinction for both a global eliminant and node-membership polynomials.

The structural producer remains absent: `q | N` makes `q | rem_N(q*f)`
automatic, while the near-total identity leaves at least 24063 relaxed locator
coordinates.  A fixed-anchor cofactor chart therefore does not select the
actual split locator globally.
-/
namespace ProximityPrize.SubmissionLower.ActualSplitLocatorBivariateCoordinateStop6900

open MvPolynomial
open InjectiveBivariateGridFamilyCount6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

noncomputable section
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Exact support represented by zeros of bivariate seed polynomials. -/
def algebraicBivariateSeedSupport
    {K Seed I : Type*} [Field K]
    (nodes : Finset I) (membership : I → MvPolynomial (Fin 2) K)
    (seed : Seed → Fin 2 → K) (gamma : Seed) : Finset I :=
  nodes.filter fun i ↦ MvPolynomial.eval (seed gamma) (membership i) = 0

/-- Nodes whose bivariate membership polynomial is identically zero. -/
def fixedBivariateSeedSupportNodes
    {K I : Type*} [Field K]
    (nodes : Finset I) (membership : I → MvPolynomial (Fin 2) K) : Finset I :=
  nodes.filter fun i ↦ membership i = 0

/-- Bivariate analogue of the univariate node-incidence lemma.  The load of a
nonzero degree-`d` node polynomial on an `S x S` grid is `S.card * d`, not
`d`. -/
theorem algebraic_bivariate_seed_support_incidence
    {K Seed I : Type*} [Field K]
    (Gamma : Finset Seed) (nodes : Finset I)
    (membership : I → MvPolynomial (Fin 2) K)
    (seed : Seed → Fin 2 → K) (S : Finset K) (hS : 0 < S.card)
    (A d : Nat)
    (hmass : ∀ gamma ∈ Gamma,
      (algebraicBivariateSeedSupport nodes membership seed gamma).card = A)
    (hdegree : ∀ i ∈ nodes, (membership i).totalDegree ≤ d)
    (hseedInjective : Set.InjOn seed (↑Gamma : Set Seed))
    (hgrid : ∀ gamma ∈ Gamma, ∀ j, seed gamma j ∈ S) :
    let fixed := fixedBivariateSeedSupportNodes nodes membership
    Gamma.card * (A - fixed.card) ≤
      (nodes.card - fixed.card) * (S.card * d) := by
  classical
  let fixed := fixedBivariateSeedSupportNodes nodes membership
  let moving := nodes \ fixed
  have hfixedSub : fixed ⊆ nodes := Finset.filter_subset _ _
  have hfixedMem : ∀ gamma,
      fixed ⊆ algebraicBivariateSeedSupport nodes membership seed gamma := by
    intro gamma i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi'.1, by simp [hi'.2]⟩
  have hrow : ∀ gamma ∈ Gamma,
      A - fixed.card ≤
        (moving.filter fun i ↦
          MvPolynomial.eval (seed gamma) (membership i) = 0).card := by
    intro gamma hgamma
    have heq :
        moving.filter (fun i ↦
          MvPolynomial.eval (seed gamma) (membership i) = 0) =
          algebraicBivariateSeedSupport nodes membership seed gamma \ fixed := by
      ext i
      simp only [moving, algebraicBivariateSeedSupport, Finset.mem_filter,
        Finset.mem_sdiff]
      tauto
    rw [heq, Finset.card_sdiff_of_subset (hfixedMem gamma), hmass gamma hgamma]
  have hcolumn : ∀ i ∈ moving,
      (Gamma.filter fun gamma ↦
        MvPolynomial.eval (seed gamma) (membership i) = 0).card ≤ S.card * d := by
    intro i hi
    have hiNodes : i ∈ nodes := (Finset.mem_sdiff.mp hi).1
    have hiNonzero : membership i ≠ 0 := by
      intro hz
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨hiNodes, hz⟩)
    apply finite_family_bivariate_grid_card_le
      (Gamma.filter fun gamma ↦
        MvPolynomial.eval (seed gamma) (membership i) = 0)
      seed S hS (membership i) hiNonzero d (hdegree i hiNodes)
    · intro gamma hgamma eta heta heq
      exact hseedInjective (Finset.mem_filter.mp hgamma).1
        (Finset.mem_filter.mp heta).1 heq
    · intro gamma hgamma j
      exact hgrid gamma (Finset.mem_filter.mp hgamma).1 j
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2
  calc
    Gamma.card * (A - fixed.card) =
        ∑ gamma ∈ Gamma, (A - fixed.card) := by simp
    _ ≤ ∑ gamma ∈ Gamma,
        (moving.filter fun i ↦
          MvPolynomial.eval (seed gamma) (membership i) = 0).card := by
      exact Finset.sum_le_sum hrow
    _ = ∑ i ∈ moving,
        (Gamma.filter fun gamma ↦
          MvPolynomial.eval (seed gamma) (membership i) = 0).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _i ∈ moving, (S.card * d) := Finset.sum_le_sum hcolumn
    _ = (nodes.card - fixed.card) * (S.card * d) := by
      simp [moving, Finset.card_sdiff_of_subset hfixedSub]

/-- Exact support injectivity turns the preceding incidence estimate into the
usable bivariate degree gate. -/
theorem bounded_bivariate_seed_degree_support_locator_gate
    {K Seed I : Type*} [Field K]
    (Gamma : Finset Seed) (nodes : Finset I)
    (membership : I → MvPolynomial (Fin 2) K)
    (seed : Seed → Fin 2 → K) (S : Finset K) (hS : 0 < S.card)
    (A d : Nat)
    (hmass : ∀ gamma ∈ Gamma,
      (algebraicBivariateSeedSupport nodes membership seed gamma).card = A)
    (hdegree : ∀ i ∈ nodes, (membership i).totalDegree ≤ d)
    (hseedInjective : Set.InjOn seed (↑Gamma : Set Seed))
    (hgrid : ∀ gamma ∈ Gamma, ∀ j, seed gamma j ∈ S)
    (hsupportInjective : Set.InjOn
      (algebraicBivariateSeedSupport nodes membership seed)
      (↑Gamma : Set Seed)) :
    Gamma.card ≤ max 1 (nodes.card * (S.card * d)) := by
  classical
  by_cases hGamma : Gamma.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hGamma]
    simp
  let fixed := fixedBivariateSeedSupportNodes nodes membership
  have hfixedMem : ∀ gamma,
      fixed ⊆ algebraicBivariateSeedSupport nodes membership seed gamma := by
    intro gamma i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi'.1, by simp [hi'.2]⟩
  by_cases hsmall : fixed.card < A
  · have hincidence := algebraic_bivariate_seed_support_incidence
      Gamma nodes membership seed S hS A d hmass hdegree hseedInjective hgrid
    dsimp only at hincidence
    apply le_max_of_le_right
    calc
      Gamma.card ≤ Gamma.card * (A - fixed.card) := by
        have hpositive : 1 ≤ A - fixed.card := by omega
        simpa only [mul_one] using Nat.mul_le_mul_left Gamma.card hpositive
      _ ≤ (nodes.card - fixed.card) * (S.card * d) := hincidence
      _ ≤ nodes.card * (S.card * d) :=
        Nat.mul_le_mul_right (S.card * d) (Nat.sub_le nodes.card fixed.card)
  · have hfixedCard : fixed.card = A := by
      have hle : fixed.card ≤ A := by
        obtain ⟨gamma, hgamma⟩ := hGamma
        calc
          fixed.card ≤
              (algebraicBivariateSeedSupport nodes membership seed gamma).card :=
            Finset.card_le_card (hfixedMem gamma)
          _ = A := hmass gamma hgamma
      omega
    have hconstant : ∀ gamma ∈ Gamma,
        algebraicBivariateSeedSupport nodes membership seed gamma = fixed := by
      intro gamma hgamma
      apply Finset.Subset.antisymm
      · have hsameCard :
            (algebraicBivariateSeedSupport nodes membership seed gamma).card =
              fixed.card := by
          rw [hmass gamma hgamma, hfixedCard]
        exact (Finset.eq_of_subset_of_card_le
          (hfixedMem gamma) hsameCard.le).symm.subset
      · exact hfixedMem gamma
    apply le_max_of_le_left
    rw [Finset.card_le_one]
    intro gamma hgamma eta heta
    apply hsupportInjective hgamma heta
    rw [hconstant gamma hgamma, hconstant eta heta]

/-- A nonzero bivariate seed eliminant of the advertised total degree would
already contradict the retained period-two mass.  The missing item is its
production from the actual split locator, not its counting consumer. -/
theorem endpoint_bivariate_seed_eliminant_contradiction
    {K Seed : Type*} [Field K]
    (Gamma : Finset Seed) (seed : Seed → Fin 2 → K) (S : Finset K)
    (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0)
    (hdegree : P.totalDegree ≤ 118980103)
    (hseedInjective : Set.InjOn seed (↑Gamma : Set Seed))
    (hgrid : ∀ gamma ∈ Gamma, ∀ j, seed gamma j ∈ S)
    (hS : S.card = 2130706433)
    (hlarge : 253511670984674103 ≤ Gamma.card)
    (hzero : ∀ gamma ∈ Gamma, MvPolynomial.eval (seed gamma) P = 0) : False := by
  have hcap := finite_family_bivariate_grid_card_le Gamma seed S
    (by rw [hS]; norm_num) P hP 118980103 hdegree hseedInjective hgrid hzero
  rw [hS] at hcap
  norm_num at hcap
  omega

/-- In independent prime-field coordinates, the endpoint node-membership
budget is only 471.  The much larger number 1005598286444 is the univariate
extension-field degree budget; conversion from bivariate coordinates can cost
a factor `p`. -/
theorem endpoint_bivariate_node_membership_contradiction
    {K Seed I : Type*} [Field K]
    (Gamma : Finset Seed) (nodes : Finset I)
    (membership : I → MvPolynomial (Fin 2) K)
    (seed : Seed → Fin 2 → K) (S : Finset K)
    (hmass : ∀ gamma ∈ Gamma,
      (algebraicBivariateSeedSupport nodes membership seed gamma).card = 180413)
    (hdegree : ∀ i ∈ nodes, (membership i).totalDegree ≤ 471)
    (hseedInjective : Set.InjOn seed (↑Gamma : Set Seed))
    (hgrid : ∀ gamma ∈ Gamma, ∀ j, seed gamma j ∈ S)
    (hsupportInjective : Set.InjOn
      (algebraicBivariateSeedSupport nodes membership seed)
      (↑Gamma : Set Seed))
    (hS : S.card = 2130706433)
    (hnodes : nodes.card = 262144)
    (hlarge : 263611557201785350 ≤ Gamma.card) : False := by
  have hcap := bounded_bivariate_seed_degree_support_locator_gate
    Gamma nodes membership seed S (by rw [hS]; norm_num) 180413 471
    hmass hdegree hseedInjective hgrid hsupportInjective
  rw [hS, hnodes] at hcap
  norm_num at hcap
  omega

/-- Literal target arithmetic separating the two coordinate systems and the
fixed-anchor chart budget. -/
theorem endpoint_coordinate_and_chart_ledger :
    2130706433 * 118980103 = 253511670861102599 ∧
    253511670861102599 < 253511670984674103 ∧
    2130706433 * 471 = 1003562729943 ∧
    1003562729943 ≤ 1005598286444 ∧
    1005598286444 < 2130706433 * 472 ∧
    262144 * (2130706433 * 471) = 263077948278177792 ∧
    263077948278177792 < 263611557201785350 ∧
    263611557201785350 ≤ 262144 * (2130706433 * 472) ∧
    81732 - 57669 = 24063 ∧
    81731 - 24062 = 57669 ∧
    118980103 - 2 * 18414 = 118943275 ∧
    57669 * 2062 = 118913478 ∧
    118913478 ≤ 118943275 ∧
    118943275 < 57669 * 2063 := by
  norm_num

#print axioms algebraic_bivariate_seed_support_incidence
#print axioms bounded_bivariate_seed_degree_support_locator_gate
#print axioms endpoint_bivariate_seed_eliminant_contradiction
#print axioms endpoint_bivariate_node_membership_contradiction
#print axioms endpoint_coordinate_and_chart_ledger

end
end ProximityPrize.SubmissionLower.ActualSplitLocatorBivariateCoordinateStop6900
