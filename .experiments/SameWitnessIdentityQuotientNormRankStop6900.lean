import ProjectiveHighLeafResidualIdentityDebt6900
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Exact rank obstruction for a seed-faithful agreement quotient

The natural residual-coordinate relations leave almost every retained seed
in an identity fibre.  A quotient-norm or Fitting reformulation cannot make
those fibres cheap merely by placing them in a finite algebra: if the quotient
still has a character for every retained seed and an element whose value at
that character is the seed itself, the characters are linearly independent.
Thus the algebra rank is at least the number of retained seeds.

After deleting the entire endpoint identity allowance `1121769749`, the
exact same-witness identity family still forces rank at least
`253511669862642210`.  This is over five billion times the maximum cumulative
eliminant degree `42700739`.

The theorem is deliberately conditional on seed-faithfulness.  A smaller
quotient must collapse or omit these identity seeds, and therefore has to pay
them as uncovered mass; this file does not claim that every possible new
relation factors through the natural residual quotient.
-/

namespace ProximityPrize.SubmissionLower.SameWitnessIdentityQuotientNormRankStop6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ProjectiveHighLeafResidualIdentityDebt6900
open ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- Distinct algebra characters are linearly independent.  If each seed is
recovered by evaluating one distinguished quotient element, the number of
seeds cannot exceed the finite module rank of the quotient. -/
theorem seed_faithful_characters_card_le_finrank
    {K A : Type*} [Field K] [DecidableEq K] [Ring A] [Algebra K A]
    [FiniteDimensional K A]
    (Seeds : Finset K) (seedCoordinate : A)
    (character : K → A →ₐ[K] K)
    (hseed : ∀ gamma ∈ Seeds,
      character gamma seedCoordinate = gamma) :
    Seeds.card ≤ Module.finrank K A := by
  let characterOnSeeds : ↑Seeds → (A →ₐ[K] K) :=
    fun gamma ↦ character gamma.1
  have hinjective : Function.Injective characterOnSeeds := by
    intro gamma delta heq
    apply Subtype.ext
    have hvalue := DFunLike.congr_fun heq seedCoordinate
    simpa only [characterOnSeeds, hseed gamma.1 gamma.2,
      hseed delta.1 delta.2] using hvalue
  have hlinear : LinearIndependent K
      (fun gamma : ↑Seeds ↦ (characterOnSeeds gamma).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K A K).comp
      characterOnSeeds hinjective
  have hcard := hlinear.fintype_card_le_finrank
  rw [Fintype.card_coe, Subspace.dual_finrank_eq] at hcard
  exact hcard

/-- Deleting a charged exceptional set can reduce the seed-faithful rank by
at most the number actually deleted. -/
theorem seed_faithful_characters_after_discard_rank
    {K A : Type*} [Field K] [DecidableEq K] [Ring A] [Algebra K A]
    [FiniteDimensional K A]
    (Seeds discarded : Finset K) (seedCoordinate : A)
    (character : K → A →ₐ[K] K)
    (hseed : ∀ gamma ∈ Seeds \ discarded,
      character gamma seedCoordinate = gamma) :
    Seeds.card - discarded.card ≤ Module.finrank K A := by
  have hrank := seed_faithful_characters_card_le_finrank
    (Seeds \ discarded) seedCoordinate character hseed
  have hcard : Seeds.card - discarded.card ≤
      (Seeds \ discarded).card := by
    have hintersection : (discarded ∩ Seeds).card ≤ discarded.card :=
      Finset.card_le_card (Finset.inter_subset_left)
    rw [Finset.card_sdiff]
    omega
  exact hcard.trans hrank

/-- At the exact same-witness identity-family lower bound, even spending the
whole allowed identity/uncovered mass leaves a quotient rank of at least
`253511669862642210`. -/
theorem endpoint_identity_majority_forces_huge_quotient_rank
    {K A : Type*} [Field K] [DecidableEq K] [Ring A] [Algebra K A]
    [FiniteDimensional K A]
    (IdentitySeeds discarded : Finset K)
    (hidentity : 253511670984411959 ≤ IdentitySeeds.card)
    (hdiscarded : discarded.card ≤ 1121769749)
    (seedCoordinate : A) (character : K → A →ₐ[K] K)
    (hseed : ∀ gamma ∈ IdentitySeeds \ discarded,
      character gamma seedCoordinate = gamma) :
    253511669862642210 ≤ Module.finrank K A ∧
      42700739 < Module.finrank K A := by
  have hrank := seed_faithful_characters_after_discard_rank
    IdentitySeeds discarded seedCoordinate character hseed
  constructor
  · exact (show 253511669862642210 ≤
        IdentitySeeds.card - discarded.card by omega).trans hrank
  · have hlarge : 253511669862642210 ≤ Module.finrank K A :=
      (show 253511669862642210 ≤
        IdentitySeeds.card - discarded.card by omega).trans hrank
    omega

/-- Direct adapter to the exact lossless projective-high leaf.  For the same
`Good/agreement/selected` witness and its natural residual rows, no
finite-dimensional quotient of rank at most `42700739` can retain the seed
coordinate on all identity seeds after discarding only the permitted
`1121769749` candidates. -/
theorem projectiveHigh_leaf_no_small_seed_faithful_identity_quotient
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    {A : Type*} [Ring A] [Algebra ExtensionField A]
    [FiniteDimensional ExtensionField A]
    (leaf : ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected)
    (hrank : Module.finrank ExtensionField A ≤ 42700739) :
    ∃ Good : Finset ExtensionField,
      ∃ row0 row1 : Index → ExtensionField,
      Good ⊆ Gamma ∧ 253511670984674103 ≤ Good.card ∧
      (∀ gamma ∈ Good, ∀ i ∈ agreement gamma,
        row0 i + gamma * row1 i = 0) ∧
      253511670984411959 ≤
        (Good \ activeSeeds Good agreement row0 row1).card ∧
      ∀ discarded : Finset ExtensionField,
        discarded.card ≤ 1121769749 →
        ∀ (seedCoordinate : A)
          (character : ExtensionField → A →ₐ[ExtensionField] ExtensionField),
          ¬ (∀ gamma ∈
              (Good \ activeSeeds Good agreement row0 row1) \ discarded,
            character gamma seedCoordinate = gamma) := by
  obtain ⟨Good, row0, row1, hsub, hcard, hrelation, hidentity, _⟩ :=
    projectiveHigh_leaf_natural_residual_identity_debt leaf
  refine ⟨Good, row0, row1, hsub, hcard, hrelation, hidentity, ?_⟩
  intro discarded hdiscarded seedCoordinate character hseed
  have hseed' : ∀ gamma ∈
      (Good \ activeSeeds Good agreement row0 row1) \ discarded,
      character gamma seedCoordinate = gamma := by
    intro gamma hgamma
    apply hseed gamma
    simpa only [Finset.mem_sdiff] using hgamma
  have hlarge := endpoint_identity_majority_forces_huge_quotient_rank
    (Good \ activeSeeds Good agreement row0 row1) discarded hidentity
      hdiscarded seedCoordinate character hseed'
  omega

/-- Exact amount by which the rank forced after the full identity allowance
exceeds the cumulative eliminant-degree gate. -/
theorem endpoint_identity_quotient_rank_excess :
    253511669862642210 - 42700739 = 253511669819941471 := by
  norm_num

/-- The preceding lower bound is more than `5,936,938,699` times the allowed
rank.  This integer quotient is included only as a scale receipt. -/
theorem endpoint_identity_quotient_rank_ratio :
    5936938699 * 42700739 ≤ 253511669862642210 := by
  norm_num

#print axioms seed_faithful_characters_card_le_finrank
#print axioms seed_faithful_characters_after_discard_rank
#print axioms endpoint_identity_majority_forces_huge_quotient_rank
#print axioms projectiveHigh_leaf_no_small_seed_faithful_identity_quotient
#print axioms endpoint_identity_quotient_rank_excess
#print axioms endpoint_identity_quotient_rank_ratio

end
end ProximityPrize.SubmissionLower.SameWitnessIdentityQuotientNormRankStop6900
