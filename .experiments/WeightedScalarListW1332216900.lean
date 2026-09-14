import WeightedPrimaryAllFactorReductionW1332216900
import WeightedActiveBatchCountW1332216900

/-! Complete scalar-list bound at W=133221.  The primary source, helper
escape, shortened-Johnson cap, heavy/cheap partition, and nonactive cleanup
are all supplied by proved producers. -/
namespace ProximityPrize.SubmissionLower.WeightedScalarListW1332216900

open WeightedPrimaryAllFactorReductionW1332216900
open WeightedRepresentativeCountLedgerW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Direct composed bound.  It is 721 below the ledger's advertised complete
cap because the semantic nonactive cover does not need a separate Y-only
charge. -/
theorem scalar_finite_list_card_le
    {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144) (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagreement : ∀ P∈Gamma,180413≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card) :
    Gamma.card≤250960796897672558 := by
  obtain ⟨Q,hQ,hweighted,hbox,hsolution,hcleanup⟩ :=
    exists_primary_source_and_nonactive_bound nodes received hinj hI
      Gamma hdegree hagreement
  obtain ⟨hT,hRT,hJet⟩ := primary_source_weighted_caps Q hbox
  have hTdegree := (primary_source_coordinate_caps Q hbox).2.2
  have hactive :=
    WeightedActiveBatchCountW1332216900.activeTRegular_card_le
      Q hQ hT hTdegree hRT hJet Gamma nodes received hinj hI
      hdegree hagreement
  rw [active_caps_exact.1,active_caps_exact.2] at hactive
  omega

theorem scalar_finite_list_card_lt_retained
    {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144) (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagreement : ∀ P∈Gamma,180413≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card) :
    Gamma.card<253511670984674103 := by
  exact (scalar_finite_list_card_le nodes received hinj hI Gamma
    hdegree hagreement).trans_lt (by norm_num)

/-- Injective only on the selected family; no arbitrary global extension of
the scalarization map is required. -/
theorem scalarized_seed_family_card_le
    {Seed : Type*} {K I : Type} [Field K] [Fintype I]
    [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144)
    (selected : Finset Seed) (scalar : Seed→Polynomial K)
    (hscalar : Set.InjOn scalar (↑selected : Set Seed))
    (hdegree : ∀ s∈selected,(scalar s).natDegree≤133221)
    (hagreement : ∀ s∈selected,180413≤
      (Finset.univ.filter fun i =>
        (scalar s).eval (nodes i)=received i).card) :
    selected.card≤250960796897672558 := by
  have hcard : (selected.image scalar).card=selected.card :=
    Finset.card_image_of_injOn hscalar
  rw [← hcard]
  apply scalar_finite_list_card_le nodes received hinj hI
  · intro P hP
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hP
    exact hdegree s hs
  · intro P hP
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hP
    exact hagreement s hs

theorem scalarized_seed_family_card_lt_retained
    {Seed : Type*} {K I : Type} [Field K] [Fintype I]
    [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144)
    (selected : Finset Seed) (scalar : Seed→Polynomial K)
    (hscalar : Set.InjOn scalar (↑selected : Set Seed))
    (hdegree : ∀ s∈selected,(scalar s).natDegree≤133221)
    (hagreement : ∀ s∈selected,180413≤
      (Finset.univ.filter fun i =>
        (scalar s).eval (nodes i)=received i).card) :
    selected.card<253511670984674103 := by
  exact (scalarized_seed_family_card_le nodes received hinj hI selected
    scalar hscalar hdegree hagreement).trans_lt (by norm_num)

/-- A selected family reaching the retained threshold cannot have scalar
degree at most 133221. -/
theorem scalarized_large_family_degree_obstruction
    {Seed : Type*} {K I : Type} [Field K] [Fintype I]
    [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144)
    (selected : Finset Seed) (scalar : Seed→Polynomial K)
    (hscalar : Set.InjOn scalar (↑selected : Set Seed))
    (W : Nat) (hdegree : ∀ s∈selected,(scalar s).natDegree≤W)
    (hagreement : ∀ s∈selected,180413≤
      (Finset.univ.filter fun i =>
        (scalar s).eval (nodes i)=received i).card)
    (hlarge : 253511670984674103≤selected.card) : 133222≤W := by
  by_contra hnot
  have hW : W≤133221 := by omega
  have hcount := scalarized_seed_family_card_lt_retained nodes received
    hinj hI selected scalar hscalar
    (fun s hs => (hdegree s hs).trans hW) hagreement
  omega

end
end ProximityPrize.SubmissionLower.WeightedScalarListW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedScalarListW1332216900.scalar_finite_list_card_le
#print axioms ProximityPrize.SubmissionLower.WeightedScalarListW1332216900.scalar_finite_list_card_lt_retained
#print axioms ProximityPrize.SubmissionLower.WeightedScalarListW1332216900.scalarized_seed_family_card_le
#print axioms ProximityPrize.SubmissionLower.WeightedScalarListW1332216900.scalarized_large_family_degree_obstruction
