import WeightedCutoff2PrimaryAllFactorReductionW1332256900
import WeightedCutoff2ActiveBatchCountW1332256900

/-! Complete scalar-list bound on any identity core of cardinality at most `262142`. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2ScalarListW1332256900

open WeightedCutoff2PrimaryAllFactorReductionW1332256900
open WeightedCutoff2RepresentativeLedgerW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem scalar_finite_list_card_le
    {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I≤n) (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,a≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card) :
    Gamma.card≤263611056734952886 := by
  classical
  by_cases hnonempty : Gamma.Nonempty
  · obtain ⟨P,hP⟩ := hnonempty
    have hAn : a≤Fintype.card I := calc
      a ≤ (Finset.univ.filter fun i => P.eval (nodes i)=received i).card :=
        hagreement P hP
      _ ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = Fintype.card I := Finset.card_univ
    obtain ⟨Q,hQ,hweighted,hbox,hsolution,hcleanup⟩ :=
      exists_primary_source_and_nonactive_bound nodes received hinj hI hAn
        Gamma hdegree hagreement
    obtain ⟨hT,hRT,hJet⟩ := primary_source_weighted_caps Q hbox
    have hTdegree := (primary_source_coordinate_caps Q hbox).2.2
    have hactive :=
      WeightedCutoff2ActiveBatchCountW1332256900.activeTRegular_card_le
        Q hQ hT hTdegree hRT hJet Gamma nodes received hinj hI hAn
        hdegree hagreement
    rw [active_caps_exact.1,active_caps_exact.2] at hactive
    omega
  · have : Gamma=∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [this]

theorem scalar_finite_list_card_lt_retained
    {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I≤n) (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,a≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card) :
    Gamma.card<retained := by
  exact (scalar_finite_list_card_le nodes received hinj hI Gamma
    hdegree hagreement).trans_lt (by norm_num [retained])

theorem scalarized_seed_family_card_le
    {Seed : Type*} {K I : Type} [Field K] [Fintype I]
    [CharP K 2130706433]
    (nodes received : I→K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I≤n)
    (selected : Finset Seed) (scalar : Seed→Polynomial K)
    (hscalar : Set.InjOn scalar (↑selected : Set Seed))
    (hdegree : ∀ s∈selected,(scalar s).natDegree≤w)
    (hagreement : ∀ s∈selected,a≤
      (Finset.univ.filter fun i =>
        (scalar s).eval (nodes i)=received i).card) :
    selected.card≤263611056734952886 := by
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
    (hI : Fintype.card I≤n)
    (selected : Finset Seed) (scalar : Seed→Polynomial K)
    (hscalar : Set.InjOn scalar (↑selected : Set Seed))
    (hdegree : ∀ s∈selected,(scalar s).natDegree≤w)
    (hagreement : ∀ s∈selected,a≤
      (Finset.univ.filter fun i =>
        (scalar s).eval (nodes i)=received i).card) :
    selected.card<retained := by
  exact (scalarized_seed_family_card_le nodes received hinj hI selected
    scalar hscalar hdegree hagreement).trans_lt (by norm_num [retained])

end
end ProximityPrize.SubmissionLower.WeightedCutoff2ScalarListW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ScalarListW1332256900.scalar_finite_list_card_le
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ScalarListW1332256900.scalarized_seed_family_card_lt_retained
