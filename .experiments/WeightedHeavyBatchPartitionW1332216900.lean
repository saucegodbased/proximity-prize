import WeightedActualProductBandGate6900

/-! Certificate-preserving strict-subset batch descent. A helper is attached
to each exited factor, while the final product has small actual degrees.
All aggregate degree charges are taken from the original factor set once. -/

namespace ProximityPrize.SubmissionLower.WeightedHeavyBatchPartitionW1332216900

open scoped BigOperators
open Order2SourceBasisScaffold WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

section Generic
variable {ι : Type*} [DecidableEq ι]

/-- Witness-preserving refinement of the accepted strict-route induction.
Each recursive call removes an actually certified member. -/
theorem exists_certified_terminal_subset (ambient : Finset ι)
    (terminal : Finset ι → Prop) (certificate : ι → Prop)
    (hstep : ∀ T, T⊆ambient → ¬terminal T → ∃ i∈T, certificate i) :
    ∃ rest, rest⊆ambient ∧ terminal rest ∧
      ∀ i∈ambient\rest, certificate i := by
  classical
  have aux : ∀ T : Finset ι, T⊆ambient →
      ∃ rest, rest⊆T ∧ terminal rest ∧ ∀ i∈T\rest, certificate i := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hT
      by_cases ht : terminal T
      · exact ⟨T,le_rfl,ht,by simp⟩
      · obtain ⟨i,hi,hcert⟩ := hstep T hT ht
        obtain ⟨rest,hrest,hterminal,hcerts⟩ :=
          ih (T.erase i) (Finset.erase_ssubset hi) ((Finset.erase_subset i T).trans hT)
        refine ⟨rest,hrest.trans (Finset.erase_subset i T),hterminal,?_⟩
        intro a ha
        obtain ⟨haT,haR⟩ := Finset.mem_sdiff.mp ha
        by_cases hai : a=i
        · simpa only [hai] using hcert
        · exact hcerts a (Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨hai,haT⟩,haR⟩)
  exact aux ambient le_rfl

/-- Exact accounting on the final partition, with no repeated-stage charge. -/
theorem sum_exited_add_rest (ambient rest : Finset ι) (hrest : rest⊆ambient)
    (weight : ι → Nat) :
    (∑ i∈ambient\rest, weight i)+(∑ i∈rest, weight i)=
      ∑ i∈ambient, weight i := Finset.sum_sdiff hrest

/-- Direct reuse of the accepted strict-route count engine. The helper
charge is additive over the ORIGINAL set, even when each exit uses a
different helper witness. The terminal cap counts original factor families,
not the regular locus of a potentially colliding product. -/
theorem sum_count_le_terminal_add_original_charge {α : Type} [DecidableEq α]
    (ambient : Finset α)
    (terminal : Finset α → Prop) (certificate : α → Prop)
    (count charge : α → Nat) (terminalCap : Nat)
    (hstep : ∀ T, T⊆ambient → ¬terminal T → ∃ i∈T, certificate i)
    (hterminal : ∀ T, T⊆ambient → terminal T →
      (∑ i∈T, count i)≤terminalCap)
    (hcharge : ∀ i∈ambient, certificate i → count i≤charge i) :
    (∑ i∈ambient, count i)≤(∑ i∈ambient, charge i)+terminalCap := by
  classical
  apply LocatorBatchProductRoute.sum_count_le_charge_add_defect_of_strict_routes
    count charge (fun T => ¬terminal T) ambient terminalCap
  · intro T hT hn
    have ht : terminal T := Classical.not_not.mp hn
    exact (hterminal T hT ht).trans (Nat.le_add_left _ _)
  · intro T hT ht
    obtain ⟨i,hi,hcert⟩ := hstep T hT ht
    refine ⟨T.erase i,Finset.erase_ssubset hi,?_⟩
    rw [Finset.sdiff_erase_self hi]
    simpa only [Finset.sum_singleton] using hcharge i (hT hi) hcert

end Generic

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

def CheapProduct (factor : ι → Poly4 K) (T : Finset ι) : Prop :=
  jetDegree (∏ i∈T, factor i)≤207 ∧ derivativeDegree (∏ i∈T, factor i)≤54

def HeavyProduct (factor : ι → Poly4 K) (T : Finset ι) : Prop :=
  208≤jetDegree (∏ i∈T, factor i) ∨ 55≤derivativeDegree (∏ i∈T, factor i)

omit [DecidableEq ι] in
theorem cheapProduct_empty (factor : ι → Poly4 K) : CheapProduct factor ∅ := by
  simp [CheapProduct,jetDegree,derivativeDegree,MvPolynomial.weightedTotalDegree]

omit [DecidableEq ι] in
theorem heavyProduct_iff_not_cheap (factor : ι → Poly4 K) (T : Finset ι) :
    HeavyProduct factor T ↔ ¬CheapProduct factor T := by
  unfold HeavyProduct CheapProduct
  omega

omit [DecidableEq ι] in
theorem heavyProduct_nonempty (factor : ι → Poly4 K) (T : Finset ι)
    (hheavy : HeavyProduct factor T) : T.Nonempty := by
  by_contra hn
  have hT : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hnot := (heavyProduct_iff_not_cheap factor T).mp hheavy
  rw [hT] at hnot
  exact hnot (cheapProduct_empty factor)

/-- Actual-degree terminal partition. `certificate` may contain a different
proper helper and its semantic/counting evidence for each original factor.
The only algebraic step premise concerns the current remaining subset. -/
theorem heavy_products_partition (factor : ι → Poly4 K) (ambient : Finset ι)
    (certificate : ι → Prop)
    (hstep : ∀ T, T⊆ambient → T.Nonempty → HeavyProduct factor T →
      ∃ i∈T, certificate i) :
    ∃ exited rest : Finset ι,
      rest⊆ambient ∧ exited=ambient\rest ∧ Disjoint exited rest ∧
      exited∪rest=ambient ∧ CheapProduct factor rest ∧
      ∀ i∈exited, certificate i := by
  obtain ⟨rest,hrest,hcheap,hcert⟩ := exists_certified_terminal_subset ambient
    (CheapProduct factor) certificate (fun T hT hnot =>
      hstep T hT (heavyProduct_nonempty factor T
        ((heavyProduct_iff_not_cheap factor T).mpr hnot))
        ((heavyProduct_iff_not_cheap factor T).mpr hnot))
  refine ⟨ambient\rest,rest,hrest,rfl,?_,?_,hcheap,hcert⟩
  · exact Finset.disjoint_left.mpr (fun i hi hr => (Finset.mem_sdiff.mp hi).2 hr)
  · rw [Finset.union_comm]
    exact Finset.union_sdiff_of_subset hrest

/-- Exact product-degree additivity is reused from the accepted proof. It
turns the small product caps into small sums of ORIGINAL factor degrees. -/
theorem cheapProduct_iff_sum_degrees (factor : ι → Poly4 K) (T : Finset ι)
    (hfactor : ∀ i∈T, factor i≠0) :
    CheapProduct factor T ↔
      (∑ i∈T, jetDegree (factor i))≤207 ∧
      (∑ i∈T, derivativeDegree (factor i))≤54 := by
  have hj := RCN071.weightedTotalDegree_prod_eq jetWeights T factor hfactor
  have hd := RCN071.weightedTotalDegree_prod_eq derivativeWeights T factor hfactor
  change MvPolynomial.weightedTotalDegree jetWeights (∏ i∈T, factor i)≤207 ∧
      MvPolynomial.weightedTotalDegree derivativeWeights (∏ i∈T, factor i)≤54 ↔ _
  rw [hj,hd]
  rfl

/-- Both sides of the partition share one original weighted-degree budget.
This applies separately to every flag coordinate or additive source charge. -/
theorem original_factor_weight_budget (factor : ι → Poly4 K)
    (ambient rest : Finset ι) (hrest : rest⊆ambient)
    (source : Poly4 K) (hsource : source≠0)
    (hprod : (∏ i∈ambient, factor i)∣source) (weights : Fin 4 → Nat) :
    (∑ i∈ambient\rest, MvPolynomial.weightedTotalDegree weights (factor i))+
      (∑ i∈rest, MvPolynomial.weightedTotalDegree weights (factor i))≤
        MvPolynomial.weightedTotalDegree weights source := by
  rw [sum_exited_add_rest ambient rest hrest]
  exact RCN071.sum_weightedTotalDegree_le_of_prod_dvd weights ambient factor source
    hsource hprod

/-- The count corollary specialized to the actual heavy-product split.
Its terminal input is explicitly a sum over the original remaining factors. -/
theorem heavy_products_count_le {α : Type} [DecidableEq α]
    (factor : α → Poly4 K) (ambient : Finset α)
    (certificate : α → Prop) (count charge : α → Nat) (terminalCap : Nat)
    (hstep : ∀ T, T⊆ambient → T.Nonempty → HeavyProduct factor T →
      ∃ i∈T, certificate i)
    (hterminal : ∀ T, T⊆ambient → CheapProduct factor T →
      (∑ i∈T, count i)≤terminalCap)
    (hcharge : ∀ i∈ambient, certificate i → count i≤charge i) :
    (∑ i∈ambient, count i)≤(∑ i∈ambient, charge i)+terminalCap := by
  apply sum_count_le_terminal_add_original_charge ambient (CheapProduct factor)
    certificate count charge terminalCap
  · intro T hT hnot
    have hh := (heavyProduct_iff_not_cheap factor T).mpr hnot
    exact hstep T hT (heavyProduct_nonempty factor T hh) hh
  · exact hterminal
  · exact hcharge

#print axioms exists_certified_terminal_subset
#print axioms heavy_products_partition
#print axioms cheapProduct_iff_sum_degrees
#print axioms original_factor_weight_budget
#print axioms heavy_products_count_le

end
end ProximityPrize.SubmissionLower.WeightedHeavyBatchPartitionW1332216900
