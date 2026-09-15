import WeightedIdentityCoupledFlagAggregationW1332256900
import WeightedFactorFlagBudgetW1332246900
import WeightedHeavyBatchPartitionW1332246900

/-!
# Actual factor-partition adapter for the coupled W=133225 budget

This file derives the six cumulative premises of
`coupled_armA_counts_scaled` from one ambient positive-factor product and an
arm-A terminal remainder.  In particular, the exited and remaining factors
are never assigned independent copies of the primary source flag.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900

open scoped Classical BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135
open Order2ValueYCapAllFactorScaffold Order2FlagTwoCutAdapter
open Order2SourceBasisScaffold WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900 WeightedBatchFactorChoice6900
open WeightedFactorFlagBudgetW1332246900
open WeightedHeavyBatchPartitionW1332246900
open WeightedIdentityCoupledFlagAggregationW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

noncomputable section

variable {K : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

namespace R
abbrev n := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n
abbrev a := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a
abbrev v := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v
abbrev primaryFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryFlag
abbrev armAFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag
abbrev armAExitFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag
abbrev armAAgreement :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement
abbrev armBFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBFlag
abbrev armBExitFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBExitFlag
abbrev armBAgreement :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBAgreement
abbrev jointHelperFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag
abbrev primaryAgreement :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement
abbrev jointCommonNumerator :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator
end R

def factorFlag (F : MvPolynomial (Fin 4) K) : FlagDegree :=
  exactFlag (rtySource F)

/-- Subtype sums over a strict partition are the original ambient sum. -/
theorem sum_sdiff_subtype_add_rest {α : Type*} [DecidableEq α]
    (ambient rest : Finset α) (hrest : rest⊆ambient) (f : α→Nat) :
    (∑ i : ↥(ambient\rest),f i.1)+(∑ i : ↥rest,f i.1)=
      ∑ i : ↥ambient,f i.1 := by
  rw [Finset.sum_coe_sort,Finset.sum_coe_sort,Finset.sum_coe_sort]
  exact sum_exited_add_rest ambient rest hrest f

section LTerminal

variable {ι : Type*} [DecidableEq ι]

/-- The nonrectangular terminal which keeps the difficult corner out. -/
def LTerminal (factor : ι→MvPolynomial (Fin 4) K) (T : Finset ι) : Prop :=
  (jetDegree (∏ i∈T,factor i)≤211 ∧
      derivativeDegree (∏ i∈T,factor i)≤55) ∨
    (jetDegree (∏ i∈T,factor i)≤212 ∧
      derivativeDegree (∏ i∈T,factor i)≤54)

/-- Exactly the three helper-producing regions: high jet, high derivative,
or the excluded `(212,55)` corner. -/
def LHeavy (factor : ι→MvPolynomial (Fin 4) K) (T : Finset ι) : Prop :=
  213≤jetDegree (∏ i∈T,factor i) ∨
    56≤derivativeDegree (∏ i∈T,factor i) ∨
    (212≤jetDegree (∏ i∈T,factor i) ∧
      55≤derivativeDegree (∏ i∈T,factor i))

theorem lheavy_iff_not_lterminal (factor : ι→MvPolynomial (Fin 4) K)
    (T : Finset ι) : LHeavy factor T ↔ ¬LTerminal factor T := by
  unfold LHeavy LTerminal
  omega

theorem lheavy_nonempty (factor : ι→MvPolynomial (Fin 4) K) (T : Finset ι)
    (h : LHeavy factor T) : T.Nonempty := by
  by_contra hn
  have hT : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hnot := (lheavy_iff_not_lterminal factor T).mp h
  rw [hT] at hnot
  apply hnot
  left
  simp [jetDegree,derivativeDegree,MvPolynomial.weightedTotalDegree]

/-- Generic strict descent for the L-shaped terminal.  The corner is not a
terminal case, so a corner subset necessarily contributes a certified exit. -/
theorem lterminal_partition (factor : ι→MvPolynomial (Fin 4) K)
    (ambient : Finset ι) (certificate : ι→Prop)
    (hstep : ∀ T, T⊆ambient → T.Nonempty → LHeavy factor T →
      ∃ i∈T,certificate i) :
    ∃ exited rest : Finset ι,
      rest⊆ambient ∧ exited=ambient\rest ∧ Disjoint exited rest ∧
      exited∪rest=ambient ∧ LTerminal factor rest ∧
      ∀ i∈exited,certificate i := by
  obtain ⟨rest,hrest,hterminal,hcert⟩ :=
    exists_certified_terminal_subset ambient (LTerminal factor) certificate
      (fun T hT hnot =>
        hstep T hT (lheavy_nonempty factor T
          ((lheavy_iff_not_lterminal factor T).mpr hnot))
          ((lheavy_iff_not_lterminal factor T).mpr hnot))
  refine ⟨ambient\rest,rest,hrest,rfl,?_,?_,hterminal,hcert⟩
  · exact Finset.disjoint_left.mpr
      (fun i hi hr => (Finset.mem_sdiff.mp hi).2 hr)
  · rw [Finset.union_comm]
    exact Finset.union_sdiff_of_subset hrest

end LTerminal

/-- The exact six nested budgets needed by the coupled LP.  The first three
come from the one ambient product; the last three come from the arm-A
terminal product. -/
theorem armA_partition_six_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤211)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤55) :
    ((∑ F : ↥(ambient\rest),
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤740) ∧
    ((∑ F : ↥(ambient\rest),((factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤244) ∧
    ((∑ F : ↥(ambient\rest),(factorFlag F.1).all)+
      (∑ F : ↥rest,(factorFlag F.1).all)≤122) ∧
    ((∑ F : ↥rest,
      ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤211) ∧
    ((∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤55) ∧
    ((∑ F : ↥rest,(factorFlag F.1).all)≤27) := by
  have hambientBudget := exactFlag_cumulative_of_weight_bounds ambient Q hQ
    (positiveT_subset_product_dvd ambient Q hQ hambient) R.primaryFlag
    hQT hQRT hQJ
  let P : MvPolynomial (Fin 4) K := ∏ F∈rest,F
  have hirr : ∀ F∈rest,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hambient (hrest hF))).1
  have hP : P≠0 := product_ne_zero rest id hirr
  have hnested := derivative_nested_bounds P
  have hdiv : derivativeDegree P/2≤55/2 := Nat.div_le_div_right hrestD
  have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
    hnested.1.trans (by norm_num at hdiv ⊢; exact hdiv)
  have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤55 :=
    hnested.2.trans hrestD
  have hrestBudget := exactFlag_cumulative_of_weight_bounds rest P hP dvd_rfl
    R.armAFlag hPT hPRT hrestJ
  have splitS := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).all)
  have splitM := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).yz+(factorFlag F).all)
  have splitJ := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).zOnly+(factorFlag F).yz+(factorFlag F).all)
  refine ⟨splitJ.le.trans hambientBudget.2.2,splitM.le.trans hambientBudget.2.1,
    splitS.le.trans hambientBudget.1,hrestBudget.2.2,hrestBudget.2.1,
    hrestBudget.1⟩

/-- Count-facing mechanical seam.  Once strict descent supplies the per-exit
joint-helper inequalities and the old arm-A inequalities for the remainder,
the exact factor partition automatically supplies every coupled flag premise. -/
theorem armA_partition_counts_scaled
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤211)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤55)
    (count : MvPolynomial (Fin 4) K→Nat)
    (hexit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.jointHelperFlag
        R.primaryAgreement)
    (hcheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
      (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armAAgreement
        R.armAAgreement) :
    ((∑ F∈ambient\rest,count F)+(∑ F∈rest,count F))*(R.a-R.v)^2≤
      R.jointCommonNumerator R.armAFlag R.armAExitFlag R.armAAgreement := by
  obtain ⟨hJ,hM,hS,hrJ,hrM,hrS⟩ :=
    armA_partition_six_budgets Q hQ hQT hQRT hQJ ambient rest hambient
      hrest hrestJ hrestD
  have h := coupled_armA_counts_scaled
    (fun F : ↥(ambient\rest) => count F.1) (fun F : ↥rest => count F.1)
    (fun F : ↥(ambient\rest) => factorFlag F.1)
    (fun F : ↥rest => factorFlag F.1)
    hexit hcheap hJ hM hS hrJ hrM hrS
  simpa only [Finset.sum_coe_sort] using h

theorem armB_partition_six_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤212)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤54) :
    ((∑ F : ↥(ambient\rest),
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤740) ∧
    ((∑ F : ↥(ambient\rest),((factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤244) ∧
    ((∑ F : ↥(ambient\rest),(factorFlag F.1).all)+
      (∑ F : ↥rest,(factorFlag F.1).all)≤122) ∧
    ((∑ F : ↥rest,
      ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤212) ∧
    ((∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤54) ∧
    ((∑ F : ↥rest,(factorFlag F.1).all)≤27) := by
  have hambientBudget := exactFlag_cumulative_of_weight_bounds ambient Q hQ
    (positiveT_subset_product_dvd ambient Q hQ hambient) R.primaryFlag
    hQT hQRT hQJ
  let P : MvPolynomial (Fin 4) K := ∏ F∈rest,F
  have hirr : ∀ F∈rest,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hambient (hrest hF))).1
  have hP : P≠0 := product_ne_zero rest id hirr
  have hnested := derivative_nested_bounds P
  have hdiv : derivativeDegree P/2≤54/2 := Nat.div_le_div_right hrestD
  have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
    hnested.1.trans (by norm_num at hdiv ⊢; exact hdiv)
  have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤54 :=
    hnested.2.trans hrestD
  have hrestBudget := exactFlag_cumulative_of_weight_bounds rest P hP dvd_rfl
    R.armBFlag hPT hPRT hrestJ
  have splitS := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).all)
  have splitM := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).yz+(factorFlag F).all)
  have splitJ := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).zOnly+(factorFlag F).yz+(factorFlag F).all)
  refine ⟨splitJ.le.trans hambientBudget.2.2,splitM.le.trans hambientBudget.2.1,
    splitS.le.trans hambientBudget.1,hrestBudget.2.2,hrestBudget.2.1,
    hrestBudget.1⟩

theorem armB_partition_counts_scaled
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤212)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤54)
    (count : MvPolynomial (Fin 4) K→Nat)
    (hexit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.jointHelperFlag
        R.primaryAgreement)
    (hcheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
      (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armBAgreement
        R.armBAgreement) :
    ((∑ F∈ambient\rest,count F)+(∑ F∈rest,count F))*(R.a-R.v)^2≤
      R.jointCommonNumerator R.armBFlag R.armBExitFlag R.armBAgreement := by
  obtain ⟨hJ,hM,hS,hrJ,hrM,hrS⟩ :=
    armB_partition_six_budgets Q hQ hQT hQRT hQJ ambient rest hambient
      hrest hrestJ hrestD
  have h := coupled_armB_counts_scaled
    (fun F : ↥(ambient\rest) => count F.1) (fun F : ↥rest => count F.1)
    (fun F : ↥(ambient\rest) => factorFlag F.1)
    (fun F : ↥rest => factorFlag F.1)
    hexit hcheap hJ hM hS hrJ hrM hrS
  simpa only [Finset.sum_coe_sort] using h

theorem armB_jointNumerator_le_armA :
    R.jointCommonNumerator R.armBFlag R.armBExitFlag R.armBAgreement≤
      R.jointCommonNumerator R.armAFlag R.armAExitFlag R.armAAgreement := by
  norm_num [R.jointCommonNumerator,R.armAFlag,R.armAExitFlag,R.armAAgreement,
    R.armBFlag,R.armBExitFlag,R.armBAgreement,R.jointHelperFlag,
    R.primaryAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBExitFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,flagMixed]

/-- End-to-end abstract strict-descent seam.  Its only producer input is the
three-way L-heavy step; all flag sharing and both terminal branches are
discharged here. -/
theorem lterminal_partition_counts_scaled
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (ambient : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q)
    (certificate : MvPolynomial (Fin 4) K→Prop)
    (hstep : ∀ T, T⊆ambient → T.Nonempty → LHeavy id T →
      ∃ F∈T,certificate F)
    (count : MvPolynomial (Fin 4) K→Nat)
    (hexit : ∀ F∈ambient,certificate F → count F*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F) R.jointHelperFlag
        R.primaryAgreement)
    (hcheapA : ∀ T, T⊆ambient →
      jetDegree (∏ F∈T,F)≤211 → derivativeDegree (∏ F∈T,F)≤55 →
      ∀ F : ↥T,count F.1*(R.a-R.v)^2≤
        (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armAAgreement
          R.armAAgreement)
    (hcheapB : ∀ T, T⊆ambient →
      jetDegree (∏ F∈T,F)≤212 → derivativeDegree (∏ F∈T,F)≤54 →
      ∀ F : ↥T,count F.1*(R.a-R.v)^2≤
        (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armBAgreement
          R.armBAgreement) :
    (∑ F∈ambient,count F)*(R.a-R.v)^2≤
      R.jointCommonNumerator R.armAFlag R.armAExitFlag R.armAAgreement := by
  obtain ⟨exited,rest,hrest,hEx,hdisjoint,hunion,hterminal,hcert⟩ :=
    lterminal_partition id ambient certificate hstep
  subst exited
  have hExit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.jointHelperFlag
        R.primaryAgreement := by
    intro F
    exact hexit F.1 (Finset.mem_sdiff.mp F.2).1 (hcert F.1 F.2)
  have hsplit := sum_exited_add_rest ambient rest hrest count
  rw [← hsplit]
  rcases hterminal with hA | hB
  · exact armA_partition_counts_scaled Q hQ hQT hQRT hQJ ambient rest
      hambient hrest hA.1 hA.2 count hExit
      (hcheapA rest hrest hA.1 hA.2)
  · exact (armB_partition_counts_scaled Q hQ hQT hQRT hQJ ambient rest
      hambient hrest hB.1 hB.2 count hExit
      (hcheapB rest hrest hB.1 hB.2)).trans armB_jointNumerator_le_armA

end
end ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.armA_partition_six_budgets
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.armA_partition_counts_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.lterminal_partition
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.armB_partition_counts_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.lterminal_partition_counts_scaled
