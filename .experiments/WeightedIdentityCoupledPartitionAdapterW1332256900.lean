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

end
end ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.armA_partition_six_budgets
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledPartitionAdapterW1332256900.armA_partition_counts_scaled
