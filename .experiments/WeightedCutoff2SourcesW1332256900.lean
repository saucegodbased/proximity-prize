import WeightedCutoff2TargetW1332256900
import WeightedCutoff2ColumnsW1332256900
import WeightedCutoff2BandsW1332256900
import WeightedPolynomialContactKernel6900
import WeightedSourcePowerEscape6900

/-! Actual primary/helper polynomial sources on any cutoff-two node type. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedQuadricContactTarget6900
open WeightedSourceIndex6900
open WeightedSourceKernel6900
open WeightedSourceBoxQuotient6900
open WeightedSourceColumnBands6900
open WeightedPolynomialContactKernel6900
open WeightedSourcePowerEscape6900
open WeightedStageFibreBoundProbe6900
open WeightedActualProductBandGate6900
open WeightedCutoff2TargetW1332256900
open WeightedCutoff2ColumnsW1332256900
open WeightedCutoff2BandsW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
noncomputable section

variable (K : Type*) [Field K]

def primaryPolynomialKernel (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) : Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 546 98505498 133225 61 (by norm_num) nodes values

def helperPolynomialKernel (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) : Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 11810 2130677530 133225 1312
    (by norm_num) nodes values

theorem primaryPolynomialKernel_le_box (I : Type*) [Fintype I]
    (htwo : (2:K)≠0) (nodes values : I→K) :
    primaryPolynomialKernel K I htwo nodes values≤
      weightedCoefficientBox K 98505498 133225 244 :=
  polynomialKernel_le_box K I htwo 546 98505498 133225 61
    (by norm_num) nodes values

theorem helperPolynomialKernel_le_box (I : Type*) [Fintype I]
    (htwo : (2:K)≠0) (nodes values : I→K) :
    helperPolynomialKernel K I htwo nodes values≤
      weightedCoefficientBox K 2130677530 133225 5248 :=
  polynomialKernel_le_box K I htwo 11810 2130677530 133225 1312
    (by norm_num) nodes values

theorem primaryPolynomialKernel_dimension (I : Type*) [Fintype I]
    (htwo : (2:K)≠0) (nodes values : I→K)
    (hn : Fintype.card I≤262142) :
    630889495≤Module.finrank K
      (primaryPolynomialKernel K I htwo nodes values) := by
  have hr := primary_totalTarget_rank_le K htwo
  have hg := globalKernel_finrank_lower K I htwo 546 98505498 133225 61
    (by norm_num) nodes values
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at hg
  have hproduct : Fintype.card I*
      Module.finrank K (totalTarget K 546 739 61)≤
        262142*1477453392 := Nat.mul_le_mul hn hr
  have hsource := primary_columns_lower
  have hbudget :
      630889495≤columns 98505498 133225 244-
        Fintype.card I*Module.finrank K (totalTarget K 546 739 61) := by
    omega
  unfold primaryPolynomialKernel
  rw [polynomialKernel_finrank]
  exact hbudget.trans hg

theorem helperPolynomialKernel_dimension (I : Type*) [Fintype I]
    (htwo : (2:K)≠0) (nodes values : I→K)
    (hn : Fintype.card I≤262142) :
    133965718104546337≤Module.finrank K
      (helperPolynomialKernel K I htwo nodes values) := by
  have hr := helper_totalTarget_rank_le K htwo
  have hg := globalKernel_finrank_lower K I htwo 11810 2130677530 133225
    1312 (by norm_num) nodes values
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at hg
  have hproduct : Fintype.card I*
      Module.finrank K (totalTarget K 11810 15993 1312)≤
        262142*314478446061020 := Nat.mul_le_mul hn hr
  have hsource := helper_columns_lower
  have hbudget :
      133965718104546337≤columns 2130677530 133225 5248-
        Fintype.card I*Module.finrank K
          (totalTarget K 11810 15993 1312) := by
    omega
  unfold helperPolynomialKernel
  rw [polynomialKernel_finrank]
  exact hbudget.trans hg

theorem primary_source_exists (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262142) :
    ∃ Q : Poly4 K,Q≠0 ∧
      Q∈weightedCoefficientBox K 98505498 133225 244 ∧
      Q∈globalOrder2CoefficientBox K 98505498 133225 739 244 122 ∧
      ∀ i:I,contactTruncation K 546
        (localSubstitution K (nodes i) (values i) Q)=0 := by
  have hr := primary_totalTarget_rank_le K htwo
  have hgate : Fintype.card I*Module.finrank K (totalTarget K 546 739 61)<
      columns 98505498 133225 244 := by
    have hp := Nat.mul_le_mul hn hr
    have hc := primary_columns_lower
    omega
  have h := exists_nonzero_polynomial_in_box K I htwo 546 98505498
    133225 61 (by norm_num) nodes values hgate
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at h
  exact h

theorem helper_source_exists (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262142) :
    ∃ Q : Poly4 K,Q≠0 ∧
      Q∈weightedCoefficientBox K 2130677530 133225 5248 ∧
      Q∈globalOrder2CoefficientBox K 2130677530 133225 15993 5248 2624 ∧
      ∀ i:I,contactTruncation K 11810
        (localSubstitution K (nodes i) (values i) Q)=0 := by
  have hr := helper_totalTarget_rank_le K htwo
  have hgate : Fintype.card I*
      Module.finrank K (totalTarget K 11810 15993 1312)<
        columns 2130677530 133225 5248 := by
    have hp := Nat.mul_le_mul hn hr
    have hc := helper_columns_lower
    omega
  have h := exists_nonzero_polynomial_in_box K I htwo 11810 2130677530
    133225 1312 (by norm_num) nodes values hgate
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at h
  exact h

theorem heavy_product_escape (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262142)
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P)
    (hheavy : 212≤jetDegree P ∨ 56≤derivativeDegree P) :
    ∃ (j : Nat) (G : Poly4 K),
      j≤2624 ∧ G≠0 ∧ ¬P∣G ∧
      P^j*G∈helperPolynomialKernel K I htwo nodes values ∧
      G∈weightedCoefficientBox K
        (2130677530-j*mainDegree 133225 P-j*47190) 133225
        (5248-j*derivativeDegree P) ∧
      P^j*G∈weightedCoefficientBox K (2130677530-j*47190) 133225 5248 ∧
      (∀ i:I,contactTruncation K 11810
        (localSubstitution K (nodes i) (values i) (P^j*G))=0) ∧
      P^j*G≠0 ∧ j*mainDegree 133225 P<2130677530 ∧
      j*derivativeDegree P≤5248 := by
  let V := helperPolynomialKernel K I htwo nodes values
  have hV : V≤weightedCoefficientBox K 2130677530 133225 5248 :=
    helperPolynomialKernel_le_box K I htwo nodes values
  have hbudget :
      (∑ j ∈ Finset.range 2624,
        stageBand 2130677530 133225 5248 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j)<Module.finrank K V := by
    have hb := (expensive_product_band_lt_kernel P hP hrho 2624 hheavy).trans_le
      (helperPolynomialKernel_dimension K I htwo nodes values hn)
    exact (congrArg (fun x : Nat => x<Module.finrank K V)
      (helperProductBandSum_eq P 2624)).mp hb
  have hterminal : 5248<(2624+1)*derivativeDegree P := by omega
  obtain ⟨j,G,hj,hG,hOriginal,hQuotient,hnd,hmain,hder⟩ :=
    exists_low_power_quotient V P 2130677530 133225 5248 47190 2624
      (by norm_num) hV hP hbudget (Or.inr hterminal)
  have hstage : G∈powerStage V P 2130677530 133225 5248 47190 j :=
    ⟨hOriginal,hQuotient⟩
  have htight := stage_original_mem_tightened V P G 2130677530 133225
    5248 47190 j hV hP hG hstage
  have hcontact := polynomialKernel_contact K I htwo 11810 2130677530
    133225 1312 (by norm_num) nodes values hOriginal
  exact ⟨j,G,hj,hG,hnd,hOriginal,hQuotient,htight,hcontact,
    mul_ne_zero (pow_ne_zero j hP) hG,hmain,hder⟩

end
end ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900.primaryPolynomialKernel_dimension
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900.helperPolynomialKernel_dimension
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900.primary_source_exists
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900.helper_source_exists
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2SourcesW1332256900.heavy_product_escape
