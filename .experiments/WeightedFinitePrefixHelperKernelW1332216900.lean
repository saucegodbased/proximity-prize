import WeightedFinitePrefixHelperTargetW1332216900
import WeightedFinitePrefixHelperColumnsW1332216900

/-! End-to-end reconstructed helper kernel at the W=133221 parameters. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperKernelW1332216900

open Order2SourceBasisScaffold
open WeightedQuadricContactTarget6900
open WeightedSourceIndex6900 WeightedSourceKernel6900
open WeightedPolynomialContactKernel6900
open WeightedFinitePrefixHelperTargetW1332216900
open WeightedFinitePrefixHelperColumnsW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 2200
noncomputable section

variable (K : Type*) [Field K]

/-- The actual reconstructed helper kernel at
`(m,B,W,k)=(11268,2032893684,133221,1252)`. -/
def helperPolynomialKernel
    (I : Type*) [Fintype I] (htwo : (2:K)≠0) (nodes values : I→K) :
    Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 11268 2032893684 133221 1252
    (by norm_num) nodes values

/-- Exact arithmetic margin:
`68450284539644380157 - 262144*260685624246315`.-/
theorem helperPolynomialKernel_dimension
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    113112257218380797≤Module.finrank K
      (helperPolynomialKernel K I htwo nodes values) := by
  have hr := helper_totalTarget_rank_le K htwo
  have hg := globalKernel_finrank_lower K I htwo 11268 2032893684 133221
    1252 (by norm_num) nodes values
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at hg
  have hproduct : Fintype.card I*
      Module.finrank K (totalTarget K 11268 15259 1252)≤
        262144*260685624246315 := Nat.mul_le_mul hn hr
  have hsource := helper_columns_lower
  have hbudget :
      113112257218380797≤columns 2032893684 133221 5008-
        Fintype.card I*Module.finrank K (totalTarget K 11268 15259 1252) := by
    omega
  unfold helperPolynomialKernel
  rw [polynomialKernel_finrank]
  exact hbudget.trans hg

/-- Nonzero helper source in the literal weighted/global boxes with order
`11268` contact at every one of at most `262144` nodes. -/
theorem helper_source_exists
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    ∃ Q : Poly4 K,Q≠0 ∧
      Q∈weightedCoefficientBox K 2032893684 133221 5008 ∧
      Q∈globalOrder2CoefficientBox K 2032893684 133221 15259 5008 2504 ∧
      ∀ i:I,contactTruncation K 11268
        (localSubstitution K (nodes i) (values i) Q)=0 := by
  have hr := helper_totalTarget_rank_le K htwo
  have hgate : Fintype.card I*Module.finrank K
      (totalTarget K 11268 15259 1252)<
        columns 2032893684 133221 5008 := by
    have hp := Nat.mul_le_mul hn hr
    have hc := helper_columns_lower
    norm_num only [Nat.reduceMul] at hp
    omega
  have h := exists_nonzero_polynomial_in_box K I htwo 11268 2032893684
    133221 1252 (by norm_num) nodes values hgate
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at h
  exact h

end
end ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperKernelW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperKernelW1332216900.helperPolynomialKernel_dimension
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperKernelW1332216900.helper_source_exists
