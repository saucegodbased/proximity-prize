import WeightedIdentityCoreTargetW1332256900
import WeightedPrimary550ColumnsW1332266900

/-! End-to-end reconstructed-kernel receipt for the hard W=133226 primary. -/
namespace ProximityPrize.SubmissionLower.WeightedPrimary550KernelW1332266900

open Order2SourceBasisScaffold
open WeightedQuadricContactTarget6900
open WeightedSourceIndex6900 WeightedSourceKernel6900
open WeightedPolynomialContactKernel6900
open WeightedIdentityCoreTargetW1332256900
open WeightedPrimary550ColumnsW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 2400
noncomputable section

variable (K : Type*) [Field K]

/-- Actual reconstructed kernel at `(m,B,W,k)=(550,99227150,133226,61)`. -/
def primaryPolynomialKernel
    (I : Type*) [Fintype I] (htwo : (2:K)≠0) (nodes values : I→K) :
    Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 550 99227150 133226 61 (by norm_num) nodes values

/-- Conservative dimension headroom at 262144 nodes. -/
theorem primaryPolynomialKernel_dimension
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    1258448670≤Module.finrank K (primaryPolynomialKernel K I htwo nodes values) := by
  have hr := helper_totalTarget_rank_le K htwo
  have hg := globalKernel_finrank_lower K I htwo 550 99227150 133226 61
    (by norm_num) nodes values
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at hg
  have hproduct : Fintype.card I*Module.finrank K (totalTarget K 550 744 61)≤
      262144*1503271269 := Nat.mul_le_mul hn hr
  have hsource := helper_columns_lower
  have hbudget :
      1258448670≤columns 99227150 133226 244-
        Fintype.card I*Module.finrank K (totalTarget K 550 744 61) := by omega
  unfold primaryPolynomialKernel
  rw [polynomialKernel_finrank]
  exact hbudget.trans hg

/-- A genuine nonzero primary in both the weighted source box and exact
nested global box, with order-550 contact at every one of at most 262144
nodes. -/
theorem primary_source_exists
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    ∃ Q : Poly4 K, Q≠0 ∧
      Q∈weightedCoefficientBox K 99227150 133226 244 ∧
      Q∈globalOrder2CoefficientBox K 99227150 133226 744 244 122 ∧
      ∀ i:I, contactTruncation K 550
        (localSubstitution K (nodes i) (values i) Q)=0 := by
  have hr := helper_totalTarget_rank_le K htwo
  have hgate : Fintype.card I*Module.finrank K (totalTarget K 550 744 61)<
      columns 99227150 133226 244 := by
    have hp := Nat.mul_le_mul hn hr
    have hc := helper_columns_lower
    norm_num only [Nat.reduceMul] at hp
    omega
  have h := exists_nonzero_polynomial_in_box K I htwo 550 99227150
    133226 61 (by norm_num) nodes values hgate
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at h
  exact h

end
end ProximityPrize.SubmissionLower.WeightedPrimary550KernelW1332266900

#print axioms ProximityPrize.SubmissionLower.WeightedPrimary550KernelW1332266900.primaryPolynomialKernel_dimension
#print axioms ProximityPrize.SubmissionLower.WeightedPrimary550KernelW1332266900.primary_source_exists
