import WeightedFinitePrefixPrimaryTargetW1332216900
import WeightedFinitePrefixPrimaryColumnsW1332216900

/-! End-to-end semantic source receipt for the W=133221 non-`9*k` primary.
The theorem reaches the actual reconstructed polynomial kernel and the actual
weighted/global coefficient boxes. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryKernelW1332216900

open Order2SourceBasisScaffold
open WeightedQuadricContactTarget6900
open WeightedSourceIndex6900 WeightedSourceKernel6900
open WeightedPolynomialContactKernel6900
open WeightedFinitePrefixPrimaryTargetW1332216900
open WeightedFinitePrefixPrimaryColumnsW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section

variable (K : Type*) [Field K]

/-- Actual reconstructed kernel at `(m,B,W,k)=(533,96160129,133221,59)`. -/
def primaryPolynomialKernel
    (I : Type*) [Fintype I] (htwo : (2:K)≠0) (nodes values : I→K) :
    Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 533 96160129 133221 59 (by norm_num) nodes values

/-- The exact arithmetic margin is
`346699946431821 - 262144*1322554236 = 288789837`. -/
theorem primaryPolynomialKernel_dimension
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    288789837≤Module.finrank K (primaryPolynomialKernel K I htwo nodes values) := by
  have hr := primary_totalTarget_rank_le K htwo
  have hg := globalKernel_finrank_lower K I htwo 533 96160129 133221 59
    (by norm_num) nodes values
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at hg
  have hproduct : Fintype.card I*Module.finrank K (totalTarget K 533 721 59)≤
      262144*1322554236 := Nat.mul_le_mul hn hr
  have hsource := primary_columns_lower
  have hbudget :
      288789837≤columns 96160129 133221 236-
        Fintype.card I*Module.finrank K (totalTarget K 533 721 59) := by omega
  unfold primaryPolynomialKernel
  rw [polynomialKernel_finrank]
  exact hbudget.trans hg

/-- A genuine nonzero polynomial in the weighted box and the exact legacy
global box, with order-533 contact at every one of at most 262144 nodes. -/
theorem primary_source_exists
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    ∃ Q : Poly4 K,Q≠0 ∧
      Q∈weightedCoefficientBox K 96160129 133221 236 ∧
      Q∈globalOrder2CoefficientBox K 96160129 133221 721 236 118 ∧
      ∀ i:I,contactTruncation K 533
        (localSubstitution K (nodes i) (values i) Q)=0 := by
  have hr := primary_totalTarget_rank_le K htwo
  have hgate : Fintype.card I*Module.finrank K (totalTarget K 533 721 59)<
      columns 96160129 133221 236 := by
    have hp := Nat.mul_le_mul hn hr
    have hc := primary_columns_lower
    norm_num only [Nat.reduceMul] at hp
    omega
  have h := exists_nonzero_polynomial_in_box K I htwo 533 96160129
    133221 59 (by norm_num) nodes values hgate
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at h
  exact h

end
end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryKernelW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryKernelW1332216900.primaryPolynomialKernel_dimension
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryKernelW1332216900.primary_source_exists
