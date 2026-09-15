import WeightedIdentityCoreBandsW1332256900
import WeightedPolynomialContactKernel6900
import WeightedSourcePowerEscape6900

/-!
# Exact helper interface on the W=133225 identity-node core

The node type is arbitrary.  Its only numerical hypothesis is
`Fintype.card I ≤ 261851`, so this module applies directly to the subtype of
identity nodes supplied by `FixedLinearNodeSupportConcentration6900`.

The local target rank and source-column estimates are deliberately
conservative.  They leave a kernel of dimension at least `445782504611`,
which strictly dominates either live product-band profile.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityCoreHelperW1332256900

open Order2SourceBasisScaffold
open WeightedSourceIndex6900
open WeightedSourceSpace6900
open WeightedSourceBoxQuotient6900
open WeightedSourceKernel6900
open WeightedPolynomialContactKernel6900
open WeightedSourcePowerEscape6900
open WeightedQuadricContactTarget6900
open WeightedActualProductBandGate6900
open WeightedIdentityCoreTargetW1332256900
open WeightedIdentityCoreColumnsW1332256900
open WeightedIdentityCoreBandsW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
noncomputable section

variable (K : Type*) [Field K]

/-- The helper polynomial space, imposed only at the supplied identity
nodes.  The original agreement threshold does not occur in this definition:
it remains available in full for the downstream incidence argument. -/
def identityCoreHelperKernel (I : Type*) [Fintype I]
    (htwo : (2 : K)≠0) (nodes values : I→K) : Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 550 99227150 133225 61 (by norm_num) nodes values

theorem identityCoreHelperKernel_le_box (I : Type*) [Fintype I]
    (htwo : (2 : K)≠0) (nodes values : I→K) :
    identityCoreHelperKernel K I htwo nodes values ≤
      weightedCoefficientBox K 99227150 133225 244 := by
  exact polynomialKernel_le_box K I htwo 550 99227150 133225 61
    (by norm_num) nodes values

/-- The conservative dimension receipt at the sharp identity-core cutoff.
The literal estimates used here are

* columns `≥ 394078867563530`,
* local rank `≤ 1503271269`,
* node count `≤ 261851`.
-/
theorem identityCoreHelperKernel_finrank_lower (I : Type*) [Fintype I]
    (htwo : (2 : K)≠0) (nodes values : I→K)
    (hnodes : Fintype.card I≤261851) :
    445782504611 ≤
      Module.finrank K (identityCoreHelperKernel K I htwo nodes values) := by
  rw [identityCoreHelperKernel,polynomialKernel_finrank]
  have hrank := helper_totalTarget_rank_le K htwo
  have hrank' :
      Module.finrank K
        (totalTarget K 550 (99227150/(133225-2)) 61) ≤ 1503271269 := by
    exact hrank
  have hconstraints :
      Fintype.card I *
          Module.finrank K (totalTarget K 550 (99227150/(133225-2)) 61) ≤
        261851 * 1503271269 := Nat.mul_le_mul hnodes hrank'
  have hkernel := globalKernel_finrank_lower K I htwo
    550 99227150 133225 61 (by norm_num) nodes values
  norm_num only [Nat.reduceMul] at hkernel
  have hcolumns := helper_columns_lower
  omega

/-- Either heavy polynomial profile has product-band cost strictly below the
actual helper-kernel dimension on the identity-node subtype. -/
theorem expensive_product_band_lt_identityCoreHelperKernel
    (I : Type*) [Fintype I] (htwo : (2 : K)≠0) (nodes values : I→K)
    (hnodes : Fintype.card I≤261851) (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (fuel : Nat)
    (hprofile : 212≤jetDegree P ∨ 56≤derivativeDegree P) :
    helperProductBandSum P fuel <
      Module.finrank K (identityCoreHelperKernel K I htwo nodes values) := by
  exact (expensive_product_band_lt_budget P hP hrho fuel hprofile).trans_le
    (identityCoreHelperKernel_finrank_lower K I htwo nodes values hnodes)

/-- Fully connected source endpoint: the product-band inequality produces an
actual nondivisible quotient whose powered preimage lies in the helper
kernel. -/
theorem identityCoreHelper_exists_low_power_quotient
    (I : Type*) [Fintype I] (htwo : (2 : K)≠0) (nodes values : I→K)
    (hnodes : Fintype.card I≤261851) (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (fuel : Nat)
    (hprofile : 212≤jetDegree P ∨ 56≤derivativeDegree P)
    (hterminal :
      99227150≤(fuel+1)*mainDegree 133225 P ∨
        244<(fuel+1)*derivativeDegree P) :
    ∃ (j : Nat) (G : Poly4 K), j≤fuel ∧ G≠0 ∧
      P^j*G∈identityCoreHelperKernel K I htwo nodes values ∧
      G∈weightedCoefficientBox K
        (99227150-j*mainDegree 133225 P-j*47190) 133225
        (244-j*derivativeDegree P) ∧
      ¬P∣G ∧ j*mainDegree 133225 P<99227150 ∧
        j*derivativeDegree P≤244 := by
  apply exists_low_power_quotient
    (identityCoreHelperKernel K I htwo nodes values) P
    99227150 133225 244 47190 fuel (by norm_num)
    (identityCoreHelperKernel_le_box K I htwo nodes values) hP
    (expensive_product_band_lt_identityCoreHelperKernel K I htwo nodes values
      hnodes P hP hrho fuel hprofile) hterminal

theorem conservative_kernel_receipt :
    394078867563530-261851*1503271269=445782504611 := by norm_num

#print axioms identityCoreHelperKernel_finrank_lower
#print axioms expensive_product_band_lt_identityCoreHelperKernel
#print axioms identityCoreHelper_exists_low_power_quotient

end
end ProximityPrize.SubmissionLower.WeightedIdentityCoreHelperW1332256900
