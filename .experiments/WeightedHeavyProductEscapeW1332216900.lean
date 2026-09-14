import WeightedSourcePowerEscape6900
import WeightedPolynomialContactKernel6900
import WeightedFinitePrefixHelperKernelW1332216900
import WeightedHelperBandsW1332216900

/-! Actual heavy-product escape for the reconstructed W=133221 helper.
The source kernel and product-band bounds are the proved finite-prefix
producers; the returned original source retains all-node contact. -/

namespace ProximityPrize.SubmissionLower.WeightedHeavyProductEscapeW1332216900

open scoped BigOperators
open Order2SourceBasisScaffold WeightedSourceIndex6900
open WeightedSourceBoxQuotient6900 WeightedSourceColumnBands6900
open WeightedSourcePowerEscape6900 WeightedPolynomialContactKernel6900
open WeightedActualProductBandGate6900
open WeightedHelperBandsW1332216900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

variable (K : Type*) [Field K]

/-- The W=133221 reconstructed helper kernel, exposed under the escape
namespace for its downstream consumers. -/
def helperPolynomialKernel (I : Type*) [Fintype I] (htwo : (2 : K)≠0)
    (nodes values : I → K) : Submodule K (Poly4 K) :=
  WeightedFinitePrefixHelperKernelW1332216900.helperPolynomialKernel
    K I htwo nodes values

theorem helperPolynomialKernel_le_box (I : Type*) [Fintype I]
    (htwo : (2 : K)≠0) (nodes values : I → K) :
    helperPolynomialKernel K I htwo nodes values ≤
      weightedCoefficientBox K 2032893684 133221 5008 := by
  exact polynomialKernel_le_box K I htwo 11268 2032893684 133221 1252
    (by norm_num) nodes values

theorem helperPolynomialKernel_dimension (I : Type*) [Fintype I]
    (htwo : (2 : K)≠0) (nodes values : I → K)
    (hn : Fintype.card I≤262144) :
    113112257218380797≤Module.finrank K
      (helperPolynomialKernel K I htwo nodes values) := by
  exact WeightedFinitePrefixHelperKernelW1332216900.helperPolynomialKernel_dimension
    K I htwo nodes values hn

/-- Every actual W=133221 heavy product of derivative weight at least two has
a low-band exit. The multiplied polynomial remains in the original helper
kernel, so it retains order-11268 contact at every node. -/
theorem heavy_product_escape (I : Type*) [Fintype I] (htwo : (2 : K)≠0)
    (nodes values : I → K) (hn : Fintype.card I≤262144)
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P)
    (hheavy : 208≤jetDegree P ∨ 55≤derivativeDegree P) :
    ∃ (j : Nat) (G : Poly4 K),
      j≤2504 ∧ G≠0 ∧ ¬P∣G ∧
      P^j*G∈helperPolynomialKernel K I htwo nodes values ∧
      G∈weightedCoefficientBox K
        (2032893684-j*mainDegree 133221 P-j*47194) 133221
        (5008-j*derivativeDegree P) ∧
      P^j*G∈weightedCoefficientBox K (2032893684-j*47194) 133221 5008 ∧
      (∀ i : I, contactTruncation K 11268
        (localSubstitution K (nodes i) (values i) (P^j*G))=0) ∧
      P^j*G≠0 ∧ j*mainDegree 133221 P<2032893684 ∧
      j*derivativeDegree P≤5008 := by
  let V := helperPolynomialKernel K I htwo nodes values
  have hV : V≤weightedCoefficientBox K 2032893684 133221 5008 :=
    helperPolynomialKernel_le_box K I htwo nodes values
  have hbudget :
      (∑ j ∈ Finset.range 2504,
        stageBand 2032893684 133221 5008 (mainDegree 133221 P)
          (derivativeDegree P) 47194 j)<Module.finrank K V := by
    have hb := expensive_product_band_lt_kernel P hP hrho 2504 hheavy
    exact hb.trans_le
      (helperPolynomialKernel_dimension K I htwo nodes values hn)
  have hterminal : 5008<(2504+1)*derivativeDegree P := by
    omega
  obtain ⟨j,G,hj,hG,hOriginal,hQuotient,hnd,hmain,hder⟩ :=
    exists_low_power_quotient V P 2032893684 133221 5008 47194 2504
      (by norm_num) hV hP hbudget (Or.inr hterminal)
  have hstage : G∈powerStage V P 2032893684 133221 5008 47194 j :=
    ⟨hOriginal,hQuotient⟩
  have htight := stage_original_mem_tightened V P G 2032893684 133221
    5008 47194 j hV hP hG hstage
  have hcontact := polynomialKernel_contact K I htwo 11268 2032893684
    133221 1252 (by norm_num) nodes values hOriginal
  exact ⟨j,G,hj,hG,hnd,hOriginal,hQuotient,htight,hcontact,
    mul_ne_zero (pow_ne_zero j hP) hG,hmain,hder⟩

#print axioms helperPolynomialKernel_le_box
#print axioms helperPolynomialKernel_dimension
#print axioms heavy_product_escape

end
end ProximityPrize.SubmissionLower.WeightedHeavyProductEscapeW1332216900
