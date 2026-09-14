import WeightedHelperBandsArithmeticW1332216900
import WeightedFinitePrefixHelperKernelW1332216900

/-! Semantic J207/D54 product-band gates for the actual W=133221 helper
kernel.  These bounds retain the exact shrinking derivative triangle and use
the conservative W-2 relaxation only in the finite arithmetic majorant. -/
namespace ProximityPrize.SubmissionLower.WeightedHelperBandsW1332216900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedSourceBoxQuotient6900
open WeightedSourceColumnBands6900
open WeightedSourceDerivativeBands6900
open WeightedStageFibreBoundProbe6900
open WeightedActualProductBandGate6900
open WeightedRelaxedFibreCoreW1332216900
open WeightedHelperBandsArithmeticW1332216900
open WeightedFinitePrefixHelperKernelW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
noncomputable section

variable {K : Type*} [Field K]

def helperProductBandSum (P : Poly4 K) (fuel : Nat) : Nat :=
  ∑ j ∈ Finset.range fuel,
    stageBand 2032893684 133221 5008 (mainDegree 133221 P)
      (derivativeDegree P) 47194 j

theorem j207_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 208≤jetDegree P) (j : Nat) :
    stageBand 2032893684 133221 5008 (mainDegree 133221 P)
        (derivativeDegree P) 47194 j≤47194*j207RelaxedCount j := by
  have hg : 27709552≤mainDegree 133221 P := by
    have hm := (Nat.mul_le_mul_left (133221-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133221 P hP)
    norm_num only [Nat.reduceSub,Nat.reduceMul] at hm
    exact hm
  have hs := stageBand_le_profile 2032893684 133221 5008
    (mainDegree 133221 P) 27709552 (derivativeDegree P) 2 47194 j
    (by norm_num) hg hrho
  calc
    _ ≤ 47194*activeFibreCount (j207Top j) 133221 (j207Derivative j) := by
      simpa [j207Top,j207Derivative] using hs
    _ ≤ 47194*relaxedPairCount (j207Top j) 133221 (j207Derivative j) :=
      Nat.mul_le_mul_left 47194
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem d54_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 55≤derivativeDegree P) (j : Nat) :
    stageBand 2032893684 133221 5008 (mainDegree 133221 P)
        (derivativeDegree P) 47194 j≤47194*d54RelaxedCount j := by
  have hjet : 28≤jetDegree P := by
    have hrel := derivativeDegree_le_twice_jetDegree P
    omega
  have hg : 3730132≤mainDegree 133221 P := by
    have hm := (Nat.mul_le_mul_left (133221-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133221 P hP)
    norm_num only [Nat.reduceSub,Nat.reduceMul] at hm
    exact hm
  have hs := stageBand_le_profile 2032893684 133221 5008
    (mainDegree 133221 P) 3730132 (derivativeDegree P) 55 47194 j
    (by norm_num) hg hrho
  calc
    _ ≤ 47194*activeFibreCount (d54Top j) 133221 (d54Derivative j) := by
      simpa [d54Top,d54Derivative] using hs
    _ ≤ 47194*relaxedPairCount (d54Top j) 133221 (d54Derivative j) :=
      Nat.mul_le_mul_left 47194
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem d54_stage_zero (P : Poly4 K) (hrho : 55≤derivativeDegree P)
    (j : Nat) (hj : 91≤j) :
    stageBand 2032893684 133221 5008 (mainDegree 133221 P)
      (derivativeDegree P) 47194 j=0 := by
  unfold stageBand
  rw [if_neg]
  have hm := Nat.mul_le_mul_left (j+1) hrho
  omega

/-- J207 branch: the conservative relaxed charge is
`113106876085688338`, leaving margin `5381132692459`. -/
theorem j207_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 208≤jetDegree P)
    (fuel : Nat) : helperProductBandSum P fuel≤113106876085688338 := by
  unfold helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,47194*j207RelaxedCount j :=
      Finset.sum_le_sum fun j hj => j207_stage_le_relaxed P hP hrho hjet j
    _ = 47194*(∑ j ∈ Finset.range fuel,j207RelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ 47194*2396636777677 :=
      Nat.mul_le_mul_left 47194 (j207_relaxed_sum_le fuel)
    _ = _ := by norm_num

/-- D54 branch: the conservative relaxed charge is
`112649056618599536`, leaving margin `463200599781261`. -/
theorem d54_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 55≤derivativeDegree P) (fuel : Nat) :
    helperProductBandSum P fuel≤112649056618599536 := by
  unfold helperProductBandSum
  have hprefix :
      (∑ j ∈ Finset.range fuel,
        stageBand 2032893684 133221 5008 (mainDegree 133221 P)
          (derivativeDegree P) 47194 j)≤
      ∑ j ∈ Finset.range 91,
        stageBand 2032893684 133221 5008 (mainDegree 133221 P)
          (derivativeDegree P) 47194 j := by
    apply sum_range_le_fixed_prefix_of_zero
    intro j hj
    exact d54_stage_zero P hrho j hj
  calc
    _ ≤ ∑ j ∈ Finset.range 91,
        stageBand 2032893684 133221 5008 (mainDegree 133221 P)
          (derivativeDegree P) 47194 j := hprefix
    _ ≤ ∑ j ∈ Finset.range 91,47194*d54RelaxedCount j :=
      Finset.sum_le_sum fun j hj => d54_stage_le_relaxed P hP hrho j
    _ = 47194*(∑ j ∈ Finset.range 91,d54RelaxedCount j) := by
      rw [Finset.mul_sum]
    _ = 47194*2386935979544 := by rw [d54_relaxed_prefix_exact]
    _ = _ := by norm_num

theorem j207_product_band_lt_kernel (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 208≤jetDegree P)
    (fuel : Nat) : helperProductBandSum P fuel<113112257218380797 :=
  (j207_product_band_le P hP hrho hjet fuel).trans_lt (by norm_num)

theorem d54_product_band_lt_kernel (P : Poly4 K) (hP : P≠0)
    (hrho : 55≤derivativeDegree P) (fuel : Nat) :
    helperProductBandSum P fuel<113112257218380797 :=
  (d54_product_band_le P hP hrho fuel).trans_lt (by norm_num)

theorem expensive_product_band_lt_kernel (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (fuel : Nat)
    (hprofile : 208≤jetDegree P ∨ 55≤derivativeDegree P) :
    helperProductBandSum P fuel<113112257218380797 := by
  rcases hprofile with hjet | hder
  · exact j207_product_band_lt_kernel P hP hrho hjet fuel
  · exact d54_product_band_lt_kernel P hP hder fuel

theorem expensive_product_band_lt_polynomialKernel
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144)
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P)
    (fuel : Nat) (hprofile : 208≤jetDegree P ∨ 55≤derivativeDegree P) :
    helperProductBandSum P fuel<Module.finrank K
      (helperPolynomialKernel K I htwo nodes values) :=
  (expensive_product_band_lt_kernel P hP hrho fuel hprofile).trans_le
    (helperPolynomialKernel_dimension K I htwo nodes values hn)

end
end ProximityPrize.SubmissionLower.WeightedHelperBandsW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedHelperBandsW1332216900.j207_product_band_le
#print axioms ProximityPrize.SubmissionLower.WeightedHelperBandsW1332216900.d54_product_band_le
#print axioms ProximityPrize.SubmissionLower.WeightedHelperBandsW1332216900.expensive_product_band_lt_polynomialKernel
