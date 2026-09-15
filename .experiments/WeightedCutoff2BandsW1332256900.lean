import WeightedCutoff2PrefixBoundsW1332256900
import WeightedActualProductBandGate6900

/-! J211/D55 product-band receipts for the cutoff-two W=133225 helper. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2BandsW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedSourceBoxQuotient6900
open WeightedSourceColumnBands6900
open WeightedSourceDerivativeBands6900
open WeightedStageFibreBoundProbe6900
open WeightedActualProductBandGate6900
open WeightedRelaxedFibreCoreW1332246900
open WeightedTrianglePrefixFormulaW1332246900
open WeightedRelaxedFibreFormulaW1332256900
open WeightedCutoff2ContinuousArithmeticW1332256900
open WeightedCutoff2PrefixBoundsW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
noncomputable section

def j211Top (j : Nat) : Nat :=
  2130677530-(j+1)*28243276-j*47190

def j211Derivative (j : Nat) : Nat := 5248-(j+1)*2

def j211RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (j211Top j) 133225 (j211Derivative j)

def d55Top (j : Nat) : Nat :=
  2130677530-(j+1)*3730244-j*47190

def d55Derivative (j : Nat) : Nat := 5248-(j+1)*56

def d55RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (d55Top j) 133225 (d55Derivative j)

theorem triangleRelaxedCount_zero_133225 (E : Nat) :
    triangleRelaxedCount 0 133225 E=0 := by
  simp [triangleRelaxedCount,ceilWidth]

theorem j211RelaxedCount_zero (j : Nat) (hj : 75≤j) :
    j211RelaxedCount j=0 := by
  have htop : j211Top j=0 := by unfold j211Top; omega
  rw [j211RelaxedCount,htop,triangleRelaxedCount_zero_133225]

theorem j211Top_eq_jC (j : Nat) : j211Top j=jC j := by
  unfold j211Top jC
  omega

theorem j211Derivative_eq_jE (j : Nat) : j211Derivative j=jE j := by
  unfold j211Derivative jE
  omega

theorem d55Top_eq_dC (j : Nat) : d55Top j=dC j := by
  unfold d55Top dC
  omega

theorem d55Derivative_eq_dE (j : Nat) : d55Derivative j=dE j := by
  unfold d55Derivative dE
  omega

theorem j211RelaxedCount_eq_external (j : Nat) :
    j211RelaxedCount j=jRelaxedCount j := by
  unfold j211RelaxedCount jRelaxedCount
  rw [j211Top_eq_jC,j211Derivative_eq_jE]

theorem d55RelaxedCount_eq_external (j : Nat) :
    d55RelaxedCount j=dRelaxedCount j := by
  unfold d55RelaxedCount dRelaxedCount
  rw [d55Top_eq_dC,d55Derivative_eq_dE]

theorem sum_range_le_fixed_prefix_of_zero (f : Nat→Nat) (fuel cutoff : Nat)
    (hz : ∀ j,cutoff≤j→f j=0) :
    (∑ j ∈ Finset.range fuel,f j)≤∑ j ∈ Finset.range cutoff,f j := by
  by_cases hf : fuel≤cutoff
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hf)
      (fun _ _ _ => Nat.zero_le _)
  · have hcf : cutoff≤fuel := by omega
    have heq : (∑ j ∈ Finset.range cutoff,f j)=∑ j ∈ Finset.range fuel,f j := by
      apply Finset.sum_subset (Finset.range_mono hcf)
      intro j hj hsmall
      apply hz j
      have hnot : ¬j<cutoff := fun h => hsmall (Finset.mem_range.mpr h)
      omega
    exact heq.ge

theorem j211_relaxed_prefix_le :
    (∑ j ∈ Finset.range (51+24),j211RelaxedCount j)≤2838653664050 := by
  have heq :
      (∑ j ∈ Finset.range (51+24),j211RelaxedCount j)=
        ∑ j ∈ Finset.range (51+24),jRelaxedCount j := by
    exact Finset.sum_congr rfl (fun j hj => j211RelaxedCount_eq_external j)
  exact heq.trans_le j_relaxed_prefix_le

theorem d55_relaxed_prefix_le :
    (∑ j ∈ Finset.range 93,d55RelaxedCount j)≤2831401397270 := by
  have heq :
      (∑ j ∈ Finset.range 93,d55RelaxedCount j)=
        ∑ j ∈ Finset.range 93,dRelaxedCount j := by
    exact Finset.sum_congr rfl (fun j hj => d55RelaxedCount_eq_external j)
  exact heq.trans_le d_relaxed_prefix_le

theorem j211_relaxed_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,j211RelaxedCount j)≤2838653664050 := by
  exact (sum_range_le_fixed_prefix_of_zero j211RelaxedCount fuel (51+24)
    (fun j hj => j211RelaxedCount_zero j hj)).trans j211_relaxed_prefix_le

variable {K : Type*} [Field K]

def helperProductBandSum (P : Poly4 K) (fuel : Nat) : Nat :=
  ∑ j ∈ Finset.range fuel,
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j

theorem helperProductBandSum_eq (P : Poly4 K) (fuel : Nat) :
    helperProductBandSum P fuel=
      ∑ j ∈ Finset.range fuel,
        stageBand 2130677530 133225 5248 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := rfl

theorem j211_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 212≤jetDegree P) (j : Nat) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
        (derivativeDegree P) 47190 j≤47190*j211RelaxedCount j := by
  have hg : 28243276≤mainDegree 133225 P := by
    have hm := (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
    norm_num only [Nat.reduceSub,Nat.reduceMul] at hm
    exact hm
  have hs := stageBand_le_profile 2130677530 133225 5248
    (mainDegree 133225 P) 28243276 (derivativeDegree P) 2 47190 j
    (by norm_num) hg hrho
  calc
    _ ≤ 47190*activeFibreCount (j211Top j) 133225 (j211Derivative j) := by
      simpa [j211Top,j211Derivative] using hs
    _ ≤ 47190*relaxedPairCount (j211Top j) 133225 (j211Derivative j) :=
      Nat.mul_le_mul_left 47190
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem d55_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 56≤derivativeDegree P) (j : Nat) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
        (derivativeDegree P) 47190 j≤47190*d55RelaxedCount j := by
  have hjet : 28≤jetDegree P := by
    have hrel := derivativeDegree_le_twice_jetDegree P
    omega
  have hg : 3730244≤mainDegree 133225 P := by
    have hm := (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
    norm_num only [Nat.reduceSub,Nat.reduceMul] at hm
    exact hm
  have hs := stageBand_le_profile 2130677530 133225 5248
    (mainDegree 133225 P) 3730244 (derivativeDegree P) 56 47190 j
    (by norm_num) hg hrho
  calc
    _ ≤ 47190*activeFibreCount (d55Top j) 133225 (d55Derivative j) := by
      simpa [d55Top,d55Derivative] using hs
    _ ≤ 47190*relaxedPairCount (d55Top j) 133225 (d55Derivative j) :=
      Nat.mul_le_mul_left 47190
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem d55_stage_zero (P : Poly4 K) (hrho : 56≤derivativeDegree P)
    (j : Nat) (hj : 93≤j) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j=0 := by
  unfold stageBand
  rw [if_neg]
  have hm := Nat.mul_le_mul_left (j+1) hrho
  omega

theorem j211_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 212≤jetDegree P)
    (fuel : Nat) : helperProductBandSum P fuel≤133956066406519500 := by
  unfold helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,47190*j211RelaxedCount j :=
      Finset.sum_le_sum fun j hj => j211_stage_le_relaxed P hP hrho hjet j
    _ = 47190*(∑ j ∈ Finset.range fuel,j211RelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ 47190*2838653664050 :=
      Nat.mul_le_mul_left 47190 (j211_relaxed_sum_le fuel)
    _ = _ := by norm_num

theorem d55_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 56≤derivativeDegree P) (fuel : Nat) :
    helperProductBandSum P fuel≤133613831937171300 := by
  unfold helperProductBandSum
  have hprefix :
      (∑ j ∈ Finset.range fuel,
        stageBand 2130677530 133225 5248 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j)≤
      ∑ j ∈ Finset.range 93,
        stageBand 2130677530 133225 5248 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := by
    apply sum_range_le_fixed_prefix_of_zero
    intro j hj
    exact d55_stage_zero P hrho j hj
  calc
    _ ≤ ∑ j ∈ Finset.range 93,
        stageBand 2130677530 133225 5248 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := hprefix
    _ ≤ ∑ j ∈ Finset.range 93,47190*d55RelaxedCount j :=
      Finset.sum_le_sum fun j hj => d55_stage_le_relaxed P hP hrho j
    _ = 47190*(∑ j ∈ Finset.range 93,d55RelaxedCount j) := by
      exact sum_mul_eq_mul_sum (Finset.range 93) 47190 d55RelaxedCount
    _ ≤ 47190*2831401397270 :=
      Nat.mul_le_mul_left 47190 d55_relaxed_prefix_le
    _ = _ := by norm_num

theorem expensive_product_band_lt_kernel (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (fuel : Nat)
    (hprofile : 212≤jetDegree P ∨ 56≤derivativeDegree P) :
    helperProductBandSum P fuel<133965718104546337 := by
  rcases hprofile with hjet | hder
  · exact (j211_product_band_le P hP hrho hjet fuel).trans_lt (by norm_num)
  · exact (d55_product_band_le P hP hder fuel).trans_lt (by norm_num)

end
end ProximityPrize.SubmissionLower.WeightedCutoff2BandsW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2BandsW1332256900.j211_product_band_le
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2BandsW1332256900.d55_product_band_le
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2BandsW1332256900.expensive_product_band_lt_kernel
