import WeightedRelaxedFibreFormulaW1332256900
import WeightedActualProductBandGate6900

/-! The `jetDegree >= 213` hard-product band at W=133225. -/
namespace ProximityPrize.SubmissionLower.WeightedHardJBandW1332256900

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

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
noncomputable section

theorem triangleRelaxedCount_zero_133225 (E : Nat) :
    triangleRelaxedCount 0 133225 E=0 := by
  simp [triangleRelaxedCount,ceilWidth]

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

def j213Top (j : Nat) : Nat :=
  2130677530-(j+1)*28376499-j*47190

def j213Derivative (j : Nat) : Nat := 5248-(j+1)*2

def j213RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (j213Top j) 133225 (j213Derivative j)

theorem j213RelaxedCount_zero (j : Nat) (hj : 74≤j) :
    j213RelaxedCount j=0 := by
  have htop : j213Top j=0 := by unfold j213Top; omega
  rw [j213RelaxedCount,htop,triangleRelaxedCount_zero_133225]

theorem j213Top_mod_pos (j : Nat) (hj : j<74) :
    0<j213Top j%133225 := by
  interval_cases j <;> norm_num [j213Top]

theorem j213_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 74,j213RelaxedCount j)=2825124043212 := by
  have hcast : (((∑ j ∈ Finset.range 74,j213RelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 74,
        relaxedClosedQ (j213Top j) 133225 (j213Derivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · exact j213Top_mod_pos j (Finset.mem_range.mp hj)
    · unfold j213Derivative
      omega
  have heval :
      (∑ j ∈ Finset.range 74,
        relaxedClosedQ (j213Top j) 133225 (j213Derivative j))=
          (2825124043212:ℚ) := by
    norm_num (config := { maxSteps := 1200000 })
      [Finset.sum_range_succ,j213Top,j213Derivative,relaxedClosedQ,
      triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
      upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

theorem j213_relaxed_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,j213RelaxedCount j)≤2825124043212 := by
  exact (sum_range_le_fixed_prefix_of_zero j213RelaxedCount fuel 74
    j213RelaxedCount_zero).trans_eq j213_relaxed_prefix_exact

variable {K : Type*} [Field K]

def helperProductBandSum (P : Poly4 K) (fuel : Nat) : Nat :=
  ∑ j ∈ Finset.range fuel,
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j

theorem j213_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 213≤jetDegree P) (j : Nat) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
        (derivativeDegree P) 47190 j≤47190*j213RelaxedCount j := by
  have hg : 28376499≤mainDegree 133225 P := by
    have hm := (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
    norm_num only [Nat.reduceSub,Nat.reduceMul] at hm
    exact hm
  have hs := stageBand_le_profile 2130677530 133225 5248
    (mainDegree 133225 P) 28376499 (derivativeDegree P) 2 47190 j
    (by norm_num) hg hrho
  calc
    _ ≤ 47190*activeFibreCount (j213Top j) 133225 (j213Derivative j) := by
      simpa [j213Top,j213Derivative] using hs
    _ ≤ 47190*relaxedPairCount (j213Top j) 133225 (j213Derivative j) :=
      Nat.mul_le_mul_left 47190
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem j213_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P) (hjet : 213≤jetDegree P)
    (fuel : Nat) :
    helperProductBandSum P fuel≤133317603599174280 := by
  unfold helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,47190*j213RelaxedCount j :=
      Finset.sum_le_sum fun j hj => j213_stage_le_relaxed P hP hrho hjet j
    _ = 47190*(∑ j ∈ Finset.range fuel,j213RelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ 47190*2825124043212 :=
      Nat.mul_le_mul_left 47190 (j213_relaxed_sum_le fuel)
    _ = _ := by norm_num

end
end ProximityPrize.SubmissionLower.WeightedHardJBandW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedHardJBandW1332256900.j213_product_band_le
