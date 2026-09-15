import WeightedHardDPrefixW1332256900

/-! The `derivativeDegree >= 56` hard-product band. -/
namespace ProximityPrize.SubmissionLower.WeightedHardDBandW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedSourceBoxQuotient6900
open WeightedSourceColumnBands6900
open WeightedSourceDerivativeBands6900
open WeightedStageFibreBoundProbe6900
open WeightedActualProductBandGate6900
open WeightedRelaxedFibreCoreW1332246900
open WeightedHardJBandW1332256900
open WeightedHardDPrefixW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
noncomputable section

theorem d56_stage_zero {K : Type*} [Field K] (P : Poly4 K)
    (hrho : 56≤derivativeDegree P) (j : Nat) (hj : 93≤j) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j=0 := by
  unfold stageBand
  rw [if_neg]
  have hm := Nat.mul_le_mul_left (j+1) hrho
  omega

variable {K : Type*} [Field K]

theorem d56_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 56≤derivativeDegree P) (j : Nat) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
        (derivativeDegree P) 47190 j≤47190*d56RelaxedCount j := by
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
    _ ≤ 47190*activeFibreCount (d56Top j) 133225 (d56Derivative j) := by
      simpa [d56Top,d56Derivative] using hs
    _ ≤ 47190*relaxedPairCount (d56Top j) 133225 (d56Derivative j) :=
      Nat.mul_le_mul_left 47190
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

/-- Truncate the relaxed majorant exactly where the actual stage band is
definitionally zero.  This keeps the final variable-fuel proof from carrying
a concrete 93-stage `stageBand` expression through kernel reduction. -/
def d56TruncatedRelaxedCount (j : Nat) : Nat :=
  if j<93 then d56RelaxedCount j else 0

theorem d56TruncatedRelaxedCount_zero (j : Nat) (hj : 93≤j) :
    d56TruncatedRelaxedCount j=0 := by
  simp [d56TruncatedRelaxedCount,hj]

theorem d56_truncated_prefix_exact :
    (∑ j ∈ Finset.range 93,d56TruncatedRelaxedCount j)=2831297168548 := by
  rw [show (∑ j ∈ Finset.range 93,d56TruncatedRelaxedCount j)=
      ∑ j ∈ Finset.range 93,d56RelaxedCount j by
    apply Finset.sum_congr rfl
    intro j hj
    simp [d56TruncatedRelaxedCount,Finset.mem_range.mp hj]]
  exact d56_relaxed_prefix_exact

theorem d56_truncated_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,d56TruncatedRelaxedCount j)≤2831297168548 := by
  exact (WeightedHardJBandW1332256900.sum_range_le_fixed_prefix_of_zero
    d56TruncatedRelaxedCount fuel 93 d56TruncatedRelaxedCount_zero).trans_eq
      d56_truncated_prefix_exact

theorem d56_stage_le_truncated (P : Poly4 K) (hP : P≠0)
    (hrho : 56≤derivativeDegree P) (j : Nat) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
        (derivativeDegree P) 47190 j≤47190*d56TruncatedRelaxedCount j := by
  by_cases hj : j<93
  · simpa [d56TruncatedRelaxedCount,hj] using
      d56_stage_le_relaxed P hP hrho j
  · have hz := d56_stage_zero P hrho j (by omega)
    rw [hz]
    exact Nat.zero_le _

theorem d56_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 56≤derivativeDegree P) (fuel : Nat) :
    helperProductBandSum P fuel≤133608913383780120 := by
  unfold WeightedHardJBandW1332256900.helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,47190*d56TruncatedRelaxedCount j :=
      Finset.sum_le_sum fun j hj => d56_stage_le_truncated P hP hrho j
    _ = 47190*(∑ j ∈ Finset.range fuel,d56TruncatedRelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ 47190*2831297168548 :=
      Nat.mul_le_mul_left 47190 (d56_truncated_sum_le fuel)
    _ = _ := by norm_num

end
end ProximityPrize.SubmissionLower.WeightedHardDBandW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedHardDBandW1332256900.d56_product_band_le
