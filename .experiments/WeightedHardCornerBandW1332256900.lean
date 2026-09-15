import WeightedHardJBandW1332256900

/-! The joint `(jetDegree >= 212, derivativeDegree >= 55)` corner band. -/
namespace ProximityPrize.SubmissionLower.WeightedHardCornerBandW1332256900

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
open WeightedHardJBandW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
noncomputable section

def cornerTop (j : Nat) : Nat :=
  2130677530-(j+1)*28243276-j*47190

def cornerDerivative (j : Nat) : Nat := 5248-(j+1)*55

def cornerRelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (cornerTop j) 133225 (cornerDerivative j)

theorem cornerRelaxedCount_zero (j : Nat) (hj : 75≤j) :
    cornerRelaxedCount j=0 := by
  have htop : cornerTop j=0 := by unfold cornerTop; omega
  rw [cornerRelaxedCount,htop,triangleRelaxedCount_zero_133225]

theorem cornerTop_mod_pos (j : Nat) (hj : j<75) :
    0<cornerTop j%133225 := by
  interval_cases j <;> norm_num [cornerTop]

theorem corner_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 75,cornerRelaxedCount j)=1921791896580 := by
  have hcast : (((∑ j ∈ Finset.range 75,cornerRelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 75,
        relaxedClosedQ (cornerTop j) 133225 (cornerDerivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · exact cornerTop_mod_pos j (Finset.mem_range.mp hj)
    · unfold cornerDerivative
      omega
  have heval :
      (∑ j ∈ Finset.range 75,
        relaxedClosedQ (cornerTop j) 133225 (cornerDerivative j))=
          (1921791896580:ℚ) := by
    norm_num (config := { maxSteps := 1200000 })
      [Finset.sum_range_succ,cornerTop,cornerDerivative,relaxedClosedQ,
      triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
      upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

theorem corner_relaxed_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,cornerRelaxedCount j)≤1921791896580 := by
  exact (sum_range_le_fixed_prefix_of_zero cornerRelaxedCount fuel 75
    cornerRelaxedCount_zero).trans_eq corner_relaxed_prefix_exact

variable {K : Type*} [Field K]

theorem corner_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hrho : 55≤derivativeDegree P) (hjet : 212≤jetDegree P) (j : Nat) :
    stageBand 2130677530 133225 5248 (mainDegree 133225 P)
        (derivativeDegree P) 47190 j≤47190*cornerRelaxedCount j := by
  have hg : 28243276≤mainDegree 133225 P := by
    have hm := (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
    norm_num only [Nat.reduceSub,Nat.reduceMul] at hm
    exact hm
  have hs := stageBand_le_profile 2130677530 133225 5248
    (mainDegree 133225 P) 28243276 (derivativeDegree P) 55 47190 j
    (by norm_num) hg hrho
  calc
    _ ≤ 47190*activeFibreCount (cornerTop j) 133225 (cornerDerivative j) := by
      simpa [cornerTop,cornerDerivative] using hs
    _ ≤ 47190*relaxedPairCount (cornerTop j) 133225 (cornerDerivative j) :=
      Nat.mul_le_mul_left 47190
        (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem corner_product_band_le (P : Poly4 K) (hP : P≠0)
    (hrho : 55≤derivativeDegree P) (hjet : 212≤jetDegree P)
    (fuel : Nat) :
    helperProductBandSum P fuel≤90689359599610200 := by
  unfold WeightedHardJBandW1332256900.helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,47190*cornerRelaxedCount j :=
      Finset.sum_le_sum fun j hj => corner_stage_le_relaxed P hP hrho hjet j
    _ = 47190*(∑ j ∈ Finset.range fuel,cornerRelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ 47190*1921791896580 :=
      Nat.mul_le_mul_left 47190 (corner_relaxed_sum_le fuel)
    _ = _ := by norm_num

end
end ProximityPrize.SubmissionLower.WeightedHardCornerBandW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedHardCornerBandW1332256900.corner_product_band_le
