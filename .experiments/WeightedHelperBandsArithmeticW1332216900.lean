import WeightedRelaxedFibreFormulaW1332216900

/-! Closed arithmetic receipts for the W=133221 helper's J207 and D54
relaxed active-fibre profiles. -/
namespace ProximityPrize.SubmissionLower.WeightedHelperBandsArithmeticW1332216900

open scoped BigOperators
open WeightedSourceDerivativeBands6900
open WeightedRelaxedFibreCoreW1332216900
open WeightedTrianglePrefixFormulaW1332216900
open WeightedRelaxedFibreFormulaW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500

def j207Top (j : Nat) : Nat :=
  2032893684-(j+1)*27709552-j*47194

def j207Derivative (j : Nat) : Nat := 5008-(j+1)*2

def j207RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (j207Top j) 133221 (j207Derivative j)

def d54Top (j : Nat) : Nat :=
  2032893684-(j+1)*3730132-j*47194

def d54Derivative (j : Nat) : Nat := 5008-(j+1)*55

def d54RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (d54Top j) 133221 (d54Derivative j)

theorem triangleRelaxedCount_zero_133221 (E : Nat) :
    triangleRelaxedCount 0 133221 E=0 := by
  simp [triangleRelaxedCount,ceilWidth]

theorem j207RelaxedCount_zero (j : Nat) (hj : 73≤j) :
    j207RelaxedCount j=0 := by
  have htop : j207Top j=0 := by unfold j207Top; omega
  rw [j207RelaxedCount,htop,triangleRelaxedCount_zero_133221]

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

theorem j207_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 73,j207RelaxedCount j)=2396636777677 := by
  have hcast : (((∑ j ∈ Finset.range 73,j207RelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 73,
        relaxedClosedQ (j207Top j) 133221 (j207Derivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · have hj' := Finset.mem_range.mp hj
      interval_cases j <;> norm_num [j207Top]
    · unfold j207Derivative
      omega
  have heval :
      (∑ j ∈ Finset.range 73,
        relaxedClosedQ (j207Top j) 133221 (j207Derivative j))=
          (2396636777677:ℚ) := by
    norm_num (config := { maxSteps := 1000000 })
      [Finset.sum_range_succ,j207Top,j207Derivative,relaxedClosedQ,
      triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
      upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

theorem d54_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 91,d54RelaxedCount j)=2386935979544 := by
  have hcast : (((∑ j ∈ Finset.range 91,d54RelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 91,
        relaxedClosedQ (d54Top j) 133221 (d54Derivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · have hj' := Finset.mem_range.mp hj
      interval_cases j <;> norm_num [d54Top]
    · unfold d54Derivative
      omega
  have heval :
      (∑ j ∈ Finset.range 91,
        relaxedClosedQ (d54Top j) 133221 (d54Derivative j))=
          (2386935979544:ℚ) := by
    norm_num (config := { maxSteps := 1000000 })
      [Finset.sum_range_succ,d54Top,d54Derivative,relaxedClosedQ,
      triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
      upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

theorem j207_relaxed_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,j207RelaxedCount j)≤2396636777677 := by
  exact (sum_range_le_fixed_prefix_of_zero j207RelaxedCount fuel 73
    j207RelaxedCount_zero).trans_eq j207_relaxed_prefix_exact

end ProximityPrize.SubmissionLower.WeightedHelperBandsArithmeticW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedHelperBandsArithmeticW1332216900.j207_relaxed_prefix_exact
#print axioms ProximityPrize.SubmissionLower.WeightedHelperBandsArithmeticW1332216900.d54_relaxed_prefix_exact
