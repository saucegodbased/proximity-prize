import WeightedHardCornerBandW1332256900

/-! Closed relaxed-fibre prefix for the W=133225 derivative-heavy band. -/
namespace ProximityPrize.SubmissionLower.WeightedHardDPrefixW1332256900

open scoped BigOperators
open WeightedSourceDerivativeBands6900
open WeightedRelaxedFibreCoreW1332246900
open WeightedTrianglePrefixFormulaW1332246900
open WeightedRelaxedFibreFormulaW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
noncomputable section

def d56Top (j : Nat) : Nat :=
  2130677530-(j+1)*3730244-j*47190

def d56Derivative (j : Nat) : Nat := 5248-(j+1)*56

def d56RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (d56Top j) 133225 (d56Derivative j)

theorem d56Top_mod_pos (j : Nat) (hj : j<93) :
    0<d56Top j%133225 := by
  interval_cases j <;> norm_num [d56Top]

theorem d56_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 93,d56RelaxedCount j)=2831297168548 := by
  have hcast : (((∑ j ∈ Finset.range 93,d56RelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 93,
        relaxedClosedQ (d56Top j) 133225 (d56Derivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · exact d56Top_mod_pos j (Finset.mem_range.mp hj)
    · unfold d56Derivative
      omega
  have heval :
      (∑ j ∈ Finset.range 93,
        relaxedClosedQ (d56Top j) 133225 (d56Derivative j))=
          (2831297168548:ℚ) := by
    norm_num (config := { maxSteps := 1200000 })
      [Finset.sum_range_succ,d56Top,d56Derivative,relaxedClosedQ,
      triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
      upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

end
end ProximityPrize.SubmissionLower.WeightedHardDPrefixW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedHardDPrefixW1332256900.d56_relaxed_prefix_exact
