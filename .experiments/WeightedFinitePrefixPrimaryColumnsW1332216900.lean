import WeightedFinitePrefixPrimaryPairSumW1332216900

/-! Integer column lower bound extracted from the exact W=133221 pair sum. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryColumnsW1332216900

open scoped BigOperators
open WeightedSourceIndex6900
open WeightedFinitePrefixHelperRankW1332196900
open WeightedFinitePrefixPrimaryPairSumW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000

/-- Generic column charge, kept symbolic so the simplifier never evaluates a
large concrete `Finset.range`. -/
theorem pairPolynomialSum_le_columns (B W D : Nat) (hW : 0<W) :
    genericPairPolynomialSum B W D≤(2*W)*columns B W D := by
  unfold genericPairPolynomialSum columns
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact WeightedSourceColumnWidths6900.sum_widthSum_lower
    (Finset.range (D-2*t+1))
    (fun r => WeightedSourceIndex6900.pairWidth B W r t) W hW

/-- `92375427127187459192 / (2*133221)` floors to
`346699946431821`; the remainder is positive and harmless. -/
theorem primary_columns_lower :
    346699946431821≤columns 96160129 133221 236 := by
  have hbase : primaryPairPolynomialSum≤
      (2*133221)*columns 96160129 133221 236 := by
    exact pairPolynomialSum_le_columns 96160129 133221 236 (by norm_num)
  rw [primaryPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266442*346699946431821≤92375427127187459192 := by norm_num
  have hc : 266442*346699946431821≤
      266442*columns 96160129 133221 236 := hn.trans hbase
  exact cancel_nat_mul_le 266442 346699946431821
    (columns 96160129 133221 236) (by norm_num) hc

end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryColumnsW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryColumnsW1332216900.primary_columns_lower
