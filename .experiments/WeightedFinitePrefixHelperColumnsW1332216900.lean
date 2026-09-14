import WeightedFinitePrefixHelperPairSumW1332216900
import WeightedFinitePrefixPrimaryColumnsW1332216900

/-! Integer source-column lower bound for the W=133221 helper. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperColumnsW1332216900

open WeightedSourceIndex6900
open WeightedFinitePrefixPrimaryColumnsW1332216900
open WeightedFinitePrefixHelperPairSumW1332216900
open WeightedFinitePrefixHelperRankW1332196900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 1800

/-- The exact pair polynomial sum has remainder `3546` modulo
`2*133221`; taking the floor gives this conservative column receipt. -/
theorem helper_columns_lower :
    68450284539644380157≤columns 2032893684 133221 5008 := by
  have hbase : helperPairPolynomialSum 1252≤
      (2*133221)*columns 2032893684 133221 5008 := by
    simpa [helperPairPolynomialSum] using
      pairPolynomialSum_le_columns 2032893684 133221 5008 (by norm_num)
  rw [helperPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266442*68450284539644380157≤
      18238030713311927937794940 := by norm_num
  have hc : 266442*68450284539644380157≤
      266442*columns 2032893684 133221 5008 := hn.trans hbase
  exact cancel_nat_mul_le 266442 68450284539644380157
    (columns 2032893684 133221 5008) (by norm_num) hc

end ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperColumnsW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperColumnsW1332216900.helper_columns_lower
