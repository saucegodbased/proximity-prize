import WeightedFinitePrefixPrimaryHighTailW1332216900
import WeightedFinitePrefixPrimaryLowRankW1332216900

namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryTargetW1332216900

open scoped BigOperators
open WeightedQuadricContactTarget6900
open WeightedQuadricHighTruncation6900
open WeightedFinitePrefixHelperRankW1332196900
open WeightedFinitePrefixPrimaryHighTailW1332216900
open WeightedFinitePrefixPrimaryLowRankW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
noncomputable section

variable (K : Type*) [Field K]

theorem finiteHighPrefix_533_486_118 :
    (∑ s ∈ Finset.range 486,highRankBound 533 (s+236) 118)=710133469 := by
  have h := highTailRank_prefix_add_shifted_tail 533 486 118 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  rw [highTailRank_533_118,highTailRank_47_118] at h
  omega

/-- The target is charged only through its literal degree cutoff `M=721`.
The resulting local rank is `612420767+710133469=1322554236`. -/
theorem primary_totalTarget_rank_le (htwo : (2:K)≠0) :
    Module.finrank K (totalTarget K 533 721 59)≤1322554236 := by
  have h := totalTarget_finrank_le_exact_prefix K htwo 533 721 59 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [lowRankSum_533_59,finiteHighPrefix_533_486_118] at h
  exact h

end
end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryTargetW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryTargetW1332216900.finiteHighPrefix_533_486_118
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryTargetW1332216900.primary_totalTarget_rank_le
