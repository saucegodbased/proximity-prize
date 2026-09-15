import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# Literal 6811 scalar-source profile at the 6900 agreement threshold

This checks only the first source-dimension gate.  It deliberately keeps the
accepted `(multiplicity,yTotalCap,slopeCap) = (115,159,35)` and replaces the
agreement count `181284` by `180413`.
-/

namespace ProximityPrize.SubmissionLower.MovingFiber6811ScalarProfileRetarget6900

open RCN279 RCN285
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def targetWeightedCap : Nat := 115 * 180413

theorem target_coefficient_count_exact :
    coefficientCount targetWeightedCap 131071 159 35 = 47353889814 := by
  decide +kernel

theorem accepted_local_rank_bound_exact :
    localRankBound 115 159 35 = 182580 := by
  decide +kernel

/-- The accepted 6811 scalar profile loses source existence at 6900 before
any geometric counting theorem is reached. -/
theorem literal_profile_source_deficit :
    coefficientCount targetWeightedCap 131071 159 35 <
      262144 * localRankBound 115 159 35 /\
    262144 * localRankBound 115 159 35 -
      coefficientCount targetWeightedCap 131071 159 35 = 508361706 := by
  norm_num [target_coefficient_count_exact, accepted_local_rank_bound_exact]

#print axioms target_coefficient_count_exact
#print axioms accepted_local_rank_bound_exact
#print axioms literal_profile_source_deficit

end ProximityPrize.SubmissionLower.MovingFiber6811ScalarProfileRetarget6900
