import ProximityPrize.Benchmark.TargetLower

/-!
Exact arithmetic behind the canonical agreement-tangent order for the
target-positive `(148,64,30,200,5465,4,5)` second-jet profile.
-/

namespace ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900

set_option autoImplicit false

def agreement : ℕ := 180_413
def wordDegree : ℕ := 131_071
def tangentCost : ℕ := agreement - wordDegree - 1

theorem tangentCost_exact : tangentCost = 49_341 := by
  norm_num [tangentCost, agreement, wordDegree]

theorem four_reserve_plus_four_curvature_weights :
    4 * (agreement - wordDegree + 2) + 4 * (wordDegree - 2) =
      4 * agreement := by
  norm_num [agreement, wordDegree]

theorem order14_slack_exact :
    4 * agreement - 14 * tangentCost = 30_878 := by
  norm_num [agreement, tangentCost, wordDegree]

theorem order14_still_forced :
    14 * tangentCost < 4 * agreement := by
  norm_num [agreement, tangentCost, wordDegree]

theorem order15_first_unforced :
    4 * agreement < 15 * tangentCost := by
  norm_num [agreement, tangentCost, wordDegree]

theorem order15_deficit_exact :
    15 * tangentCost - 4 * agreement = 18_463 := by
  norm_num [agreement, tangentCost, wordDegree]

end ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900

#print axioms ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900.order14_still_forced
#print axioms ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900.order15_first_unforced
