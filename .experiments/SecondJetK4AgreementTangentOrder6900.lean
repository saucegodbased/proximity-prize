import ProximityPrize.Benchmark.TargetLower

/-!
Corrected arithmetic for the canonical agreement-tangent order in the
target-positive `(148,64,30,200,5465,4,5)` second-jet profile.  Four units of
reserve plus four curvature weights already pay the four-unit contact loss;
they are not fresh directional slack.
-/

namespace ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900

set_option autoImplicit false

def agreement : ℕ := 180_413
def wordDegree : ℕ := 131_071
def tangentCost : ℕ := agreement - wordDegree - 1
def multiplicity : ℕ := 148
def postD4RootDegree : ℕ := (multiplicity - 4) * agreement
def endpointDegree : ℕ := postD4RootDegree - 1

theorem tangentCost_exact : tangentCost = 49_341 := by
  norm_num [tangentCost, agreement, wordDegree]

theorem four_reserve_plus_four_curvature_weights :
    4 * (agreement - wordDegree + 2) + 4 * (wordDegree - 2) =
      4 * agreement := by
  norm_num [agreement, wordDegree]

theorem postD4RootDegree_exact : postD4RootDegree = 25_979_472 := by
  norm_num [postD4RootDegree, multiplicity, agreement]

theorem endpointDegree_exact : endpointDegree = 25_979_471 := by
  norm_num [endpointDegree, postD4RootDegree, multiplicity, agreement]

theorem endpoint_still_root_forced : endpointDegree < postD4RootDegree := by
  norm_num [endpointDegree, postD4RootDegree, multiplicity, agreement]

/-- One agreement-tangent replacement can add `tangentCost` to the X degree,
so the sharp source endpoint is already outside the strict root-count range. -/
theorem orderOne_first_unforced :
    ¬ (endpointDegree + tangentCost < postD4RootDegree) := by
  norm_num [endpointDegree, postD4RootDegree, multiplicity, agreement,
    tangentCost, wordDegree]

theorem orderOne_overshoot_exact :
    endpointDegree + tangentCost - postD4RootDegree = 49_340 := by
  norm_num [endpointDegree, postD4RootDegree, multiplicity, agreement,
    tangentCost, wordDegree]

end ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900

#print axioms ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900.endpoint_still_root_forced
#print axioms ProximityPrize.SubmissionLower.SecondJetK4AgreementTangentOrder6900.orderOne_first_unforced
