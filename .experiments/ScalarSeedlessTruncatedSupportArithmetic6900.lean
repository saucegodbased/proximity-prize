import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# Arithmetic boundary for the truncated seedless-scalar search at 6900

This file kernel-checks the small extremal frontier found by the companion
exact search and the two scalar-list budgets which straddle total protocol
capacity.  The reduction of all later truncated slopes to their first frontier
and the finite scan over multiplicities are documented separately; they are
not asserted as Lean theorems here.
-/

namespace ProximityPrize.SubmissionLower.ScalarSeedlessTruncatedSupportArithmetic6900

open RCN279 RCN285
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def targetAgreement : Nat := 180413
def targetW : Nat := 131071
def targetN : Nat := 262144
def targetGap : Nat := targetAgreement - targetW
def protocolCapacity : Nat := 274980728111395087

def scalarListBudget (L s : Nat) : Nat :=
  let capY := 1 + 2 * targetW * L
  let capR := targetW * (2 * s - 1)
  let regular := (targetN - targetW) * (capY * s + capR * L)
  let singular := (2 * s - 1) * L
  (regular + singular * targetGap) / targetGap + 1

theorem protocolCapacity_eq_field_capacity :
    protocolCapacity = 2130706433 ^ 6 / 2 ^ 128 := by
  norm_num [protocolCapacity]

theorem first_truncated_coefficient_exact :
    coefficientCount (2 * targetAgreement) targetW 2 2 = 1116392 := by
  decide +kernel

theorem first_truncated_rank_exact :
    localRankBound 2 2 2 = 6 := by
  decide +kernel

theorem first_truncated_deficit :
    coefficientCount (2 * targetAgreement) targetW 2 2 <
      targetN * localRankBound 2 2 2 ∧
    targetN * localRankBound 2 2 2 -
      coefficientCount (2 * targetAgreement) targetW 2 2 = 456472 := by
  norm_num [first_truncated_coefficient_exact, first_truncated_rank_exact,
    targetN]

theorem last_viable_budget_exact :
    scalarListBudget 849654 232379 = 274980714544786041 := by
  norm_num [scalarListBudget, targetN, targetW, targetGap, targetAgreement]

theorem first_unviable_budget_exact :
    scalarListBudget 849655 232379 = 274981038183248926 := by
  norm_num [scalarListBudget, targetN, targetW, targetGap, targetAgreement]

theorem capacity_straddle :
    scalarListBudget 849654 232379 < protocolCapacity ∧
    protocolCapacity < scalarListBudget 849655 232379 := by
  norm_num [last_viable_budget_exact, first_unviable_budget_exact,
    protocolCapacity]

#print axioms first_truncated_deficit
#print axioms capacity_straddle

end ProximityPrize.SubmissionLower.ScalarSeedlessTruncatedSupportArithmetic6900
