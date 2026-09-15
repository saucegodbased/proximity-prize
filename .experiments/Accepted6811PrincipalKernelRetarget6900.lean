import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# Accepted 6811 principal kernels at the 6900 agreement threshold

This is a literal arithmetic audit, not a 6900 certificate.  It keeps the
three principal kernel shapes from accepted commit
`cdb451f13fdc6c84f5fe363e77ee13a89bd30974`, but replaces the per-coordinate
agreement `181284` by the exact 6900 value `180413`.

The total coefficient cap is the third argument of `coefficientCount`:
`274277`, `18992`, and `9281`, respectively.  This is separate from the
scalar-list arm audited in `MovingFiber6811ScalarProfileRetarget6900`, whose
literal source really does use the four arguments `(D,w,159,35)`.
-/

namespace ProximityPrize.SubmissionLower.Accepted6811PrincipalKernelRetarget6900

open RCN100 RCN119
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def targetAgreement : Nat := 180413

theorem target_A_coefficient_exact :
    coefficientCount (115 * targetAgreement) 131071 274277 35 =
      12985142848514811 := by
  rw [show 115 * targetAgreement = 158 * 131071 + 38277 by
    norm_num [targetAgreement]]
  rw [coefficientCount_eq_oneResidueCoefficientCount 158 38277 131071 274277 35
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem target_B_coefficient_exact :
    coefficientCount (134 * targetAgreement) 131071 18992 40 =
      1390207251526060 := by
  rw [show 134 * targetAgreement = 184 * 131071 + 58278 by
    norm_num [targetAgreement]]
  rw [coefficientCount_eq_oneResidueCoefficientCount 184 58278 131071 18992 40
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem target_T_coefficient_exact :
    coefficientCount (226 * targetAgreement) 131071 9281 70 =
      3277307768876838 := by
  rw [show 226 * targetAgreement = 311 * 131071 + 10257 by
    norm_num [targetAgreement]]
  rw [coefficientCount_eq_oneResidueCoefficientCount 311 10257 131071 9281 70
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem accepted_A_rank_exact : localRankBound 115 274277 35 = 50068355280 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem accepted_B_rank_exact : localRankBound 134 18992 40 = 5360249390 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem accepted_T_rank_exact : localRankBound 226 9281 70 = 12636646882 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- The very first principal kernel, A, already has negative target nullity.
Strict source existence would require one more coefficient beyond equality. -/
theorem target_A_source_deficit :
    coefficientCount (115 * targetAgreement) 131071 274277 35 <
        262144 * localRankBound 115 274277 35 /\
      262144 * localRankBound 115 274277 35 -
          coefficientCount (115 * targetAgreement) 131071 274277 35 =
        139976078005509 /\
      139976078005510 = 139976078005509 + 1 := by
  norm_num [target_A_coefficient_exact, accepted_A_rank_exact]

theorem target_B_source_deficit :
    coefficientCount (134 * targetAgreement) 131071 18992 40 <
        262144 * localRankBound 134 18992 40 /\
      262144 * localRankBound 134 18992 40 -
          coefficientCount (134 * targetAgreement) 131071 18992 40 =
        14949964566100 := by
  norm_num [target_B_coefficient_exact, accepted_B_rank_exact]

theorem target_T_source_deficit :
    coefficientCount (226 * targetAgreement) 131071 9281 70 <
        262144 * localRankBound 226 9281 70 /\
      262144 * localRankBound 226 9281 70 -
          coefficientCount (226 * targetAgreement) 131071 9281 70 =
        35313391358170 := by
  norm_num [target_T_coefficient_exact, accepted_T_rank_exact]

/-- Equivalent minimum rank improvement for the unchanged A coefficient
space: the local rank bound must fall by at least 533,966,363, facing strict
nullity. -/
theorem target_A_minimum_rank_reduction :
    262144 * (50068355280 - 533966363) < 12985142848514811 /\
      12985142848514811 ≤ 262144 * (50068355280 - 533966362) := by
  norm_num

#print axioms target_A_source_deficit
#print axioms target_B_source_deficit
#print axioms target_T_source_deficit
#print axioms target_A_minimum_rank_reduction

end ProximityPrize.SubmissionLower.Accepted6811PrincipalKernelRetarget6900
