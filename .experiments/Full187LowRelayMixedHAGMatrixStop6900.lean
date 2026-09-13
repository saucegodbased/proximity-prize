import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
Integer checks for the Full187 low mixed-H associated-graded STOP.
The executable polynomial matrix is in
`.experiments/full187_low_relay_mixed_h_ag_matrix_6900.py`.
No production theorem depends on this experiment.
-/

namespace Full187LowRelayMixedHAGMatrixStop6900

theorem agreement_contact_ledger :
    (60 - 57) + 57 = 60 ∧ (60 - 57) + (57 - 2) + 2 = 60 ∧
    (60 - 58) + 58 = 60 ∧ (60 - 58) + (58 - 2) + 2 = 60 ∧
    (60 - 59) + 59 = 60 ∧ (60 - 59) + (59 - 2) + 2 = 60 ∧
    (60 - 60) + 60 = 60 ∧ (60 - 60) + (60 - 2) + 2 = 60 ∧
    56 + 2 * 2 = 60 ∧ 54 + 3 * 2 = 60 := by
  norm_num

theorem weight_three_amplitudes :
    (32509 : ℤ) - 95816 + 94164 - 30856 + 1 - 1 = 1 ∧
    (57 : ℤ) * 32509 - 58 * 95816 + 59 * 94164 - 60 * 30856 + 60 - 60 = 1 ∧
    (1596 : ℤ) * 32509 - 1653 * 95816 + 1711 * 94164 - 1770 * 30856 + 1770 - 1770 = 0 ∧
    (29260 : ℤ) * 32509 - 30856 * 95816 + 32509 * 94164 - 34220 * 30856 + 34220 - 34220 = 0 := by
  norm_num

/- The fourth finite-difference functional kills the leading V-parts of
each of R57,R58,R59,R60,Phi2,Phi3.  Its target value is nonzero. -/
theorem weight_four_dual_values :
    (487635 : ℤ) - 32509 * 57 + 1653 * 1596 - 57 * 29260 + 395010 = 0 ∧
    (487635 : ℤ) - 32509 * 58 + 1653 * 1653 - 57 * 30856 + 424270 = 0 ∧
    (487635 : ℤ) - 32509 * 59 + 1653 * 1711 - 57 * 32509 + 455126 = 0 ∧
    (487635 : ℤ) - 32509 * 60 + 1653 * 1770 - 57 * 34220 + 487635 = 0 ∧
    (487635 : ℤ) - 32509 = 455126 ∧ (455126 : ℤ) ≠ 0 := by
  norm_num

/- Any exact match through weight four would give the following five moment
equations.  Phi2 and Phi3 have the same pure-V moments as exponent 60; their
H^3 J1 tails have a z factor and do not enter this x-only certificate. -/
theorem no_six_rows_match_weight_four
    (a57 a58 a59 a60 b2 b3 : ℤ)
    (h0 : a57 + a58 + a59 + a60 + b2 + b3 = 1)
    (h1 : 57 * a57 + 58 * a58 + 59 * a59 + 60 * a60 + 60 * b2 + 60 * b3 = 1)
    (h2 : 1596 * a57 + 1653 * a58 + 1711 * a59 + 1770 * a60 + 1770 * b2 + 1770 * b3 = 0)
    (h3 : 29260 * a57 + 30856 * a58 + 32509 * a59 + 34220 * a60 + 34220 * b2 + 34220 * b3 = 0)
    (h4 : 395010 * a57 + 424270 * a58 + 455126 * a59 + 487635 * a60 + 487635 * b2 + 487635 * b3 = 0) :
    False := by
  have h : (0 : ℤ) = 455126 := by
    linear_combination 487635 * h0 - 32509 * h1 + 1653 * h2 - 57 * h3 + h4
  norm_num at h

theorem field_characteristic_does_not_kill_certificate :
    (0 : ℤ) < 455126 ∧ 455126 < 2130706433 := by
  norm_num

end Full187LowRelayMixedHAGMatrixStop6900
