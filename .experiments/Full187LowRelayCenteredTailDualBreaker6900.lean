import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Exact arithmetic for the centered K1/K2 W=4 dual breaker.
The complete matrix and literal strip enumeration are checked by the paired
Python receipt.  This file has no production dependencies.
-/

namespace ProximityPrize.SubmissionLower.Full187LowRelayCenteredTailDualBreaker6900

set_option autoImplicit false

section CenteredIdentities

variable {K : Type*} [CommRing K]

def normalJ1 (L L1 V W : K) : K := L * W - L1 * V
def normalJ2 (L L1 L2 V W P : K) : K :=
  L ^ 2 * P - 2 * L * L1 * W + (2 * L1 ^ 2 - L * L2) * V
def pureU (L L1 H H1 : K) : K := -2 * L * H1 + L1 * H
def pureB (L L1 L2 H H1 H2 : K) : K :=
  -2 * L ^ 2 * H1 ^ 2 - 2 * L ^ 2 * H * H2 + 4 * L * L1 * H * H1 -
    2 * L1 ^ 2 * H ^ 2 + L * L2 * H ^ 2

theorem centered_K1_literal
    (L L1 H H1 Y R Z : K) :
    normalJ1 L L1 (Y - H ^ 2 * Z) (R - 2 * H * H1 * Z) -
        H * pureU L L1 H H1 * Z = L * R - L1 * Y := by
  simp [normalJ1, pureU]
  ring

theorem centered_K2_literal
    (L L1 L2 H H1 H2 Y R S Z : K) :
    normalJ2 L L1 L2 (Y - H ^ 2 * Z) (R - 2 * H * H1 * Z)
        (S - (2 * H1 ^ 2 + 2 * H * H2) * Z) -
      pureB L L1 L2 H H1 H2 * Z =
        (2 * L1 ^ 2 - L * L2) * Y - 2 * L * L1 * R + L ^ 2 * S := by
  simp [normalJ2, pureB]
  ring

end CenteredIdentities

theorem agreement_base_contact_ledger :
    36 + 24 = 60 ∧ 35 + 25 = 60 ∧ 26 + 34 = 60 := by
  norm_num

theorem first_source_margin_ledger :
    (24 : ℤ) * 16951 - 393213 = 13611 ∧
    (23 : ℤ) * 16951 - 393213 = -3340 ∧
    (34 : ℤ) * 16951 - 573625 = 2709 ∧
    (33 : ℤ) * 16951 - 573625 = -14242 ∧
    10680099 < 10693710 ∧ 10693710 - 10680099 = 13611 ∧
    10691000 < 10693709 ∧ 10693709 - 10691000 = 2709 := by
  norm_num

theorem first_dual_breaker_values :
    58905 - 36 * 6545 = -176715 ∧
    14950 - 26 * 2300 = -44850 ∧
    (0 : ℤ) < 176715 ∧ 176715 < 2130706433 ∧
    (0 : ℤ) < 44850 ∧ 44850 < 2130706433 := by
  norm_num

theorem flat_pair_minor :
    58905 * (-26 : ℤ) - 14950 * (-36) = -993330 ∧
    (-993330 : ℤ) ≠ 0 := by
  norm_num

/- The seven rows are 1,x,x^2,x^3,z,x^4,xz.  This is the exact flat local
solution from the script; Phi3 is deliberately set to zero. -/
theorem flat_weight_four_augmented_solution :
    let a57 : ℚ := -31630313 / 2547
    let a58 : ℚ := 61544021 / 1698
    let a59 : ℚ := -9971236 / 283
    let a60 : ℚ := 2267502127 / 198666
    let p2 : ℚ := -590249 / 198666
    let k1 : ℚ := 421201 / 38205
    let k2 : ℚ := -1434349 / 110370
    (a57 + a58 + a59 + a60 + p2 + k1 + k2 = 1) ∧
    (57*a57 + 58*a58 + 59*a59 + 60*a60 + 60*p2 + 24*k1 + 34*k2 = 1) ∧
    (1596*a57 + 1653*a58 + 1711*a59 + 1770*a60 + 1770*p2 + 276*k1 + 561*k2 = 0) ∧
    (29260*a57 + 30856*a58 + 32509*a59 + 34220*a60 + 34220*p2 + 2024*k1 + 5984*k2 = 0) ∧
    (-a57-a58-a59-a60-2*p2 = 0) ∧
    (395010*a57 + 424270*a58 + 455126*a59 + 487635*a60 + 487635*p2 + 10626*k1 + 46376*k2 = 0) ∧
    ((-55 : ℚ)*a57 + (-56 : ℚ)*a58 + (-57 : ℚ)*a59 +
      (-58 : ℚ)*a60 + (-116 : ℚ)*p2 = 0) := by
  dsimp
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> norm_num

end ProximityPrize.SubmissionLower.Full187LowRelayCenteredTailDualBreaker6900
