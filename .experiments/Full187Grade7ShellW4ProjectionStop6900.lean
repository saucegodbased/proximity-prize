import Mathlib.Tactic.NormNum

/-! Arithmetic receipt for the grade-seven W4 projection/source ceilings. -/

namespace ProximityPrize.SubmissionLower.Full187Grade7ShellW4ProjectionStop6900

set_option autoImplicit false

theorem grade7_dual_minor :
    (367290 : ℤ) * (-57) - 395010 * (-56) = 1185030 ∧
    (1185030 : ℤ) ≠ 0 ∧ 1185030 < 2130706433 := by
  norm_num

theorem grade7_projected_solution :
    let a57 : ℚ := -5015 / 81
    let a58 : ℚ := 270928 / 1485
    let a59 : ℚ := -9853 / 55
    let a60 : ℚ := 4962214 / 84645
    let p2 : ℚ := -334 / 84645
    let v4 : ℚ := -3304 / 1485
    let v3 : ℚ := 272639 / 84645
    (a57+a58+a59+a60+p2+v4+v3 = 1) ∧
    (57*a57+58*a58+59*a59+60*a60+60*p2+4*v4+3*v3 = 1) ∧
    (1596*a57+1653*a58+1711*a59+1770*a60+1770*p2+6*v4+3*v3 = 0) ∧
    (29260*a57+30856*a58+32509*a59+34220*a60+34220*p2+4*v4+v3 = 0) ∧
    (-a57-a58-a59-a60-2*p2 = 0) ∧
    (395010*a57+424270*a58+455126*a59+487635*a60+487635*p2+v4 = 0) ∧
    ((-55 : ℚ)*a57+(-56)*a58+(-57)*a59+(-58)*a60+(-116)*p2 = 0) := by
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

theorem grade7_unconditional_source_ceiling_ledger :
    60*180413 - 8*81731 = 10170932 ∧
    60*180413 - 6*81731 = 10334394 ∧
    60*180413 - (131071-1) - 180413 - 5*81731 = 10104642 ∧
    60*180413 - 180413 - 7*81731 + 1 = 10072251 ∧
    56*180413 = 10103128 ∧ 57*180413 = 10283541 ∧
    10170932 - 10103128 = 67804 ∧ 10334394 - 10283541 = 50853 ∧
    10103128 - 10072251 = 30877 := by
  norm_num

end ProximityPrize.SubmissionLower.Full187Grade7ShellW4ProjectionStop6900
