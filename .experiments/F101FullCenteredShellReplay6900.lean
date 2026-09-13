import Mathlib.Tactic.Ring

/-!
# Algebraic endpoint identities for the full F101 centered-shell replay

The finite replay checks the F101 coefficients. This file records only the
parameter-free algebra which identifies its grade-one locator-normal frame
and its grade-seven Wronskian packet. It makes no target-scale, recurrence,
or source-legality assertion.
-/

namespace ProximityPrize.SubmissionLower.F101FullCenteredShellReplay6900

set_option autoImplicit false

variable {K : Type*} [CommRing K]

/-- The first centered locator-normal companion. -/
theorem first_normal_frame
    (L L1 V V1 : K) :
    L ^ 2 * (L * V1 - L1 * V) = L ^ 3 * V1 - L ^ 2 * L1 * V := by
  ring

/-- The second centered locator-normal companion. -/
theorem second_normal_frame
    (L L1 L2 V V1 V2 : K) :
    L * (L ^ 2 * V2 - 2 * L * L1 * V1 +
        (2 * L1 ^ 2 - L * L2) * V) =
      L ^ 3 * V2 - 2 * L ^ 2 * L1 * V1 +
        (2 * L * L1 ^ 2 - L ^ 2 * L2) * V := by
  ring

/-- The three grade-one covariants vanish on the centered pure tail. This is
the algebraic reason that a homogeneous carrier times such a frame cannot
create a pure tail by itself. -/
theorem normal_frame_vanishes_on_pure_tail
    (L L1 L2 : K) :
    (L ^ 3 * (0 : K),
      L ^ 2 * (L * (0 : K) - L1 * 0),
      L * (L ^ 2 * (0 : K) - 2 * L * L1 * 0 +
        (2 * L1 ^ 2 - L * L2) * 0)) = (0, 0, 0) := by
  simp

/-- The grade-seven centered Wronskian packet in expanded form. -/
theorem grade_seven_wronskian_assembly
    (A C c L L1 H V V1 Z : K) :
    V ^ 2 * Z ^ 3 *
        (c * V ^ 2 + (C * L - A * H * L1) * V * Z +
          A * H * L * V1 * Z) =
      V ^ 2 * Z ^ 3 *
        (c * V ^ 2 + C * L * V * Z +
          A * H * (L * V1 - L1 * V) * Z) := by
  ring

end ProximityPrize.SubmissionLower.F101FullCenteredShellReplay6900
