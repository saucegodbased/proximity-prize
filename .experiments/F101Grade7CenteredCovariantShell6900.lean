import Mathlib.Tactic.Ring

/-!
# Algebraic core of the F101 grade-seven centered shell

This file formalizes the parameter-free covariant identity exposed by the
exact finite factor probe.  It deliberately does not assert the target-scale
existence or weighted source legality of the coefficient polynomials.
-/

namespace ProximityPrize.SubmissionLower.F101Grade7CenteredCovariantShell6900

set_option autoImplicit false

variable {K : Type*} [CommRing K]

/-- The centered value and first-jet packet can be written using the
Wronskian `L * V1 - L1 * V`. -/
theorem centered_wronskian_assembly
    (A C c L L1 H V V1 Z : K) :
    V ^ 2 * Z ^ 3 *
        (c * V ^ 2 + (C * L - A * H * L1) * V * Z +
          A * L * H * V1 * Z) =
      V ^ 2 * Z ^ 3 *
        (c * V ^ 2 + C * L * V * Z +
          A * H * (L * V1 - L1 * V) * Z) := by
  ring

/-- After substituting the boundary-zero tails
`V=-H^2 Z`, `V1=-2 H H1 Z`, the apparently separate top coefficients
combine into the single cofactor `B-c H^2+2 A L H1`.  Parameter `k` is
`m-2`, avoiding truncated subtraction in the statement. -/
theorem boundary_zero_head_cancellation
    (A B c L H H1 Z : K) (k b : Nat) :
    (-H ^ 2 * Z) ^ k * Z ^ b *
        (c * (-H ^ 2 * Z) ^ 2 + B * (-H ^ 2 * Z) * Z +
          A * L * H * (-2 * H * H1 * Z) * Z) =
      (B - c * H ^ 2 + 2 * A * L * H1) *
        (-H ^ 2) ^ (k + 1) * Z ^ (k + b + 2) := by
  simp only [pow_succ, pow_add]
  ring

end ProximityPrize.SubmissionLower.F101Grade7CenteredCovariantShell6900
