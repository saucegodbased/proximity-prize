import Mathlib.Tactic.Ring

/-!
# Algebraic order-four repair of the centered terminal shell

This file proves only the parameter-free polynomial identities behind the
eight-generator `Lambda,V,J1` basis found by the exact F101 audit.  It makes
no target-scale existence claim.
-/

namespace ProximityPrize.SubmissionLower.F101N10OrderFourCenteredBasis6900

set_option autoImplicit false

variable {K : Type*} [CommRing K]

/-- Expanding the eight order-four cycles gives a triangular coefficient
system.  In particular, the five coefficients absent from the old
three-carrier ansatz are supplied, in order, by
`L*V*J1`, `L^2*V^2`, `L^2*J1`, `L^3*V`, and `L^4`. -/
theorem eight_cycle_triangular_assembly
    (p4 pA pC p11 p22 p01 p31 p40 L L1 V V1 Z : K) :
    p4 * V ^ 4 * Z ^ 3 +
        pA * V ^ 2 * (L * V1 - L1 * V) * Z ^ 4 +
        pC * L * V ^ 3 * Z ^ 4 +
        p11 * L * V * (L * V1 - L1 * V) * Z ^ 5 +
        p22 * L ^ 2 * V ^ 2 * Z ^ 5 +
        p01 * L ^ 2 * (L * V1 - L1 * V) * Z ^ 6 +
        p31 * L ^ 3 * V * Z ^ 6 +
        p40 * L ^ 4 * Z ^ 7 =
      p4 * V ^ 4 * Z ^ 3 +
        (pA * L) * V1 * V ^ 2 * Z ^ 4 +
        (pC * L - pA * L1) * V ^ 3 * Z ^ 4 +
        (p11 * L ^ 2) * V1 * V * Z ^ 5 +
        (p22 * L ^ 2 - p11 * L * L1) * V ^ 2 * Z ^ 5 +
        (p01 * L ^ 3) * V1 * Z ^ 6 +
        (p31 * L ^ 3 - p01 * L ^ 2 * L1) * V * Z ^ 6 +
        p40 * L ^ 4 * Z ^ 7 := by
  ring

/-- At the raw boundary `Y=0`, hence `V=-QZ` and `V1=-Q1 Z`,
the old three-cycle head and the five-cycle correction add to the exact
`Z^7` coefficient.  This is the cancellation that permits the two summands
to have larger X-degree than their legal coupled sum. -/
theorem generalized_boundary_zero_cancellation
    (p4 pA pC p11 p22 p01 p31 p40 L L1 Q Q1 Z : K) :
    p4 * (-Q * Z) ^ 4 * Z ^ 3 +
        pA * (-Q * Z) ^ 2 *
          (L * (-Q1 * Z) - L1 * (-Q * Z)) * Z ^ 4 +
        pC * L * (-Q * Z) ^ 3 * Z ^ 4 +
        p11 * L * (-Q * Z) *
          (L * (-Q1 * Z) - L1 * (-Q * Z)) * Z ^ 5 +
        p22 * L ^ 2 * (-Q * Z) ^ 2 * Z ^ 5 +
        p01 * L ^ 2 *
          (L * (-Q1 * Z) - L1 * (-Q * Z)) * Z ^ 6 +
        p31 * L ^ 3 * (-Q * Z) * Z ^ 6 +
        p40 * L ^ 4 * Z ^ 7 =
      ((p4 * Q ^ 4 - (pC * L - pA * L1) * Q ^ 3 -
          Q1 * (pA * L) * Q ^ 2) +
        (p40 * L ^ 4 - Q * (p31 * L ^ 3 - p01 * L ^ 2 * L1) +
          Q ^ 2 * (p22 * L ^ 2 - p11 * L * L1) -
          Q1 * (p01 * L ^ 3) + Q * Q1 * (p11 * L ^ 2))) * Z ^ 7 := by
  ring

#print axioms eight_cycle_triangular_assembly
#print axioms generalized_boundary_zero_cancellation

end ProximityPrize.SubmissionLower.F101N10OrderFourCenteredBasis6900
