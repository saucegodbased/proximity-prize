import Order2SourceBasisScaffold
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-!
# Full187 first-passive unit minor

The high-`V` sparse discriminator is only relevant if its first passive
Hermite row occurs in the literal error chart.  This file isolates that
bridge.  The translated value coordinate is

`u + E + T*R - T^2/2*S`.

Consequently its `T*R` minor is exactly one.  An order-two control correction
(in particular the correction contributed by `Q=H^2` at a simple root of
`H`) starts with `T^2` and cannot change this minor.
-/

namespace ProximityPrize.SubmissionLower.Full187FirstPassiveUnitMinor6900

open ProximityPrize.SubmissionLower.Order2SourceBasisScaffold

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- Exact first-passive minor in the actual four-variable source chart. -/
theorem translated_value_first_passive_unit_minor (x u : K) :
    localSubstitution K x u (errorE K) -
        (MvPolynomial.C u + errorE K -
          halfZSquared K * curvatureS K) =
      contactZ K * slopeR K := by
  rw [localSubstitution_E]
  unfold contactY
  ring

/-- Any correction beginning in horizontal order two leaves the unit
`T*R` minor unchanged.  This is the abstract form needed for `Q=H^2`. -/
theorem first_passive_minor_survives_order_two_control
    (u E T R S C invTwo : K) :
    (u + E + T * R - invTwo * T ^ 2 * S - T ^ 2 * C) -
        (u + E - invTwo * T ^ 2 * S - T ^ 2 * C) =
      T * R := by
  ring

/-- Linearizing a high power in the passive variable produces the expected
unit-minor pivot `b*A^(b-1)*T`. -/
theorem coeff_one_high_power_first_passive
    (A T : K) (b : Nat) :
    ((Polynomial.C A + Polynomial.C T * Polynomial.X) ^ b).coeff 1 =
      (b : K) * A ^ (b - 1) * T := by
  have hcoeff := Polynomial.coeff_derivative
    ((Polynomial.C A + Polynomial.C T * Polynomial.X) ^ b) 0
  norm_num at hcoeff
  calc
    ((Polynomial.C A + Polynomial.C T * Polynomial.X) ^ b).coeff 1 =
        (Polynomial.derivative
          ((Polynomial.C A + Polynomial.C T * Polynomial.X) ^ b)).coeff 0 :=
      hcoeff.symm
    _ = (b : K) * A ^ (b - 1) * T := by
      rw [Polynomial.derivative_pow, Polynomial.coeff_zero_eq_eval_zero]
      simp

end

end ProximityPrize.SubmissionLower.Full187FirstPassiveUnitMinor6900

#print axioms ProximityPrize.SubmissionLower.Full187FirstPassiveUnitMinor6900.translated_value_first_passive_unit_minor
#print axioms ProximityPrize.SubmissionLower.Full187FirstPassiveUnitMinor6900.first_passive_minor_survives_order_two_control
#print axioms ProximityPrize.SubmissionLower.Full187FirstPassiveUnitMinor6900.coeff_one_high_power_first_passive
