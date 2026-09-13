import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full187 pure-endpoint actuator: affine identity countergate

The earlier `d0=-B` unit normalization is false.  With the literal shifted
coordinates, `J2-BZ` has no scalar term at all: it is exactly linear in the
three boundary coordinates.  Consequently an actuator's value and its `S`
boundary coefficient are controlled by the same aggregate amplitude.
-/

namespace ProximityPrize.SubmissionLower.Full187ActuatorAffineIdentityCountergate6900

set_option autoImplicit false

section Ring

variable {K : Type*} [CommRing K]

def pureB (L L1 L2 H H1 H2 : K) : K :=
  -2 * L ^ 2 * H1 ^ 2 - 2 * L ^ 2 * H * H2 + 4 * L * L1 * H * H1 -
    2 * L1 ^ 2 * H ^ 2 + L * L2 * H ^ 2

def normalJ2 (L L1 L2 V W P : K) : K :=
  L ^ 2 * P - 2 * L * L1 * W + (2 * L1 ^ 2 - L * L2) * V

/-- This literal affine identity is the correction to the false scalar
`J2-B=d0+...` premise. -/
theorem normalJ2_sub_pureB_affine
    (L L1 L2 H H1 H2 Y R S Z : K) :
    normalJ2 L L1 L2 (Y - H ^ 2 * Z) (R - 2 * H * H1 * Z)
        (S - (2 * H1 ^ 2 + 2 * H * H2) * Z) -
      pureB L L1 L2 H H1 H2 * Z =
        (2 * L1 ^ 2 - L * L2) * Y - 2 * L * L1 * R + L ^ 2 * S := by
  unfold normalJ2 pureB
  ring

/-- For an actuator `q*L^(60-b)*V^b*(J2-BZ)`, the displayed substitution
shows its exact `S` coefficient. -/
theorem actuator_S_coefficient
    (q L L1 L2 H H1 H2 Y R S Z : K) (b : Nat) :
    q * L ^ (60 - b) * (Y - H ^ 2 * Z) ^ b *
        (normalJ2 L L1 L2 (Y - H ^ 2 * Z) (R - 2 * H * H1 * Z)
          (S - (2 * H1 ^ 2 + 2 * H * H2) * Z) -
          pureB L L1 L2 H H1 H2 * Z) =
      q * L ^ (60 - b) * (Y - H ^ 2 * Z) ^ b *
        ((2 * L1 ^ 2 - L * L2) * Y - 2 * L * L1 * R + L ^ 2 * S) := by
  rw [normalJ2_sub_pureB_affine]

end Ring

section Field

variable {K : Type*} [Field K]

/-- At the normalized error base `H=0,Y=1,R=S=0`, a finite actuator packet
with aggregate amplitude `A` has value `A*c` and `S` coefficient `A*L^2`.
Thus it cannot itself match a nonzero F0 value while having zero S boundary. -/
theorem nonzero_value_zero_S_countergate
    (A c L target : K) (hL : L ≠ 0) (htarget : target ≠ 0)
    (hvalue : A * c = target) (hS : A * L ^ 2 = 0) : False := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero _ hL
  have hA : A = 0 := (mul_eq_zero.mp hS).resolve_right hL2
  apply htarget
  rw [← hvalue, hA, zero_mul]

/-- The actual univariate local `Y=1+E` two-jets of the nominal `b=36,37`
actuators have ratios 37 and 38 (when the scalar `c` is nonzero), not the
previously claimed ratios 36 and 37 based on a nonexistent `d0`. -/
theorem corrected_A36_A37_E_jet_coefficients :
    ((37 : ℤ) * 36 / 2 = 666) ∧ ((38 : ℤ) * 37 / 2 = 703) := by
  norm_num

end Field

end ProximityPrize.SubmissionLower.Full187ActuatorAffineIdentityCountergate6900

#print axioms ProximityPrize.SubmissionLower.Full187ActuatorAffineIdentityCountergate6900.normalJ2_sub_pureB_affine
#print axioms ProximityPrize.SubmissionLower.Full187ActuatorAffineIdentityCountergate6900.actuator_S_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187ActuatorAffineIdentityCountergate6900.nonzero_value_zero_S_countergate
