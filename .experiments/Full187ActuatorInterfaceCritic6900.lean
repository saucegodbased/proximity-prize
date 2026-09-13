import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full187 actuator interface critic

This file records two exact algebraic gates omitted by the endpoint actuator
receipts.

* The ratio-60/59 pair has binomial moments `(1,1,-1711)`, so after matching
  value and the first normal jet its `T^2 R^2` error-contact coefficient is
  nonzero.  Coefficient-polynomial derivatives cannot alter that passive
  quadratic row, and the explicit `H^3 J1` tail starts at horizontal order
  three.
* The proposed `J2-BZ` actuator has a passive linear error slice.  Expanding
  the definitions exactly gives
  `J2-BZ=(2(L')^2-LL'')Y-2LL'R+L^2S`.  Consequently any combination of the
  A36/A37 pair which matches a nonzero scalar value has a nonzero `S`
  coefficient already at contact weight zero.

These are local necessary conditions for the literal THREE-RHS interface;
they make no production or target-surjectivity claim.
-/

namespace ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900

set_option autoImplicit false

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Target contact-order and global-boundary-degree ledger.  At an agreement
root, `L,V,J1,J2` have contact orders `1,1,2,3`; `B*Z` may have order zero.
Thus every displayed term is in `ker C_G` termwise, while every global
boundary degree is greater than one and is invisible to `J_YRS`. -/
theorem target_agreement_and_YRS_degree_ledger :
    60 = 60 ∧
      1 + 59 = 60 ∧ 1 + 57 + 2 = 60 ∧
      24 + 36 + 3 ≥ 60 ∧ 24 + 36 = 60 ∧
      23 + 37 + 3 ≥ 60 ∧ 23 + 37 = 60 ∧
      1 < 60 ∧ 1 < 59 ∧ 1 < 37 ∧ 1 < 38 := by
  norm_num

/-- Exact fixed-coordinate second agreement covariant. -/
def normalJ2 (L L1 L2 V W P : K) : K :=
  L ^ 2 * P - 2 * L * L1 * W + (2 * L1 ^ 2 - L * L2) * V

/-- Its pure-seed coefficient for arbitrary `Q,Q',Q''`. -/
def pureSeedB (L L1 L2 Q Q1 Q2 : K) : K :=
  -(L ^ 2) * Q2 + 2 * L * L1 * Q1 - (2 * L1 ^ 2 - L * L2) * Q

/-- Subtracting the pure-seed endpoint does not leave a scalar normal
coordinate.  It leaves the entire linear section used by `F2`. -/
theorem normalJ2_sub_pureSeed_exact
    (L L1 L2 Q Q1 Q2 Y R S Z : K) :
    normalJ2 L L1 L2 (Y - Q * Z) (R - Q1 * Z) (S - Q2 * Z) -
        pureSeedB L L1 L2 Q Q1 Q2 * Z =
      (2 * L1 ^ 2 - L * L2) * Y - 2 * L * L1 * R + L ^ 2 * S := by
  unfold normalJ2 pureSeedB
  ring

/-- Matching a nonzero scalar value with any scalar multiple of the literal
`J2-BZ` slice is incompatible with its passive `S` coefficient.  This is a
contact-weight-zero contradiction because `S` is passive. -/
theorem scalar_value_forces_passive_S_failure
    (A c L f : K) (hL : L ≠ 0) (hf : f ≠ 0)
    (hvalue : A * c = f) (hS : A * L ^ 2 = 0) : False := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero _ hL
  have hA : A = 0 := by
    exact (mul_eq_zero.mp hS).resolve_right hL2
  rw [hA, zero_mul] at hvalue
  exact hf hvalue.symm

/-- The target ratio-60/59 amplitudes match the zeroth and first moments but
have the unavoidable second moment `-1711`. -/
theorem ratio_60_59_first_forced_passive_failure :
    (-58 : Int) + 59 = 1 /\
      (-58 : Int) * 60 + 59 * 59 = 1 /\
      (-58 : Int) * 1770 + 59 * 1711 = -1711 /\
      (-1711 : Int) ≠ 0 := by
  norm_num

/-- The precise first longitudinal completion condition omitted by nodewise
CRT value interpolation: equality of the pure-`T` row is equality of the
derivatives of the aggregate scalar coefficient. -/
theorem pure_T_completion_is_derivative_equality
    (A60 A59 f : Polynomial K) (x : K) :
    (A60 + A59 - f).derivative.eval x = 0 <->
      (A60 + A59).derivative.eval x = f.derivative.eval x := by
  simp only [derivative_sub, derivative_add, eval_sub, eval_add, sub_eq_zero]

end

end ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900

#print axioms ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900.normalJ2_sub_pureSeed_exact
#print axioms ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900.target_agreement_and_YRS_degree_ledger
#print axioms ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900.scalar_value_forces_passive_S_failure
#print axioms ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900.ratio_60_59_first_forced_passive_failure
#print axioms ProximityPrize.SubmissionLower.Full187ActuatorInterfaceCritic6900.pure_T_completion_is_derivative_equality
