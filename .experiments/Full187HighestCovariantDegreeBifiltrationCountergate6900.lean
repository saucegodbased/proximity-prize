import Order2SourceBasisScaffold
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full187 highest-covariant-degree argument: bifiltration countergate

At an error node the three normal coordinates are related to the literal
local variables by an invertible affine triangular map.  This does not make
the order-60 contact truncation an ordinary symmetric-power truncation:
`R,S` have contact weight zero, whereas the independent displacement `E` in
the `V` direction has weight three.

Consequently, after first taking highest total covariant degree and then the
highest `V` exponent `b`, the top `E^b` coefficient is visible through only
`60-3b` horizontal Hasse layers.  It can force at most
`H^(60-3b) | p` (when `3b < 60`), not `H^60 | p`.

The explicit order-20 osculating polynomial below is the smallest exact
countergate on the constant-X error slice: it has a nonzero degree-21
coefficient but differs from the linear coordinate by contact weight 60.
This file refutes the proposed `H^60` coefficientwise induction.  It does
not assert that the surviving high-`b` family solves the complete literal
error-contact problem, where the `Z*R` and passive-seed terms remain.
-/

namespace ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900

open Polynomial
open scoped Matrix
open ProximityPrize.SubmissionLower.Order2SourceBasisScaffold

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- Linear part of the affine change `(E,R,S) -> (V,J1,J2)`. -/
def errorNormalLinearMatrix (L L1 L2 : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
     -L1, L, 0;
     2 * L1 ^ 2 - L * L2, -2 * L * L1, L ^ 2]

/-- Its determinant is `L^3`; thus the algebraic change really is invertible
at every error.  The countergate is about unequal contact weights, not a
singular coordinate transform. -/
theorem error_normal_linear_change_det (L L1 L2 : K) :
    (errorNormalLinearMatrix L L1 L2).det = L ^ 3 := by
  simp [errorNormalLinearMatrix, Matrix.det_fin_three]
  ring

/-- The independent `V` displacement costs three units of literal contact
weight.  Hence its `b`th power leaves only `60-3b` possible horizontal
orders, and none at all once `b >= 20`. -/
theorem visible_horizontal_layers_of_E_power
    (a b : Nat) (hvisible : a + 3 * b < 60) :
    b < 20 /\ a < 60 - 3 * b := by
  omega

theorem no_E_top_visibility_from_twenty (a b : Nat) (hb : 20 <= b) :
    ¬ a + 3 * b < 60 := by
  omega

/-- On the constant-X error slice, `V=1+E`.  This degree-21 polynomial has
a genuine high-degree term, but its difference from the desired linear
coordinate is exactly of contact weight 60. -/
theorem order_twenty_error_slice_osculation (E : K) :
    (1 + E) - (1 + E) * (1 - (1 + E)) ^ 20 - (1 + E) =
      -(1 + E) * E ^ 20 := by
  ring

def errorSliceV : Poly4 K := 1 + errorE K

def errorSliceOsculating : Poly4 K :=
  errorSliceV - errorSliceV * (1 - errorSliceV) ^ 20

theorem errorSliceOsculating_sub_linear :
    errorSliceOsculating (K := K) - errorSliceV =
      -(errorSliceV * errorE K ^ 20) := by
  unfold errorSliceOsculating errorSliceV
  ring

/-- The high-degree correction is erased by the literal strict order-60
contact truncation, even though its scalar coefficient is not zero. -/
theorem errorSliceOsculating_same_order_sixty_contact :
    contactTruncation K 60
        (errorSliceOsculating (K := K) - errorSliceV) = 0 := by
  rw [errorSliceOsculating_sub_linear]
  rw [map_neg]
  apply neg_eq_zero.mpr
  apply contactTruncation_eq_zero_of_minWeight_ge K 60 60
  · have hV : HasMinContactWeight 0 (errorSliceV (K := K)) := by
      intro d hd
      exact Nat.zero_le _
    have hE := (errorE_hasMinContactWeight K).pow 20
    have hmul := HasMinContactWeight.mul hV hE
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.zero_add] using hmul
  · omega

/-- Corrected error-factor charge for a lexicographically exposed
`V^b J1^c J2^d` coefficient. -/
def correctedForcedErrorPower (b : Nat) : Nat := 60 - 3 * b

/-- The source width before an error factor is
`16951*b+16952*c+16953*d`.  Already the pure `V^20` layer has no forced
error factor under the honest bifiltration and retains a positive width.
Thus the corrected induction leaves source-legal layers alive. -/
theorem pure_V_twenty_survives_corrected_charge :
    correctedForcedErrorPower 20 = 0 /\
      0 < 16951 * 20 - correctedForcedErrorPower 20 * 81731 /\
      16951 * 20 - correctedForcedErrorPower 20 * 81731 = 339020 := by
  norm_num [correctedForcedErrorPower]

/-- Even below the cutoff, a mixed legal layer survives: `b=18,c=21,d=0`
has locator exponent zero and remains positive after the only error power
visible from its exposed `E^18` coefficient. -/
theorem mixed_b18_c21_survives_corrected_charge :
    18 + 2 * 21 = 60 /\ correctedForcedErrorPower 18 = 6 /\
      16951 * 18 + 16952 * 21 - 6 * 81731 = 170724 := by
  norm_num [correctedForcedErrorPower]

/-! ## Independent multiplicative-projector gate -/

/-- In an `F0=L^59*Y` multiplicative correction, every positive projector
`Y` coefficient already violates the largest relevant Full187 strip (the
`Y^2` strip).  This remains true for X-dependent polynomial coefficients. -/
theorem target_F0_positive_projector_coefficient_not_legal
    (L c : K[X]) (j : Nat)
    (hL : L ≠ 0) (hc : c ≠ 0)
    (hLdegree : L.natDegree = 180413) (hj : 1 ≤ j) :
    ¬ (L ^ 59 * c).natDegree <
        60 * 180413 - 131071 * (j + 1) := by
  intro hlegal
  rw [Polynomial.natDegree_mul (pow_ne_zero _ hL) hc,
    Polynomial.natDegree_pow, hLdegree] at hlegal
  omega

/-- Once all positive active coefficients are killed, boundary value one
forces the projector to be the constant one. -/
theorem projector_eq_one_of_no_positive_coefficients
    (P : Polynomial K) (hzero : P.coeff 0 = 1)
    (hpositive : forall n, 1 ≤ n -> P.coeff n = 0) :
    P = 1 := by
  ext n
  cases n with
  | zero => simpa using hzero
  | succ n =>
      rw [hpositive (n + 1) (by omega)]
      rw [Polynomial.coeff_one]
      simp

/-- Hence polynomial polarization cannot simultaneously preserve boundary
value one, have no source-legal positive coefficient, and vanish at the
normalized error value one. -/
theorem no_polynomial_projector_after_head_elimination
    (P : Polynomial K) (hzero : P.coeff 0 = 1)
    (hpositive : forall n, 1 ≤ n -> P.coeff n = 0)
    (herror : P.eval 1 = 0) : False := by
  rw [projector_eq_one_of_no_positive_coefficients P hzero hpositive] at herror
  simp at herror

end

end ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900

#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.error_normal_linear_change_det
#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.visible_horizontal_layers_of_E_power
#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.order_twenty_error_slice_osculation
#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.errorSliceOsculating_same_order_sixty_contact
#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.pure_V_twenty_survives_corrected_charge
#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.target_F0_positive_projector_coefficient_not_legal
#print axioms ProximityPrize.SubmissionLower.Full187HighestCovariantDegreeBifiltrationCountergate6900.no_polynomial_projector_after_head_elimination
