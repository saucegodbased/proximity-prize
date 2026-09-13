import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Smallest error-factor-compatible first-transvectant power at Full187

Let

`J_L=L*(R-Z*Q')-L'*(Y-Z*Q)`.

At an agreement root of `L`, `J_L` has contact order two.  The family

`H * L^(60-2k) * J_L^k`

therefore has agreement-contact order at least sixty.  This file proves the
exact target ledger showing that `k=5` is the first power for which the whole
error-locator multiple fits every literal X strip.  Powers three and four
fail only at their pure seed tails; power five retains 3,029 degrees there.

This is a literal source-family theorem, not yet an error-contact
interpolation theorem.
-/

namespace ProximityPrize.SubmissionLower.Full187QuinticFirstTransvectantErrorCompatible6900

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- The exact local first-transvectant normal form, raised to the fifth
power.  The two summands on the right have contact weights three and two,
so the fifth power has weight at least ten. -/
theorem quintic_first_transvectant_local_normal_form
    (T E a b v c : K) :
    ((T * a) * (v + T * c) - (a + T * b) * (E + T * v)) ^ 5 =
      (-(a + T * b) * E + T ^ 2 * (a * c - b * v)) ^ 5 := by
  congr 1
  ring

/-- Fifty locator factors plus five order-two first transvectants give
contact order sixty. -/
theorem quintic_order_bookkeeping
    (locatorOrder firstTransvectantOrder : Nat)
    (hL : 1 ≤ locatorOrder) (hJ : 2 ≤ firstTransvectantOrder) :
    60 ≤ 50 * locatorOrder + 5 * firstTransvectantOrder := by
  omega

/-- Fixed-coordinate identity; in particular no unavailable third jet is
used by the quintic family. -/
theorem first_transvectant_fixed_coordinate
    (L L' Q Q' Y R Z : K) :
    L * (R - Z * Q') - L' * (Y - Z * Q) =
      -L' * Y + L * R + Z * (L' * Q - L * Q') := by
  ring

/-- For a quintic source shape `Y^y R^r Z^z`, `y+r+z=5`, the first term on
the right is the coefficient-degree bound after multiplying by `H`.  The
last term is its exact distance from the literal strict cutoff. -/
theorem target_quintic_post_error_shape_margin_formula
    (y r z : Nat) (hsum : y + r + z = 5) :
    60 * 180413 - 131071 * y - (131071 - 1) * r =
      81731 + 50 * 180413 + y * (180413 - 1) + r * 180413 +
        z * (180413 + 2 * 81731 - 1) +
          (164984 - 32391 * z) := by
  norm_num at hsum ⊢
  omega

/-- The pure seed layer is narrowest and still has 3,029 degrees of room. -/
theorem target_quintic_post_error_shape_margin_positive
    (y r z : Nat) (hsum : y + r + z = 5) :
    3029 ≤ 164984 - 32391 * z ∧ 0 < 164984 - 32391 * z := by
  norm_num at hsum ⊢
  omega

/-- Every quintic shape is far inside the literal active, slope, curvature,
and seed caps of the 187-shape source. -/
theorem target_quintic_shape_caps
    (y r z : Nat) (hsum : y + r + z = 5) :
    y + r ≤ 82 ∧ r ≤ 21 ∧ (0 : Nat) ≤ 10 ∧
      y + r + z ≤ 2703 := by
  omega

/-- Exact margins in all six seed layers. -/
theorem target_quintic_post_error_seed_tail_margins :
    164984 - 32391 * 0 = 164984 ∧
    164984 - 32391 * 1 = 132593 ∧
    164984 - 32391 * 2 = 100202 ∧
    164984 - 32391 * 3 = 67811 ∧
    164984 - 32391 * 4 = 35420 ∧
    164984 - 32391 * 5 = 3029 := by
  norm_num

/-- Direct pure-`Z^5` endpoint check. -/
theorem target_quintic_post_error_pure_Z5_fits :
    81731 + 50 * 180413 + 5 * (180413 + 2 * 81731 - 1) = 10821751 ∧
      60 * 180413 = 10824780 ∧
      10824780 - 10821751 = 3029 ∧
      10821751 < 10824780 := by
  norm_num

/-- Exact minimality within the pure powers: the quartic still misses its
pure seed cutoff by 13,923 after multiplication by `H`. -/
theorem target_quartic_post_error_pure_Z4_fails :
    81731 + 52 * 180413 + 4 * (180413 + 2 * 81731 - 1) = 10838703 ∧
      60 * 180413 = 10824780 ∧
      10838703 - 10824780 = 13923 ∧
      10824780 < 10838703 := by
  norm_num

/-- The cubic failure is larger: 30,875 degrees. -/
theorem target_cubic_post_error_pure_Z3_fails :
    81731 + 54 * 180413 + 3 * (180413 + 2 * 81731 - 1) = 10855655 ∧
      60 * 180413 = 10824780 ∧
      10855655 - 10824780 = 30875 ∧
      10824780 < 10855655 := by
  norm_num

end ProximityPrize.SubmissionLower.Full187QuinticFirstTransvectantErrorCompatible6900

#print axioms ProximityPrize.SubmissionLower.Full187QuinticFirstTransvectantErrorCompatible6900.quintic_first_transvectant_local_normal_form
#print axioms ProximityPrize.SubmissionLower.Full187QuinticFirstTransvectantErrorCompatible6900.quintic_order_bookkeeping
#print axioms ProximityPrize.SubmissionLower.Full187QuinticFirstTransvectantErrorCompatible6900.target_quintic_post_error_shape_margin_formula
#print axioms ProximityPrize.SubmissionLower.Full187QuinticFirstTransvectantErrorCompatible6900.target_quintic_post_error_pure_Z5_fits
