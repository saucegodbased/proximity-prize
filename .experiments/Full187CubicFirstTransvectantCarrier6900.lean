import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A literal cubic agreement-contact carrier for Full187

This file records the first genuinely new carrier beyond the isolated
quadratic `T2` cascade.  If

`J_L = L * (R - Z*Q') - L' * (Y - Z*Q)`,

then `J_L` has contact order two at every zero of `L`.  Consequently

`L^54 * J_L^3`

has contact order at least sixty.  It uses only the literal cubic shapes
`Y^y R^r Z^z`, `y+r+z=3`, so it lies well inside the slope/curvature/active
shape box.  For the target direction `Q=H^2`, `deg H=81731`, every one of
its source coefficients also fits the strict X cutoffs.  The narrowest
coefficient is the pure `Z^3` tail and still has 50,856 degrees of room.

The final theorem records the remaining integration obstruction honestly:
an additional full error-locator factor of degree 81,731 would make that
same pure `Z^3` coefficient miss the cutoff by 30,875.  Thus the carrier is
a positive new literal source family, but a proof using it must cancel its
top seed tail before forcing every cubic coefficient through the error
locator.
-/

namespace ProximityPrize.SubmissionLower.Full187CubicFirstTransvectantCarrier6900

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- Exact local normal form for the first transvectant.  Here `T` is the
node parameter and `E` has contact weight three.  The right hand side is in
the weighted ideal `(E,T^2)`, proving contact order at least two. -/
theorem first_transvectant_local_normal_form
    (T E a b v c : K) :
    (T * a) * (v + T * c) - (a + T * b) * (E + T * v) =
      -(a + T * b) * E + T ^ 2 * (a * c - b * v) := by
  ring

/-- Cubing the preceding normal form is an exact order-six contact
identity.  It displays the four weighted pieces explicitly: `E^3`,
`E^2*T^2`, `E*T^4`, and `T^6`. -/
theorem first_transvectant_cube_local_normal_form
    (T E a b v c : K) :
    ((T * a) * (v + T * c) - (a + T * b) * (E + T * v)) ^ 3 =
      (-(a + T * b) * E) ^ 3 +
        3 * (-(a + T * b) * E) ^ 2 *
          (T ^ 2 * (a * c - b * v)) +
        3 * (-(a + T * b) * E) *
          (T ^ 2 * (a * c - b * v)) ^ 2 +
        (T ^ 2 * (a * c - b * v)) ^ 3 := by
  rw [first_transvectant_local_normal_form]
  ring

/-- Fixed-coordinate form of the carrier.  Its seed coefficient is the
Wronskian `L'*Q-L*Q'`; no third derivative or unavailable source operator
occurs. -/
theorem first_transvectant_fixed_coordinate
    (L L' Q Q' Y R Z : K) :
    L * (R - Z * Q') - L' * (Y - Z * Q) =
      -L' * Y + L * R + Z * (L' * Q - L * Q') := by
  ring

/-- Three-variable multinomial expansion used to read all ten literal
source shapes of the cubic carrier. -/
theorem cubic_three_term_expansion (u v z : K) :
    (u + v + z) ^ 3 =
      u ^ 3 + v ^ 3 + z ^ 3 +
      3 * u ^ 2 * v + 3 * u ^ 2 * z +
      3 * v ^ 2 * u + 3 * v ^ 2 * z +
      3 * z ^ 2 * u + 3 * z ^ 2 * v + 6 * u * v * z := by
  ring

/-- Exact target degree formula for a shape `Y^y R^r Z^z`, where
`y+r+z=3`.  The coefficient-degree bound is

`54g + y(g-1) + r*g + z(g+2e-1)`.

Its distance from the literal strict cutoff is
`148029-32391*z`. -/
theorem target_cubic_shape_margin_formula
    (y r z : Nat) (hsum : y + r + z = 3) :
    60 * 180413 - 131071 * y - (131071 - 1) * r =
      54 * 180413 + y * (180413 - 1) + r * 180413 +
        z * (180413 + 2 * 81731 - 1) +
          (148029 - 32391 * z) := by
  norm_num at hsum ⊢
  omega

/-- The pure-`Z^3` tail is the narrowest one, but all ten cubic shapes are
strictly legal. -/
theorem target_cubic_shape_margin_positive
    (y r z : Nat) (hsum : y + r + z = 3) :
    50856 ≤ 148029 - 32391 * z ∧ 0 < 148029 - 32391 * z := by
  norm_num at hsum ⊢
  omega

/-- Literal non-X caps for every shape in the cubic expansion. -/
theorem target_cubic_shape_caps
    (y r z : Nat) (hsum : y + r + z = 3) :
    y + r ≤ 82 ∧ r ≤ 21 ∧ (0 : Nat) ≤ 10 ∧
      y + r + z ≤ 2703 := by
  omega

/-- Endpoint widths, listed by seed exponent `z=0,1,2,3`. -/
theorem target_cubic_seed_tail_margins :
    148029 - 32391 * 0 = 148029 ∧
    148029 - 32391 * 1 = 115638 ∧
    148029 - 32391 * 2 = 83247 ∧
    148029 - 32391 * 3 = 50856 := by
  norm_num

/-- The exact pure-seed degree of the bare carrier and its positive source
margin. -/
theorem target_bare_pure_Z3_tail_fits :
    54 * 180413 + 3 * (180413 + 2 * 81731 - 1) = 10773924 ∧
      60 * 180413 = 10824780 ∧
      10824780 - 10773924 = 50856 ∧
      10773924 < 10824780 := by
  norm_num

/-- Honest integration gate: multiplying every cubic coefficient by the
full error locator does not fit the pure seed tail. -/
theorem target_error_factor_breaks_pure_Z3_tail :
    54 * 180413 + 3 * (180413 + 2 * 81731 - 1) + 81731 = 10855655 ∧
      60 * 180413 = 10824780 ∧
      10855655 - 10824780 = 30875 ∧
      10824780 < 10855655 := by
  norm_num

end ProximityPrize.SubmissionLower.Full187CubicFirstTransvectantCarrier6900

#print axioms ProximityPrize.SubmissionLower.Full187CubicFirstTransvectantCarrier6900.first_transvectant_local_normal_form
#print axioms ProximityPrize.SubmissionLower.Full187CubicFirstTransvectantCarrier6900.first_transvectant_cube_local_normal_form
#print axioms ProximityPrize.SubmissionLower.Full187CubicFirstTransvectantCarrier6900.target_cubic_shape_margin_formula
#print axioms ProximityPrize.SubmissionLower.Full187CubicFirstTransvectantCarrier6900.target_error_factor_breaks_pure_Z3_tail
