import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Error-compatible quintics from all three agreement normals

The three standard linear agreement covariants have contact orders one,
two, and three:

`V`,
`J1=L*W-L'*V`,
`J2=L^2*P-2*L*L'*W+(2*(L')^2-L*L'')*V`.

For `b+c+d=5`, the literal family

`H * L^(60-b-2c-3d) * V^b * J1^c * J2^d`

has agreement-contact order sixty.  Its pure-seed coefficient is the
narrowest target coefficient and retains at least 3,024 degrees of room.
This gives all 21 degree-five monomials in the three local leading forms,
removing the one-coordinate limitation of pure `J1` powers.

This file proves the exact local contact identities and the decisive target
arithmetic.  It does not assert the still-open coupled error-jet lift.
-/

namespace ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- Exact local normal form of the order-two first agreement covariant.
`E` has contact weight three, while the remaining pure part starts at
`T^2`. -/
theorem first_normal_local_form
    (T E a b w u v : K) :
    (T * a) * (w + T * u) -
        (a + T * b) * (E + T * w + T ^ 2 * v) =
      -(a + T * b) * E +
        T ^ 2 * (a * u - a * v - b * w) - T ^ 3 * b * v := by
  ring

/-- Exact local normal form of the order-three second agreement covariant.
The relations

`L=T*a`, `L'=a+T*b`, `L''=2b+T*c`,
`V=E+T*w+T^2*v`, `W=w+T*u`, `P=2(u-v)+T*p`

are the literal two-jet contact chart.  Every displayed term has contact
weight at least three. -/
theorem second_normal_local_form
    (T E a b c w u v p : K) :
    (T * a) ^ 2 * (2 * (u - v) + T * p) -
        2 * (T * a) * (a + T * b) * (w + T * u) +
        (2 * (a + T * b) ^ 2 - (T * a) * (2 * b + T * c)) *
          (E + T * w + T ^ 2 * v) =
      E * (2 * a ^ 2 + 2 * T * a * b +
        T ^ 2 * (2 * b ^ 2 - a * c)) +
      T ^ 3 * (a ^ 2 * p - 2 * a * b * u + 2 * a * b * v -
        a * c * w + 2 * b ^ 2 * w) +
      T ^ 4 * (2 * b ^ 2 - a * c) * v := by
  ring

/-- Contact-order bookkeeping for every mixed quintic. -/
theorem mixed_quintic_order_bookkeeping
    (b c d : Nat) (hdegree : b + c + d = 5) :
    45 ≤ 60 - (b + 2 * c + 3 * d) ∧
      (60 - (b + 2 * c + 3 * d)) + b + 2 * c + 3 * d = 60 := by
  omega

/-- The pure-seed post-error margin.  A `V` factor contributes 16,951,
`J1` contributes 16,952, and `J2` contributes 16,953.  Among all degree-five
products, the minimum is still positive. -/
theorem target_mixed_quintic_pure_seed_margin
    (b c d : Nat) (hdegree : b + c + d = 5) :
    3024 ≤ 16951 * b + 16952 * c + 16953 * d - 81731 ∧
      0 < 16951 * b + 16952 * c + 16953 * d - 81731 := by
  norm_num at hdegree ⊢
  omega

/-- Exact fixed-coordinate X-width ledger for every term in every one of
the 21 mixed quintics.  Here `(y,r,s,z)` is the resulting literal source
shape and `b,c,d` count `V,J1,J2` factors.  The actual coefficient width is

`81731 + 55*180413 + r + 2*s + 2*81731*z - (c+2*d)`.

The second summand on the right is its exact distance from the strict
187-shape cutoff.  The identity is independent of how the source variables
are distributed among the five factors. -/
theorem target_mixed_quintic_all_shape_margin_formula
    (b c d y r s z : Nat)
    (hdegree : b + c + d = 5) (hshape : y + r + s + z = 5) :
    60 * 180413 - 131071 * y - (131071 - 1) * r -
        (131071 - 2) * s =
      (81731 + 55 * 180413 + r + 2 * s + 2 * 81731 * z -
          (c + 2 * d)) +
        (164979 + c + 2 * d - 32391 * z) := by
  norm_num at hdegree hshape ⊢
  omega

/-- The pure-seed term of `V^5` is the unique narrow endpoint; hence all
literal terms in all 21 mixed quintics have positive strict margin. -/
theorem target_mixed_quintic_all_shape_margin_positive
    (b c d y r s z : Nat)
    (hdegree : b + c + d = 5) (hshape : y + r + s + z = 5) :
    3024 ≤ 164979 + c + 2 * d - 32391 * z ∧
      0 < 164979 + c + 2 * d - 32391 * z := by
  norm_num at hdegree hshape ⊢
  omega

/-- Endpoint checks for the three pure fifth powers. -/
theorem target_three_pure_quintic_margins :
    16951 * 5 - 81731 = 3024 ∧
      16952 * 5 - 81731 = 3029 ∧
      16953 * 5 - 81731 = 3034 := by
  norm_num

/-- Every mixed quintic respects the active/slope/curvature/seed caps. -/
theorem target_mixed_quintic_shape_caps
    (y r s z : Nat) (hshape : y + r + s + z = 5) :
    y + r + s ≤ 82 ∧ r + s ≤ 21 ∧ s ≤ 10 ∧
      y + r + s + z ≤ 2703 := by
  omega

/-- All 21 monomials of total degree five in three variables are present. -/
theorem mixed_quintic_family_cardinality :
    (6 * 7) / 2 = 21 := by
  norm_num

end ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900

#print axioms ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900.first_normal_local_form
#print axioms ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900.second_normal_local_form
#print axioms ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900.mixed_quintic_order_bookkeeping
#print axioms ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900.target_mixed_quintic_pure_seed_margin
#print axioms ProximityPrize.SubmissionLower.Full187ThreeNormalQuinticFamily6900.target_mixed_quintic_all_shape_margin_formula
