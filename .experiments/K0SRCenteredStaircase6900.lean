import K0SRTinyContactCore6900
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The centered `SR*Y^(m-2)` contact-zero staircase

This isolates the first algebraically natural SR seam suggested by the exact
capacity-positive m8 attribution.  It proves the literal epsilon
factorization, its three-X finite-difference realization, and legality of
the complete target m47 centered expansion.  It makes no global rank claim.
-/

namespace ProximityPrize.SubmissionLower.K0SRCenteredStaircase6900

open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

def anchoredY (u0 u1 : K) : FlatContact K :=
  MvPolynomial.C u0 + MvPolynomial.C u1 * localZ

def contactSlope : FlatContact K :=
  localR - eps * localS + eps ^ 2 * localT

theorem contactedY_sub_anchoredY (u0 u1 : K) :
    contactedY u0 u1 - anchoredY u0 u1 =
      eps * contactSlope := by
  simp [contactedY, anchoredY, contactSlope]
  ring

/-- After the second X finite difference, the centered `SR*Y^q` packet is
visibly divisible by `epsilon^(q+2)`. -/
theorem epsilon_sq_SR_centered_factor (u0 u1 : K) (q : Nat) :
    eps ^ 2 * localS * localR *
        (contactedY u0 u1 - anchoredY u0 u1) ^ q =
      eps ^ (q + 2) * localS * localR * contactSlope ^ q := by
  rw [contactedY_sub_anchoredY, mul_pow, pow_add]
  ring

/-- Convert the local epsilon square to three consecutive global-X shifts. -/
theorem eps_sq_mul_global_shift_pow (x : K) (a : Nat) :
    eps ^ 2 * (MvPolynomial.C x + eps) ^ a =
      (MvPolynomial.C x + eps) ^ (a + 2) -
        2 * MvPolynomial.C x *
          (MvPolynomial.C x + eps) ^ (a + 1) +
        MvPolynomial.C x ^ 2 *
          (MvPolynomial.C x + eps) ^ a := by
  simp only [pow_add, pow_two, pow_one]
  ring

/-- The first capacity-crossing centered band in the m8 receipt. -/
theorem m8_epsilon_sq_SR_Y6_centered_factor (u0 u1 : K) :
    eps ^ 2 * localS * localR *
        (contactedY u0 u1 - anchoredY u0 u1) ^ 6 =
      eps ^ 8 * localS * localR * contactSlope ^ 6 := by
  simpa using epsilon_sq_SR_centered_factor (K := K) u0 u1 6

/-- Target m47 analogue: a visible multiple of epsilon^47. -/
theorem m47_epsilon_sq_SR_Y45_centered_factor (u0 u1 : K) :
    eps ^ 2 * localS * localR *
        (contactedY u0 u1 - anchoredY u0 u1) ^ 45 =
      eps ^ 47 * localS * localR * contactSlope ^ 45 := by
  simpa using epsilon_sq_SR_centered_factor (K := K) u0 u1 45

theorem target_SR_Y45_X_width :
    47 * 180413 -
        (131071 * 45 + (131071 - 1) * 1 + (131071 - 2) * 1) =
      2319077 := by
  norm_num

/-- Coefficient-aware source check for every term in the global centered
expansion.  A degree-w anchor pays exactly for each removed Y factor, and
the complete three-X finite difference still fits. -/
theorem target_centered_SR_anchor_expansion_legal
    (a y z coefficientDegree shift : Nat)
    (ha : a < 2319075) (hyz : y + z ≤ 45)
    (hdegree : coefficientDegree ≤ (45 - y) * 131071)
    (hshift : shift ≤ 2) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      (a + coefficientDegree + shift) 1 y 1 z := by
  unfold rawShapeLegal
  norm_num
  omega

#print axioms m8_epsilon_sq_SR_Y6_centered_factor
#print axioms m47_epsilon_sq_SR_Y45_centered_factor
#print axioms eps_sq_mul_global_shift_pow
#print axioms target_centered_SR_anchor_expansion_legal

end


end ProximityPrize.SubmissionLower.K0SRCenteredStaircase6900
