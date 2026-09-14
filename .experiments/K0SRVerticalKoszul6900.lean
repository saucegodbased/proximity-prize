import K0SRTinyContactCore6900
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Vertical Koszul closure of the raw SR family

The derivation `partial_S + epsilon*partial_R` kills the literal contacted Y
coordinate and sends every SR column into the R/S prefix via one X shift.
-/

namespace ProximityPrize.SubmissionLower.K0SRVerticalKoszul6900

open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

def verticalKoszul (P : FlatContact K) : FlatContact K :=
  MvPolynomial.pderiv 1 P + eps * MvPolynomial.pderiv 3 P

theorem verticalKoszul_mul (P Q : FlatContact K) :
    verticalKoszul (P * Q) =
      verticalKoszul P * Q + P * verticalKoszul Q := by
  simp [verticalKoszul]
  ring

theorem verticalKoszul_mul_five
    (P Q R W Z : FlatContact K) :
    verticalKoszul (P * Q * R * W * Z) =
      verticalKoszul P * Q * R * W * Z +
      P * verticalKoszul Q * R * W * Z +
      P * Q * verticalKoszul R * W * Z +
      P * Q * R * verticalKoszul W * Z +
      P * Q * R * W * verticalKoszul Z := by
  rw [verticalKoszul_mul, verticalKoszul_mul,
    verticalKoszul_mul, verticalKoszul_mul]
  ring

theorem verticalKoszul_localS :
    verticalKoszul (localS (K := K)) = 1 := by
  simp [verticalKoszul, eps, localS]

theorem verticalKoszul_localR :
    verticalKoszul (localR (K := K)) = eps := by
  simp [verticalKoszul, eps, localR]

theorem verticalKoszul_localZ :
    verticalKoszul (localZ (K := K)) = 0 := by
  simp [verticalKoszul, eps, localZ]

theorem verticalKoszul_contactedY (u0 u1 : K) :
    verticalKoszul (contactedY (K := K) u0 u1) = 0 := by
  simp [verticalKoszul, contactedY, eps, localS, localT, localR,
    localZ]
  ring

theorem verticalKoszul_pow_of_eq_zero
    (P : FlatContact K) (hP : verticalKoszul P = 0) (n : Nat) :
    verticalKoszul (P ^ n) = 0 := by
  induction n with
  | zero => simp [verticalKoszul]
  | succ n ih => simp [pow_succ, verticalKoszul_mul, ih, hP]

/-- Exact triangular image of an SR column. -/
theorem verticalKoszul_raw_SR_to_R_and_shifted_S
    (x u0 u1 : K) (a y z : Nat) :
    verticalKoszul (rawContactColumn x u0 u1 a 1 y 1 z) =
      rawContactColumn x u0 u1 a 0 y 1 z +
      rawContactColumn x u0 u1 (a + 1) 1 y 0 z -
      x • rawContactColumn x u0 u1 a 1 y 0 z := by
  simp only [rawContactColumn, pow_zero, pow_one, mul_one]
  rw [verticalKoszul_mul_five]
  have hX : verticalKoszul (MvPolynomial.C x + eps (K := K)) = 0 := by
    simp [verticalKoszul, eps]
  rw [verticalKoszul_pow_of_eq_zero
    (MvPolynomial.C x + eps (K := K)) hX a]
  rw [verticalKoszul_localS]
  rw [verticalKoszul_pow_of_eq_zero (contactedY u0 u1)
    (verticalKoszul_contactedY u0 u1) y]
  rw [verticalKoszul_localR]
  rw [verticalKoszul_pow_of_eq_zero (localZ (K := K))
    verticalKoszul_localZ z]
  rw [pow_succ]
  simp only [MvPolynomial.smul_eq_C_mul, mul_zero, zero_mul,
    zero_add, add_zero, mul_one]
  ring

/-- The R/S image and its consecutive shift are all source-legal. -/
theorem rawShapeLegal_SR_vertical_closure
    (D w L B sCap U a y z : Nat) (hw : 2 ≤ w)
    (hlegal : rawShapeLegal D w L B sCap U a 1 y 1 z) :
    rawShapeLegal D w L B sCap U a 0 y 1 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 1 y 0 z ∧
      rawShapeLegal D w L B sCap U a 1 y 0 z := by
  unfold rawShapeLegal at hlegal ⊢
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    Nat.mul_succ] at hlegal ⊢
  omega

theorem dual_verticalKoszul_raw_SR_to_R_and_shifted_S
    (ell : Module.Dual K (FlatContact K))
    (x u0 u1 : K) (a y z : Nat) :
    ell (verticalKoszul (rawContactColumn x u0 u1 a 1 y 1 z)) =
      ell (rawContactColumn x u0 u1 a 0 y 1 z) +
      ell (rawContactColumn x u0 u1 (a + 1) 1 y 0 z) -
      x * ell (rawContactColumn x u0 u1 a 1 y 0 z) := by
  rw [verticalKoszul_raw_SR_to_R_and_shifted_S]
  simp

#print axioms verticalKoszul_raw_SR_to_R_and_shifted_S
#print axioms rawShapeLegal_SR_vertical_closure
#print axioms dual_verticalKoszul_raw_SR_to_R_and_shifted_S

end


end ProximityPrize.SubmissionLower.K0SRVerticalKoszul6900
