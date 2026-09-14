import K0SRTinyContactCore6900
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The literal SR / R^2 / R^3 connection seam

The next complete-contact Spencer edge couples the three high shape groups
in the ordered m8 attribution.  The boundary identity records separately
that SR creates kernel relations, not a new pointwise boundary coordinate.
-/

namespace ProximityPrize.SubmissionLower.K0SRR2R3SymbolicSeam6900

open Polynomial
open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

theorem localConnection_mul (P Q : FlatContact K) :
    localConnection (P * Q) =
      localConnection P * Q + P * localConnection Q := by
  simp [localConnection]
  ring

theorem localConnection_localR :
    localConnection (localR (K := K)) = 2 * localS := by
  simp [localConnection, localS, localT, localR]

theorem localConnection_localZ :
    localConnection (localZ (K := K)) = 0 := by
  simp [localConnection, localS, localT, localZ]

theorem localConnection_contactedY (u0 u1 : K) :
    localConnection (contactedY (K := K) u0 u1) = localR := by
  simp [localConnection, contactedY, eps, localS, localT, localR,
    localZ]
  ring

theorem localConnection_mul_four
    (P Q R W : FlatContact K) :
    localConnection (P * Q * R * W) =
      localConnection P * Q * R * W +
      P * localConnection Q * R * W +
      P * Q * localConnection R * W +
      P * Q * R * localConnection W := by
  rw [localConnection_mul, localConnection_mul, localConnection_mul]
  ring

theorem localConnection_pow_succ
    (P : FlatContact K) (n : Nat) :
    localConnection (P ^ (n + 1)) =
      ((n + 1 : Nat) : K) • (P ^ n * localConnection P) := by
  induction n with
  | zero => simp [localConnection]
  | succ n ih =>
      rw [pow_succ, localConnection_mul, ih]
      simp only [Nat.cast_add, Nat.cast_one,
        MvPolynomial.smul_eq_C_mul]
      rw [pow_succ]
      simp only [map_add, map_one]
      ring

theorem localConnection_pow_of_eq_zero
    (P : FlatContact K) (hP : localConnection P = 0) (n : Nat) :
    localConnection (P ^ n) = 0 := by
  induction n with
  | zero => simp [localConnection]
  | succ n ih => simp [pow_succ, localConnection_mul, ih, hP]

/-- Literal `Y*R^2 -> R^3 + 4*S*R` connection, including X lowering. -/
theorem localConnection_raw_YR2_to_R3SR
    (x u0 u1 : K) (a y z : Nat) :
    localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 (y + 1) 2 z) =
      ((a + 1 : Nat) : K) •
          rawContactColumn x u0 u1 a 0 (y + 1) 2 z +
        ((y + 1 : Nat) : K) •
          rawContactColumn x u0 u1 (a + 1) 0 y 3 z +
        rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 1 z := by
  simp only [rawContactColumn, pow_zero, mul_one]
  rw [localConnection_mul_four]
  rw [localConnection_pow_succ
    (MvPolynomial.C x + eps (K := K)) a]
  rw [localConnection_pow_succ (contactedY u0 u1) y]
  have hR2 : localConnection (localR (K := K) ^ 2) =
      4 * localS * localR := by
    rw [show localR (K := K) ^ 2 = localR * localR by ring]
    rw [localConnection_mul, localConnection_localR]
    ring
  rw [hR2]
  rw [localConnection_pow_of_eq_zero (localZ (K := K))
    localConnection_localZ z]
  have hX :
      localConnection (MvPolynomial.C x + eps (K := K)) = 1 := by
    simp [localConnection, eps, localS, localT]
  rw [hX, localConnection_contactedY]
  simp only [MvPolynomial.smul_eq_C_mul,
    mul_one, mul_zero, add_zero]
  ring

/-- The first capacity-crossing m8 band, `S*R*Y^6`. -/
theorem m8_localConnection_Y6R2_to_Y5R3_Y6SR
    (x u0 u1 : K) (a z : Nat) :
    localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 6 2 z) =
      ((a + 1 : Nat) : K) •
          rawContactColumn x u0 u1 a 0 6 2 z +
        (6 : K) • rawContactColumn x u0 u1 (a + 1) 0 5 3 z +
        rawContactColumn x u0 u1 (a + 1) 1 6 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 6 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 6 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 6 1 z := by
  simpa using localConnection_raw_YR2_to_R3SR
    (K := K) x u0 u1 a 5 z

theorem rawShapeLegal_YR2_to_R3SR
    (D w L B sCap U a y z : Nat) (hw : 3 ≤ w)
    (hB : 3 ≤ B) (hs : 1 ≤ sCap)
    (hlegal : rawShapeLegal D w L B sCap U
      (a + 1) 0 (y + 1) 2 z) :
    rawShapeLegal D w L B sCap U a 0 (y + 1) 2 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 0 y 3 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 1 (y + 1) 1 z := by
  unfold rawShapeLegal at hlegal ⊢
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    Nat.mul_succ] at hlegal ⊢
  omega

theorem dual_localConnection_raw_YR2_to_R3SR
    (ell : Module.Dual K (FlatContact K))
    (x u0 u1 : K) (a y z : Nat) :
    ell (localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 (y + 1) 2 z)) =
      ((a + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 a 0 (y + 1) 2 z) +
        ((y + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 (a + 1) 0 y 3 z) +
        (4 : K) *
          ell (rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 1 z) := by
  rw [localConnection_raw_YR2_to_R3SR]
  simp
  ring

/-- SR has no new pointwise boundary direction: it is the matching R/S/base
inclusion--exclusion row. -/
theorem rawBoundaryScalar_SR_inclusion_exclusion
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K)
    (y z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 1 y 1 z =
      S0 * rawBoundaryScalar S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 0 y 1 z +
      R0 * rawBoundaryScalar S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 1 y 0 z -
      S0 * R0 * rawBoundaryScalar S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 0 y 0 z := by
  simp [rawBoundaryScalar]
  ring

theorem rawBoundaryRHS_SR_inclusion_exclusion
    (xi S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K)
    (y z : Nat) (p : K[X]) :
    rawBoundaryRHS xi S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 1 y 1 z p =
      S0 * rawBoundaryRHS xi S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 0 y 1 z p +
      R0 * rawBoundaryRHS xi S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 1 y 0 z p -
      S0 * R0 * rawBoundaryRHS xi S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ 0 y 0 z p := by
  simp only [rawBoundaryRHS, rawBoundaryScalar_SR_inclusion_exclusion]
  ring

#print axioms localConnection_raw_YR2_to_R3SR
#print axioms m8_localConnection_Y6R2_to_Y5R3_Y6SR
#print axioms rawShapeLegal_YR2_to_R3SR
#print axioms dual_localConnection_raw_YR2_to_R3SR
#print axioms rawBoundaryScalar_SR_inclusion_exclusion
#print axioms rawBoundaryRHS_SR_inclusion_exclusion

end


end ProximityPrize.SubmissionLower.K0SRR2R3SymbolicSeam6900
