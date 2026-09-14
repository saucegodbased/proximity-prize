import K0SRTinyContactCore6900
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Passive-seed product rule for the k0 normal repair

The controlled m8 discriminator shows that extending only the passive `Z`
reach repairs a rank-three boundary image to rank four.  This file isolates
the literal identities behind the proposed explanation.

Multiplying a raw column by `Z` preserves every contact relation because the
local contact operator treats `Z` as a passive coordinate.  At the new
boundary point, however, the gradient obeys the product rule

`grad (Z*f) = gamma * grad f + f * e_Z`.

After pairing with a boundary covector, the new term is exactly
`lambdaZ * f(boundary)`.  Thus a residual conormal with nonzero `Z`
coordinate is killed as soon as an old contact-kernel relation has nonzero
boundary value and its shifted support remains source-legal.

These are mechanism lemmas, not yet the target-uniform existence theorem for
that nonzero-value relation.
-/

namespace ProximityPrize.SubmissionLower.K0PassiveSeedProductRule6900

open K0SRTinyContactCore6900
open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

/-- Value of the non-`X` raw monomial at the boundary point. -/
def rawBoundaryValue
    (S0 Y0 R0 gamma : K) (s y r z : Nat) : K :=
  S0 ^ s * Y0 ^ y * R0 ^ r * gamma ^ z

/-- A passive seed shift is literally multiplication of the localized raw
column by the local `Z` coordinate. -/
theorem rawContactColumn_seed_succ
    (x u0 u1 : K) (a s y r z : Nat) :
    rawContactColumn x u0 u1 a s y r (z + 1) =
      rawContactColumn x u0 u1 a s y r z * localZ := by
  simp only [rawContactColumn, pow_succ]
  ring

/-- Scalar boundary product rule for one raw monomial.  The formula is valid
also at `z=0`; the zero coefficient in the old `Z` derivative removes the
otherwise awkward truncated subtraction. -/
theorem rawBoundaryScalar_seed_succ
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K)
    (s y r z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ s y r (z + 1) =
      gamma * rawBoundaryScalar S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ s y r z +
      lambdaZ * rawBoundaryValue S0 Y0 R0 gamma s y r z := by
  cases z with
  | zero =>
      simp [rawBoundaryScalar, rawBoundaryValue]
      ring
  | succ z =>
      simp only [rawBoundaryScalar, rawBoundaryValue, Nat.cast_add,
        Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      ring

/-- The same product rule including the arbitrary outer `X` polynomial
coefficient used by the boundary right-hand side. -/
theorem rawBoundaryRHS_seed_succ
    (xi S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K)
    (s y r z : Nat) (p : K[X]) :
    rawBoundaryRHS xi S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ s y r (z + 1) p =
      gamma * rawBoundaryRHS xi S0 Y0 R0 gamma
        lambdaS lambdaY lambdaR lambdaZ s y r z p +
      lambdaZ *
        (rawBoundaryValue S0 Y0 R0 gamma s y r z * p.eval xi) := by
  rw [rawBoundaryRHS, rawBoundaryRHS, rawBoundaryScalar_seed_succ]
  ring

/-- Raising the passive seed preserves source legality whenever the literal
passive cap has one unit of room.  All active and weighted caps are unchanged.
-/
theorem rawShapeLegal_seed_succ
    (D w L B sCap U a s y r z : Nat)
    (hlegal : rawShapeLegal D w L B sCap U a s y r z)
    (hroom : s + y + r + z < L) :
    rawShapeLegal D w L B sCap U a s y r (z + 1) := by
  unfold rawShapeLegal at hlegal ⊢
  omega

/-- Abstract last-line killer supplied by the passive product rule.  This is
the exact logical endpoint needed after a packet has confined compatible
boundary covectors to one line. -/
theorem passive_shift_detects_residual
    (gamma lambdaZ oldPair value shiftedPair : K)
    (hproduct : shiftedPair = gamma * oldPair + lambdaZ * value)
    (hold : oldPair = 0) (hlambdaZ : lambdaZ ≠ 0) (hvalue : value ≠ 0) :
    shiftedPair ≠ 0 := by
  rw [hproduct, hold, mul_zero, zero_add]
  exact mul_ne_zero hlambdaZ hvalue

#print axioms rawContactColumn_seed_succ
#print axioms rawBoundaryScalar_seed_succ
#print axioms rawBoundaryRHS_seed_succ
#print axioms rawShapeLegal_seed_succ
#print axioms passive_shift_detects_residual

end

end ProximityPrize.SubmissionLower.K0PassiveSeedProductRule6900
