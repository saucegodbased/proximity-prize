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

open scoped BigOperators
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

/-- Any finite contact relation remains a contact relation after shifting
every participating raw column by one passive seed.  This statement is only
about the local contact polynomials; source legality of every successor is a
separate obligation below. -/
theorem rawContactRelation_seed_succ
    {I : Type*} (indices : Finset I) (coefficient : I → K)
    (x u0 u1 : K) (a s y r z : I → Nat)
    (hrelation :
      ∑ i ∈ indices, coefficient i •
        rawContactColumn x u0 u1 (a i) (s i) (y i) (r i) (z i) = 0) :
    ∑ i ∈ indices, coefficient i •
        rawContactColumn x u0 u1
          (a i) (s i) (y i) (r i) (z i + 1) = 0 := by
  simp_rw [rawContactColumn_seed_succ, ← smul_mul_assoc]
  rw [← Finset.sum_mul, hrelation, zero_mul]

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

/-- Conversely, every positive-seed column in the cap-`L+1` source is the
passive successor of a cap-`L` column.  This identifies the genuinely new
passive face as `Z` times the preceding cap face. -/
theorem rawShapeLegal_passive_pred
    (D w L B sCap U a s y r z : Nat) (hz : 0 < z)
    (hlegal : rawShapeLegal D w (L + 1) B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U a s y r (z - 1) := by
  unfold rawShapeLegal at hlegal ⊢
  omega

/-- A cap-`L+1` column is either already present at cap `L`, belongs to the
genuinely new active `z=0` face, or is a positive-seed successor of a cap-`L`
column.  This is the abstract disjoint ledger used by the active/passive
ablation. -/
theorem rawShapeLegal_cap_succ_cases
    (D w L B sCap U a s y r z : Nat)
    (hlegal : rawShapeLegal D w (L + 1) B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U a s y r z ∨ z = 0 ∨
      (0 < z ∧ rawShapeLegal D w L B sCap U a s y r (z - 1)) := by
  by_cases hold : s + y + r + z ≤ L
  · left
    unfold rawShapeLegal at hlegal ⊢
    omega
  · right
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      have hz : 0 < z := Nat.zero_lt_of_ne_zero hz0
      exact ⟨hz,
        rawShapeLegal_passive_pred D w L B sCap U a s y r z hz hlegal⟩

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
#print axioms rawContactRelation_seed_succ
#print axioms rawBoundaryScalar_seed_succ
#print axioms rawBoundaryRHS_seed_succ
#print axioms rawShapeLegal_seed_succ
#print axioms rawShapeLegal_passive_pred
#print axioms rawShapeLegal_cap_succ_cases
#print axioms passive_shift_detects_residual

end

end ProximityPrize.SubmissionLower.K0PassiveSeedProductRule6900
