import K0RawRSConnectionTranspose6900
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.NormNum

/-!
# Locator-adic/Hasse cap-seam audit for k0

The useful falling-factorial basis is the basis in powers of the agreement
locator, not the ordinary consecutive-integer basis.  This file records the
source-side fact needed before such a basis can be used: lowering one raw
active exponent and multiplying its coefficient by a polynomial no larger
than the released weight preserves *every* literal source cap.

It also records the exact target partial-block arithmetic.  The degree-w
anchor interpolant and the degree-(w+1) anchor locator have carries of widths
23049 and 23050, exactly the partial blocks of `S*Y^47` and `S*Y^46*R`.
An arbitrary degree-(g-1) interpolant still leaves the 49341-wide tail.
-/

namespace ProximityPrize.SubmissionLower.K0FallingFactorialHasseSeamAudit6900

open K0RawRSConnectionTranspose6900

set_option autoImplicit false

/-- A degree-at-most-w coefficient can replace one Y factor without leaving
any of the five literal source caps.  This is the monomial statement behind
the legal triangular shear `Y -> Y + q(X)`, `deg q <= w`. -/
theorem rawShapeLegal_lowerY_addX
    (D w L B sCap U a s y r z d : Nat)
    (hy : 1 <= y) (hd : d <= w)
    (h : rawShapeLegal D w L B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U (a + d) s (y - 1) r z := by
  rcases h with ⟨hB, hsCap, hU, hL, hD⟩
  refine ⟨hB, hsCap, by omega, by omega, ?_⟩
  have hyEq : y - 1 + 1 = y := Nat.sub_add_cancel hy
  have hweight : w * (y - 1) + w = w * y := by
    conv_rhs => rw [← hyEq]
    rw [Nat.mul_add]
    simp
  omega

/-- The derivative-weight companion: replacing one R by an X coefficient of
degree at most w-1 preserves the full source, including `2*S+R <= B`. -/
theorem rawShapeLegal_lowerR_addX
    (D w L B sCap U a s y r z d : Nat)
    (hr : 1 <= r) (hd : d <= w - 1)
    (h : rawShapeLegal D w L B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U (a + d) s y (r - 1) z := by
  rcases h with ⟨hB, hsCap, hU, hL, hD⟩
  refine ⟨by omega, hsCap, by omega, by omega, ?_⟩
  have hrEq : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hweight : (w - 1) * (r - 1) + (w - 1) = (w - 1) * r := by
    conv_rhs => rw [← hrEq]
    rw [Nat.mul_add]
    simp
  omega

/-- The curvature-weight companion: replacing one S by an X coefficient of
degree at most w-2 preserves the full source and releases two B-units. -/
theorem rawShapeLegal_lowerS_addX
    (D w L B sCap U a s y r z d : Nat)
    (hs : 1 <= s) (hd : d <= w - 2)
    (h : rawShapeLegal D w L B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U (a + d) (s - 1) y r z := by
  rcases h with ⟨hB, hsCap, hU, hL, hD⟩
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  have hsEq : s - 1 + 1 = s := Nat.sub_add_cancel hs
  have hweight : (w - 2) * (s - 1) + (w - 2) = (w - 2) * s := by
    conv_rhs => rw [← hsEq]
    rw [Nat.mul_add]
    simp
  omega

/-- Translating the passive coordinate by a scalar only lowers its exponent,
so it is harmless for every cap. -/
theorem rawShapeLegal_lowerZ
    (D w L B sCap U a s y r z z' : Nat)
    (hz : z' <= z)
    (h : rawShapeLegal D w L B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U a s y r z' := by
  unfold rawShapeLegal at h ⊢
  omega

def targetChar : Nat := 2130706433
def targetM : Nat := 47
def targetG : Nat := 180413
def targetW : Nat := 131071
def targetD : Nat := targetM * targetG

def targetCost (y r s : Nat) : Nat :=
  targetW * y + (targetW - 1) * r + (targetW - 2) * s

def targetWindow (y r s : Nat) : Nat := targetD - targetCost y r s

/-- Exact locator-adic decomposition of the three critical windows. -/
theorem critical_locator_blocks :
    targetWindow 48 0 1 = 11 * targetG + 72391 ∧
    targetWindow 47 0 1 = 12 * targetG + 23049 ∧
    targetWindow 46 1 1 = 12 * targetG + 23050 := by
  norm_num [targetWindow, targetCost, targetD, targetM, targetG, targetW]

/-- Multiplication of the top `S*Y^48` residual block by a degree-w anchor
interpolant makes a carry of exactly the receiving `S*Y^47` partial width;
using the degree-(w+1) locator makes exactly the connector partial width. -/
theorem anchor_and_locator_carries_are_exact :
    72391 + targetW - targetG = 23049 ∧
    72391 + (targetW + 1) - targetG = 23050 := by
  norm_num [targetW, targetG]

/-- A generic degree-(g-1) multiplier is not made legal by changing basis:
the adjacent-Y window still misses by exactly 49341 degrees. -/
theorem generic_interpolant_tail_is_exact :
    targetG - targetW - 1 = 49341 ∧
    targetWindow 48 0 1 - 1 + (targetG - 1) =
      (targetWindow 47 0 1 - 1) + 49341 := by
  norm_num [targetWindow, targetCost, targetD, targetM, targetG, targetW]

/-- The low anchor polynomial is on the legal endpoint, rather than one
degree outside it. -/
theorem degree_w_anchor_fits_on_last_degree :
    targetWindow 48 0 1 - 1 + targetW =
      targetWindow 47 0 1 - 1 := by
  norm_num [targetWindow, targetCost, targetD, targetM, targetG, targetW]

/-- Every factorial index which could appear in an ordinary-derivative
conversion of the complete X window is below the target characteristic.
The proposed Hasse implementation does not require this division, but the
fact rules out a hidden characteristic seam. -/
theorem complete_X_factorial_indices_below_characteristic
    (j : Nat) (hj : j < targetD) : j < targetChar := by
  norm_num [targetD, targetM, targetG, targetChar] at hj ⊢
  omega

variable {K : Type*} [Field K] [CharP K 2130706433]

/-- Consequently no factorial used by an optional ordinary-derivative
normalization vanishes in the actual field.  The locator-adic diagonal itself
uses Hasse coefficients and avoids factorial division entirely. -/
theorem complete_X_factorial_ne_zero
    (j : Nat) (hj : j < targetD) : (j.factorial : K) ≠ 0 := by
  intro hzero
  have hprime : Nat.Prime 2130706433 :=
    CharP.char_prime_of_ne_zero (R := K) (by norm_num)
  have hdvd : 2130706433 ∣ j.factorial :=
    (CharP.cast_eq_zero_iff K 2130706433 j.factorial).mp hzero
  have hchar_le : 2130706433 <= j := hprime.dvd_factorial.mp hdvd
  exact (not_le_of_gt
    (complete_X_factorial_indices_below_characteristic j hj)) hchar_le

#print axioms rawShapeLegal_lowerY_addX
#print axioms rawShapeLegal_lowerR_addX
#print axioms rawShapeLegal_lowerS_addX
#print axioms rawShapeLegal_lowerZ
#print axioms critical_locator_blocks
#print axioms anchor_and_locator_carries_are_exact
#print axioms generic_interpolant_tail_is_exact
#print axioms degree_w_anchor_fits_on_last_degree
#print axioms complete_X_factorial_indices_below_characteristic
#print axioms complete_X_factorial_ne_zero

end ProximityPrize.SubmissionLower.K0FallingFactorialHasseSeamAudit6900
