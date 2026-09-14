import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

/-!
# Constant affine translation of the passive seed

The k0 raw source bounds the passive `Z` exponent only from above and is
downward-closed in that exponent.  These elementary lemmas isolate the exact
coordinate change used to move any boundary seed to `1` without changing the
affine anchor or consuming X/active/derivative degree.
-/

namespace ProximityPrize.SubmissionLower.K0AffineSeedTranslation6900

set_option autoImplicit false

/-- Re-centering the seed and compensating the constant anchor leaves the
literal affine expression unchanged. -/
theorem affine_anchor_translate {K : Type*} [CommRing K]
    (u0 u1 Z c : K) :
    (u0 + c * u1) + u1 * (Z - c) = u0 + u1 * Z := by
  ring

/-- Taking `c = gamma - 1` makes the translated boundary seed exactly one. -/
theorem translated_boundary_seed_one {K : Type*} [Ring K] (gamma : K) :
    gamma - (gamma - 1) = 1 := by
  simp [sub_eq_add_neg]

/-- The passive-total inequality is downward-closed in the seed exponent. -/
theorem passive_total_downward
    {y r s z z' L : ℕ} (hz : z' ≤ z) (hlegal : y + r + s + z ≤ L) :
    y + r + s + z' ≤ L := by
  exact (Nat.add_le_add_left hz (y + r + s)).trans hlegal

noncomputable section

open Polynomial

/-- Substitute `Z-c` for `Z`. -/
def seedTranslate {K : Type*} [CommRing K] (c : K) (p : K[X]) : K[X] :=
  p.comp (X - C c)

@[simp] theorem seedTranslate_X {K : Type*} [CommRing K] (c : K) :
    seedTranslate c X = X - C c := by
  simp [seedTranslate]

@[simp] theorem seedTranslate_C {K : Type*} [CommRing K] (c a : K) :
    seedTranslate c (C a) = C a := by
  simp [seedTranslate]

theorem seedTranslate_add {K : Type*} [CommRing K] (c : K) (p q : K[X]) :
    seedTranslate c (p + q) = seedTranslate c p + seedTranslate c q := by
  simp [seedTranslate]

theorem seedTranslate_mul {K : Type*} [CommRing K] (c : K) (p q : K[X]) :
    seedTranslate c (p * q) = seedTranslate c p * seedTranslate c q := by
  simp [seedTranslate]

/-- Constant translation is an automorphism; the inverse translates by the
opposite constant. -/
theorem seedTranslate_inverse {K : Type*} [CommRing K] (c : K) (p : K[X]) :
    seedTranslate (-c) (seedTranslate c p) = p := by
  simp [seedTranslate, Polynomial.comp_assoc]

/-- Evaluation commutes with translation in the expected direction. -/
theorem eval_seedTranslate {K : Type*} [CommRing K] (c z : K) (p : K[X]) :
    eval z (seedTranslate c p) = eval (z - c) p := by
  simp [seedTranslate, eval_comp]

#print axioms affine_anchor_translate
#print axioms translated_boundary_seed_one
#print axioms passive_total_downward
#print axioms seedTranslate_inverse
#print axioms eval_seedTranslate

end

end ProximityPrize.SubmissionLower.K0AffineSeedTranslation6900
