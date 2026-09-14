import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Four high Pascal contacts kill a denominator-only two-row dual

This is the algebraic core exposed by the exact literal chain
`(r,s,q)=(0,0,26)`, `Y={41,42}`.  For `W=1/E`, the high contacts
`41,43,45,47` yield short prefix duals `G0,...,G3`.  After clearing powers of
`E`, their Pascal directions are affine in the contact index, so consecutive
second differences give

`E^4*G2 - 2*E^2*G1 + G0 = 0` and
`E^4*G3 - 2*E^2*G2 + G1 = 0`.

Each identity makes its head divisible by `E^2`.  In the m69 degree range,
`deg(E^2)>=4302`, whereas the high-prefix dual caps are at most 3302, so both
heads vanish.  This file formalizes that rigidity step without computation.
-/

namespace ProximityPrize.SubmissionLower.M69LiteralPascalFourHighDenominatorOne6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- Three consecutive normalized high-contact encodings have zero second
difference after their denominator powers are aligned. -/
theorem three_encodings_pascal_second_difference
    {K : Type*} [Field K]
    (e x lambda0 lambda1 c g0 g1 g2 : K)
    (hx : x ≠ 0)
    (h0 : e ^ 53 * lambda0 = x * g0)
    (h1 : e ^ 51 * (lambda0 + c * lambda1) = x * g1)
    (h2 : e ^ 49 * (lambda0 + 2 * c * lambda1) = x * g2) :
    e ^ 4 * g2 - 2 * e ^ 2 * g1 + g0 = 0 := by
  apply mul_left_cancel₀ hx
  simp only [mul_zero]
  calc
    x * (e ^ 4 * g2 - 2 * e ^ 2 * g1 + g0) =
        e ^ 4 * (x * g2) - 2 * e ^ 2 * (x * g1) + x * g0 := by ring
    _ = e ^ 4 * (e ^ 49 * (lambda0 + 2 * c * lambda1)) -
          2 * e ^ 2 * (e ^ 51 * (lambda0 + c * lambda1)) +
          e ^ 53 * lambda0 := by rw [← h2, ← h1, ← h0]
    _ = 0 := by ring

/-- A short polynomial cannot be the head of the literal Pascal second
difference when the denominator has the m69 minimum degree. -/
theorem short_head_zero_of_pascal_second_difference
    {K : Type*} [Field K]
    (E G0 G1 G2 : K[X])
    (hEdegree : 2151 ≤ E.natDegree)
    (hG0degree : G0.natDegree < 3302)
    (hrecurrence : E ^ 4 * G2 - 2 * E ^ 2 * G1 + G0 = 0) :
    G0 = 0 := by
  have hE : E ≠ 0 := by
    intro hzero
    simp only [hzero, natDegree_zero] at hEdegree
    omega
  have hE2 : E ^ 2 ≠ 0 := pow_ne_zero 2 hE
  have hfactor : G0 = E ^ 2 * (2 * G1 - E ^ 2 * G2) := by
    calc
      G0 = -(E ^ 4 * G2 - 2 * E ^ 2 * G1) :=
        eq_neg_of_add_eq_zero_right hrecurrence
      _ = 2 * E ^ 2 * G1 - E ^ 4 * G2 := by ring
      _ = E ^ 2 * (2 * G1 - E ^ 2 * G2) := by ring
  by_contra hG0
  have hcofactor : 2 * G1 - E ^ 2 * G2 ≠ 0 := by
    intro hzero
    rw [hfactor, hzero, mul_zero] at hG0
    exact hG0 rfl
  have hdegree := natDegree_mul hE2 hcofactor
  have hE2degree : (E ^ 2).natDegree = 2 * E.natDegree := by
    rw [natDegree_pow]
  rw [hfactor, hdegree, hE2degree] at hG0degree
  omega

/-- The two consecutive second differences force both initial high duals to
vanish. -/
theorem first_two_short_duals_zero
    {K : Type*} [Field K]
    (E G0 G1 G2 G3 : K[X])
    (hEdegree : 2151 ≤ E.natDegree)
    (hG0degree : G0.natDegree < 3302)
    (hG1degree : G1.natDegree < 3300)
    (hrecurrence0 : E ^ 4 * G2 - 2 * E ^ 2 * G1 + G0 = 0)
    (hrecurrence1 : E ^ 4 * G3 - 2 * E ^ 2 * G2 + G1 = 0) :
    G0 = 0 ∧ G1 = 0 := by
  constructor
  · exact short_head_zero_of_pascal_second_difference
      E G0 G1 G2 hEdegree hG0degree hrecurrence0
  · exact short_head_zero_of_pascal_second_difference
      E G1 G2 G3 hEdegree (hG1degree.trans_le (by omega)) hrecurrence1

/-- Once the two short heads vanish, the first two high-contact encodings
kill both independent output covectors at every node where `E` is nonzero. -/
theorem output_dual_zero_of_four_high_data
    {I K : Type*} [Field K]
    (nodes : I → K) (E G0 G1 G2 G3 : K[X])
    (lambda0 lambda1 : I → K)
    (hEdegree : 2151 ≤ E.natDegree)
    (hG0degree : G0.natDegree < 3302)
    (hG1degree : G1.natDegree < 3300)
    (hrecurrence0 : E ^ 4 * G2 - 2 * E ^ 2 * G1 + G0 = 0)
    (hrecurrence1 : E ^ 4 * G3 - 2 * E ^ 2 * G2 + G1 = 0)
    (hErootfree : ∀ i, E.eval (nodes i) ≠ 0)
    (h21 : (21 : K) ≠ 0)
    (hencoding0 : ∀ i,
      E.eval (nodes i) ^ 53 * lambda0 i =
        nodes i * G0.eval (nodes i))
    (hencoding1 : ∀ i,
      E.eval (nodes i) ^ 51 *
          (lambda0 i + (21 : K)⁻¹ * lambda1 i) =
        nodes i * G1.eval (nodes i)) :
    ∀ i, lambda0 i = 0 ∧ lambda1 i = 0 := by
  obtain ⟨hG0, hG1⟩ := first_two_short_duals_zero
    E G0 G1 G2 G3 hEdegree hG0degree hG1degree
      hrecurrence0 hrecurrence1
  intro i
  have hfirst := hencoding0 i
  rw [hG0] at hfirst
  simp only [eval_zero, mul_zero] at hfirst
  have hlambda0 : lambda0 i = 0 :=
    (mul_eq_zero.mp hfirst).resolve_left (pow_ne_zero 53 (hErootfree i))
  have hsecond := hencoding1 i
  rw [hG1, hlambda0] at hsecond
  simp only [zero_add, eval_zero, mul_zero] at hsecond
  have hinvMul : (21 : K)⁻¹ * lambda1 i = 0 :=
    (mul_eq_zero.mp hsecond).resolve_left (pow_ne_zero 51 (hErootfree i))
  have hlambda1 : lambda1 i = 0 :=
    (mul_eq_zero.mp hinvMul).resolve_left (inv_ne_zero h21)
  exact ⟨hlambda0, hlambda1⟩

/-- Exact no-wrap arithmetic for both second differences throughout the
complete m69 denominator interval. -/
theorem literal_four_high_no_wrap_arithmetic :
    4 * 18414 + (3298 - 1) < 262144 ∧
    2 * 18414 + (3300 - 1) < 262144 ∧
    4 * 18414 + (3296 - 1) < 262144 ∧
    2 * 2151 > 3302 := by
  norm_num

#print axioms short_head_zero_of_pascal_second_difference
#print axioms first_two_short_duals_zero
#print axioms three_encodings_pascal_second_difference
#print axioms output_dual_zero_of_four_high_data
#print axioms literal_four_high_no_wrap_arithmetic

end
end ProximityPrize.SubmissionLower.M69LiteralPascalFourHighDenominatorOne6900
