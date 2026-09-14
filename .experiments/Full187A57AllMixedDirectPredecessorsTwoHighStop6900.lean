import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The two-high-row invariant does not make the direct A57 envelope onto

The projective endpoint cut forces every nonzero linear combination of the
two received-row interpolants to have degree at least `133120`.  This file
tests that exact new invariant against the strongest direct A57 predecessor
envelope.

Take

`U0 = X^133121`, `U1 = X^133120`.

Their high tails are linearly independent and every nonzero constant linear
combination has degree at least `133120`.  Even if every mixed monomial
`U0^k * U1^(t-k)`, `0 <= k <= t < 24`, is granted an independently
adjustable polynomial throughout the complete physical residual window, its
support ends before coefficient `255186`.  Thus the enlarged 300-channel
direct envelope still has a suffix defect of at least `6958`.

This is only a STOP for using the new projective degree invariant to promote
the direct Full187 A57 construction.  It says nothing about indirect sources
or a whole-family count theorem.
-/

namespace ProximityPrize.SubmissionLower.Full187A57AllMixedDirectPredecessorsTwoHighStop6900

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

variable {K : Type} [Field K]

/-- The monomial shift of `U0^k * U1^(t-k)` modulo the `262144`-node
cyclic coordinate ring. -/
def mixedShift (t k : Nat) : Nat :=
  (t * 133120 + k) % 262144

/-- The exact residual coefficient-window dimension depends only on the
total frozen received-row power. -/
def mixedPredecessorFringe (t : Nat) : Nat :=
  if t % 2 = 0 then 208036 + t else 76964 + t

/-- All 300 mixed direct windows end before coefficient `255186`. -/
theorem mixedShift_add_fringe_le
    (t k : Nat) (ht : t < 24) (hk : k ≤ t) :
    mixedShift t k + mixedPredecessorFringe t ≤ 255186 := by
  interval_cases t <;> interval_cases k <;>
    norm_num [mixedShift, mixedPredecessorFringe] at *

theorem one_mixed_direct_predecessor_missing_coefficient
    (t k : Nat) (ht : t < 24) (hk : k ≤ t) (V : K[X])
    (hV : V.natDegree < mixedPredecessorFringe t) :
    (X ^ mixedShift t k * V).coeff 255186 = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  calc
    (X ^ mixedShift t k * V).natDegree
        ≤ (X ^ mixedShift t k).natDegree + V.natDegree := natDegree_mul_le
    _ = mixedShift t k + V.natDegree := by simp
    _ < mixedShift t k + mixedPredecessorFringe t :=
      Nat.add_lt_add_left hV _
    _ ≤ 255186 := mixedShift_add_fringe_le t k ht hk

theorem coeff_finset_sum
    {A : Type*} (s : Finset A) (f : A → K[X]) (n : Nat) :
    (∑ x ∈ s, f x).coeff n = ∑ x ∈ s, (f x).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp [Finset.sum_insert, hx, ih, coeff_add]

/-- Even the direct sum in which all 300 mixed channels vary independently
misses coefficient `255186`. -/
theorem all_mixed_direct_predecessors_missing_coefficient
    (V : (x : Fin 24) → Fin (x.val + 1) → K[X])
    (hV : ∀ (t : Fin 24) (k : Fin (t.val + 1)),
      (V t k).natDegree < mixedPredecessorFringe t.val) :
    (∑ t : Fin 24, ∑ k : Fin (t.val + 1),
      X ^ mixedShift t.val k.val * V t k).coeff 255186 = 0 := by
  classical
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro t _ht
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro k _hk
  exact one_mixed_direct_predecessor_missing_coefficient
    t.val k.val t.isLt (by omega) (V t k) (hV t k)

/-- The hostile pair satisfies the exact projective degree invariant: every
nonzero constant linear combination has degree at least `133120`. -/
theorem hostile_pair_every_direction_high
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    133120 ≤
      (C a * X ^ 133121 + C b * X ^ 133120 : K[X]).natDegree := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := by simpa using hab
    simp [hb]
  · have htop :
        (C a * X ^ 133121 + C b * X ^ 133120 : K[X]).coeff 133121 = a := by
      simp
    have hcoeffNe :
        (C a * X ^ 133121 + C b * X ^ 133120 : K[X]).coeff 133121 ≠ 0 := by
      rw [htop]
      exact ha
    have hcoeff := le_natDegree_of_ne_zero hcoeffNe
    omega

end ProximityPrize.SubmissionLower.Full187A57AllMixedDirectPredecessorsTwoHighStop6900

#print axioms ProximityPrize.SubmissionLower.Full187A57AllMixedDirectPredecessorsTwoHighStop6900.all_mixed_direct_predecessors_missing_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187A57AllMixedDirectPredecessorsTwoHighStop6900.hostile_pair_every_direction_high
