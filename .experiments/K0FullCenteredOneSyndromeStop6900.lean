import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Full-centered pure carriers do not contain the literal F3 syndrome

This file isolates the coefficient-ring obstruction for the exact-G k=0
lower-6900 route.  The outer passive-seed coordinate is a genuine polynomial
variable; it is not completed or truncated adically.  Thus an affine
polynomial with nonzero constant coefficient need not be a unit.
-/

namespace ProximityPrize.SubmissionLower.K0FullCenteredOneSyndromeStop6900

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option Elab.async false

noncomputable section

variable {K I : Type*} [Field K]

/-- The contact-constant error trace of the full-centered factor, written in
the centered passive-seed coordinate. -/
def affineResidual (delta epsilon : K) : K[X] :=
  Polynomial.C delta + Polynomial.C epsilon * Polynomial.X

/-- Every finite linear combination of powers at least two retains the
square of the same affine residual.  Arbitrary passive-seed shifts and all
fixed-node values of legal X multipliers are absorbed into `coefficient`. -/
theorem sum_ge_two_powers_eq_square_mul
    (s : Finset I) (coefficient : I -> K[X]) (power : I -> Nat)
    (hpower : forall i, i ∈ s -> 2 <= power i)
    (a : K[X]) :
    (∑ i ∈ s, coefficient i * a ^ power i) =
      a ^ 2 * (∑ i ∈ s, coefficient i * a ^ (power i - 2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi2 := hpower i hi
  have hpow : a ^ 2 * a ^ (power i - 2) = a ^ power i := by
    rw [<- pow_add]
    congr 1
    omega
  calc
    coefficient i * a ^ power i =
        coefficient i * (a ^ 2 * a ^ (power i - 2)) := by rw [hpow]
    _ = a ^ 2 * (coefficient i * a ^ (power i - 2)) := by ring

/-- At a mismatch (`epsilon != 0`), no multiple of the square of the
full-centered affine residual can equal a nonzero affine F3 trace.  The
constant term of the latter is nonzero because both the off-agreement
locator value and the selected-value residual are nonzero. -/
theorem affine_F3_not_square_multiple
    (delta epsilon eta B : K) (hdelta : delta ≠ 0)
    (hepsilon : epsilon ≠ 0) (hB : B ≠ 0) (p : K[X]) :
    affineResidual delta epsilon ^ 2 * p ≠
      Polynomial.C B *
        (Polynomial.C delta + Polynomial.C eta * Polynomial.X) := by
  let a := affineResidual delta epsilon
  let target := Polynomial.C B *
    (Polynomial.C delta + Polynomial.C eta * Polynomial.X)
  have ha_degree : a.natDegree = 1 := by
    dsimp only [a, affineResidual]
    rw [add_comm]
    exact Polynomial.natDegree_linear hepsilon
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, Polynomial.natDegree_zero] at ha_degree
    omega
  have htarget_shape : target =
      Polynomial.C (B * eta) * Polynomial.X + Polynomial.C (B * delta) := by
    dsimp only [target]
    simp only [Polynomial.C_mul]
    ring
  have htarget_degree : target.natDegree <= 1 := by
    rw [htarget_shape]
    exact Polynomial.natDegree_linear_le
  have htarget : target ≠ 0 := by
    intro hzero
    have heval := congrArg (fun q : K[X] => q.eval 0) hzero
    dsimp only [target] at heval
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X, mul_zero, add_zero,
      Polynomial.eval_zero] at heval
    exact (mul_ne_zero hB hdelta) heval
  change a ^ 2 * p ≠ target
  intro heq
  by_cases hp : p = 0
  · rw [hp, mul_zero] at heq
    exact htarget heq.symm
  · have hleft_degree : (a ^ 2 * p).natDegree = 2 + p.natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero 2 ha) hp,
        Polynomial.natDegree_pow, ha_degree]
    rw [heq] at hleft_degree
    omega

/-- Consequently an arbitrary finite family of full-centered powers
`k>=2` misses the same literal affine F3 trace at every mismatched error.
This already permits arbitrary polynomial coefficients, so it includes all
legal X values and passive-seed shifts. -/
theorem affine_F3_not_in_ge_two_family
    (s : Finset I) (coefficient : I -> K[X]) (power : I -> Nat)
    (hpower : forall i, i ∈ s -> 2 <= power i)
    (delta epsilon eta B : K) (hdelta : delta ≠ 0)
    (hepsilon : epsilon ≠ 0) (hB : B ≠ 0) :
    (∑ i ∈ s,
        coefficient i * affineResidual delta epsilon ^ power i) ≠
      Polynomial.C B *
        (Polynomial.C delta + Polynomial.C eta * Polynomial.X) := by
  rw [sum_ge_two_powers_eq_square_mul s coefficient power hpower]
  exact affine_F3_not_square_multiple delta epsilon eta B
    hdelta hepsilon hB _

/-- Smallest exact mismatch witness.  Here the full-centered trace is
`1+W`, while the desired literal F3 trace is `1`.  No combination of any
`k>=2` pure centered powers, with arbitrary polynomial coefficients, can
represent it. -/
theorem one_error_full_centered_family_counterexample
    (s : Finset I) (coefficient : I -> Polynomial Rat)
    (power : I -> Nat) (hpower : forall i, i ∈ s -> 2 <= power i) :
    (∑ i ∈ s,
        coefficient i * affineResidual (K := Rat) 1 1 ^ power i) ≠ 1 := by
  rw [sum_ge_two_powers_eq_square_mul s coefficient power hpower]
  intro h
  have heval := congrArg (fun p : Polynomial Rat => p.eval (-1)) h
  norm_num [affineResidual] at heval

/-- With `deg Q_G=g-1`, a pure carrier of exponent `k` has worst weighted
X degree `47*g-k`.  Therefore a uniform X shift is legal exactly only below
the `k`-wide strict window.  This is the target worst-case arithmetic, not a
claim that the obstruction comes from too few such shifts. -/
theorem target_worst_full_centered_weight
    (g k : Nat) (hg : 1 <= g) (hk : k <= 47) :
    (47 - k) * g + k * (g - 1) = 47 * g - k := by
  rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
  have hkg : k * g <= 47 * g := Nat.mul_le_mul_right g hk
  have hkkg : k <= k * g := by
    simpa only [mul_one] using Nat.mul_le_mul_left k hg
  omega

theorem target_uniform_X_shift_legal
    (g k j : Nat) (hg : 1 <= g) (hk : k <= 47) (hj : j < k) :
    j + ((47 - k) * g + k * (g - 1)) < 47 * g := by
  rw [target_worst_full_centered_weight g k hg hk]
  omega

theorem target_uniform_X_shift_illegal_at_k
    (g k : Nat) (hg : 1 <= g) (hk : k <= 47) :
    ¬ (k + ((47 - k) * g + k * (g - 1)) < 47 * g) := by
  rw [target_worst_full_centered_weight g k hg hk]
  have hkprod : k <= 47 * g := by
    have h47 : 47 <= 47 * g := by
      simpa only [mul_one] using Nat.mul_le_mul_left 47 hg
    exact hk.trans h47
  omega

/-- For `2<=k<=47`, all active and passive caps of the m47 source leave the
centered pure carrier and each external seed shift `z<=3757-k` admissible.
The failure above therefore occurs after source legality, in the actual
error trace module. -/
theorem target_full_centered_shape_caps
    (k z : Nat) (hk0 : 2 <= k) (hk47 : k <= 47)
    (hz : z <= 3757 - k) :
    k <= 64 /\ 0 <= 16 /\ 0 <= 8 /\ z + k <= 3757 := by
  omega

#print axioms sum_ge_two_powers_eq_square_mul
#print axioms affine_F3_not_square_multiple
#print axioms affine_F3_not_in_ge_two_family
#print axioms one_error_full_centered_family_counterexample
#print axioms target_worst_full_centered_weight
#print axioms target_uniform_X_shift_legal
#print axioms target_uniform_X_shift_illegal_at_k
#print axioms target_full_centered_shape_caps

end

end ProximityPrize.SubmissionLower.K0FullCenteredOneSyndromeStop6900
