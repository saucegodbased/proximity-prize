import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The first m69 actual residual at numerator-zero nodes

The literal first-defect residual has a terminal `W^31` term and 29 incoming
terms with powers `W^1,...,W^29`.  Arbitrary scalars absorb the nonzero
binomial coefficients.  The first two theorems record its common `W` factor.

The interpolation theorem is the abstract two-channel gluing used when the
zero set has at least 134317 nodes: a low polynomial handles that zero set,
and `W` times a second polynomial handles its complement.  It deliberately
does not assert the still-open small-zero rational-rank theorem.
-/

namespace ProximityPrize.SubmissionLower.M69FirstDefectActualResidualZeroSplit6900

open Polynomial
open scoped Finset

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

/-- Binomial scalars may be absorbed into `u`.  This is the exact power
pattern of the incoming first-defect residual: terminal power 31 and direct
predecessor powers 1 through 29. -/
def positiveResidual {K : Type*} [CommRing K]
    (w c : K) (u : Fin 29 → K) : K :=
  w ^ 31 * c + ∑ i : Fin 29, w ^ (i.1 + 1) * u i

theorem positiveResidual_eq_mul {K : Type*} [CommRing K]
    (w c : K) (u : Fin 29 → K) :
    positiveResidual w c u =
      w * (w ^ 30 * c + ∑ i : Fin 29, w ^ i.1 * u i) := by
  simp only [positiveResidual, mul_add, Finset.mul_sum]
  congr 1
  · rw [show 31 = 30 + 1 by omega, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [pow_succ]
    ring

theorem positiveResidual_eq_zero_of_w_eq_zero
    {K : Type*} [CommRing K] (w c : K) (u : Fin 29 → K)
    (hw : w = 0) :
    positiveResidual w c u = 0 := by
  rw [positiveResidual_eq_mul, hw, zero_mul]

/-- Lagrange interpolation implements the zero/live two-channel gluing.
`A` first realizes arbitrary target values on `Z`.  On its complement `L`,
`B` realizes `(target-A)/w`, which is defined because `w` is nonzero there.
Thus `A+w*B` realizes the target everywhere. -/
theorem exists_two_channel_interpolants
    {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (nodes : I → K) (hnodes : Function.Injective nodes)
    (Z : Finset I) (w target : I → K)
    (hzero : ∀ i, w i = 0 ↔ i ∈ Z) :
    ∃ A B : K[X],
      A.degree < Z.card ∧
      B.degree < ((Finset.univ : Finset I) \ Z).card ∧
      ∀ i, A.eval (nodes i) + w i * B.eval (nodes i) = target i := by
  classical
  let L : Finset I := (Finset.univ : Finset I) \ Z
  let A : K[X] := Lagrange.interpolate Z nodes target
  let residual : I → K := fun i ↦
    (target i - A.eval (nodes i)) / w i
  let B : K[X] := Lagrange.interpolate L nodes residual
  have hZinj : Set.InjOn nodes Z := hnodes.injOn
  have hLinj : Set.InjOn nodes L := hnodes.injOn
  refine ⟨A, B, Lagrange.degree_interpolate_lt target hZinj,
    Lagrange.degree_interpolate_lt residual hLinj, ?_⟩
  intro i
  by_cases hi : i ∈ Z
  · have hA : A.eval (nodes i) = target i := by
      exact Lagrange.eval_interpolate_at_node target hZinj hi
    rw [hA, (hzero i).mpr hi]
    simp
  · have hiL : i ∈ L := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
    have hw : w i ≠ 0 := by
      exact fun hw ↦ hi ((hzero i).mp hw)
    have hB : B.eval (nodes i) = residual i := by
      exact Lagrange.eval_interpolate_at_node residual hLinj hiL
    rw [hB]
    dsimp only [residual]
    rw [mul_div_cancel₀ _ hw]
    ring

/-- Exact dimensions for the large-numerator-zero branch. -/
theorem first_defect_large_zero_arithmetic (z : Nat)
    (hzLower : 134317 ≤ z) (hzUpper : z ≤ 149776) :
    z ≤ 258898 ∧ 262144 - z ≤ 127827 := by
  omega

/-- Literal first-defect powers, widths, and the remaining parameter window. -/
theorem first_defect_literal_arithmetic :
    94 - 14 - 10 - 39 = 31 ∧
    69 - 39 = 30 ∧
    149776 < 258898 ∧
    262144 - 127827 = 134317 ∧
    149776 - 129449 = 20327 := by
  norm_num

#print axioms positiveResidual_eq_mul
#print axioms positiveResidual_eq_zero_of_w_eq_zero
#print axioms exists_two_channel_interpolants
#print axioms first_defect_large_zero_arithmetic
#print axioms first_defect_literal_arithmetic

end
end ProximityPrize.SubmissionLower.M69FirstDefectActualResidualZeroSplit6900
