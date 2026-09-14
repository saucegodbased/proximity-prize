import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# A numerator zero set blocks the universal m69 rational-prefix map

This file isolates the linear-algebra step in the exact countergate.  On a
set `Z` where the rational multiplier `W` vanishes, every positive-power
channel restricts to zero.  Thus the restricted combined map factors through
the base prefix.  If that prefix has rank `< |Z|`, the combined map cannot be
surjective, regardless of how many positive powers are supplied.

The final theorem checks the literal m69 numbers.  The `(0,0,0)` deficient
shape has base fringe `127729`; a numerator locator may have `127730` domain
zeros while still satisfying the current degree cap
`deg N0 <= 131071 + deg E0 + s` at `deg E0=2151,s=0`.
-/

namespace ProximityPrize.SubmissionLower.M69NumeratorZeroSetRankCountergate6900

open Module
open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option Elab.async false

noncomputable section

/-- The hostile numerator is simply the locator of its chosen zero set. -/
def nodalLocator {K I : Type*} [Field K]
    (nodes : I → K) (Z : Finset I) : K[X] :=
  ∏ i ∈ Z, (X - C (nodes i))

theorem nodalLocator_natDegree {K I : Type*} [Field K]
    (nodes : I → K) (Z : Finset I) :
    (nodalLocator nodes Z).natDegree = Z.card := by
  classical
  have h := Polynomial.natDegree_prod_of_monic Z
    (fun i : I ↦ (X - C (nodes i) : K[X]))
    (fun i _hi ↦ Polynomial.monic_X_sub_C (nodes i))
  simpa [nodalLocator] using h

theorem nodalLocator_eval_eq_zero {K I : Type*} [Field K]
    (nodes : I → K) (Z : Finset I) {i : I} (hi : i ∈ Z) :
    (nodalLocator nodes Z).eval (nodes i) = 0 := by
  classical
  rw [nodalLocator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hi
  simp

private theorem isCoprime_X_sub_C_of_eval_ne_zero
    {K : Type*} [Field K] (E : K[X]) (x : K)
    (hx : E.eval x ≠ 0) : IsCoprime E (X - C x) := by
  obtain ⟨d, hd⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := E) (a := x)
  refine ⟨C (E.eval x)⁻¹, -(C (E.eval x)⁻¹ * d), ?_⟩
  have hc : C (E.eval x)⁻¹ * C (E.eval x) = (1 : K[X]) := by
    rw [← C_mul]
    simp [hx]
  rw [← hc]
  linear_combination C (E.eval x)⁻¹ * hd

/-- Root-freeness of the denominator on `Z` makes it coprime to the hostile
numerator locator. -/
theorem isCoprime_nodalLocator_of_root_free
    {K I : Type*} [Field K] (nodes : I → K) (Z : Finset I) (E : K[X])
    (hroot : ∀ i ∈ Z, E.eval (nodes i) ≠ 0) :
    IsCoprime E (nodalLocator nodes Z) := by
  classical
  unfold nodalLocator
  apply IsCoprime.prod_right
  intro i hi
  exact isCoprime_X_sub_C_of_eval_ne_zero E (nodes i) (hroot i hi)

/-- Formal polynomial package for a `127730`-node numerator zero set. -/
theorem nodalLocator_127730_certificate
    {K I : Type*} [Field K] (nodes : I → K) (Z : Finset I)
    (hcard : Z.card = 127730) (E : K[X])
    (hroot : ∀ i ∈ Z, E.eval (nodes i) ≠ 0) :
    let N0 := nodalLocator nodes Z
    N0.natDegree = 127730 ∧ IsCoprime E N0 ∧
      ∀ i ∈ Z, N0.eval (nodes i) = 0 := by
  dsimp only
  refine ⟨(nodalLocator_natDegree nodes Z).trans hcard, ?_, ?_⟩
  · exact isCoprime_nodalLocator_of_root_free nodes Z E hroot
  · intro i hi
    exact nodalLocator_eval_eq_zero nodes Z hi

/-- A map into functions on `Z` cannot be onto when its range factors through
a map of rank at most `f < |Z|`.  This is the abstract restriction argument
used when all positive powers of a rational multiplier vanish on `Z`. -/
theorem not_surjective_of_restriction_factors_through_low_rank
    {K A B Z : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [Fintype Z]
    (combined : A →ₗ[K] (Z → K)) (base : B →ₗ[K] (Z → K))
    (f : Nat)
    (hfactor : ∀ a, ∃ b, combined a = base b)
    (hbase : finrank K (LinearMap.range base) ≤ f)
    (hsmall : f < Fintype.card Z) :
    ¬ Function.Surjective combined := by
  have hrange : LinearMap.range combined ≤ LinearMap.range base := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hfactor a
    exact ⟨b, hb.symm⟩
  have hcombined : finrank K (LinearMap.range combined) ≤ f :=
    (Submodule.finrank_mono hrange).trans hbase
  intro hsurj
  have htop : LinearMap.range combined = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hfull : Fintype.card Z ≤ f := by
    calc
      Fintype.card Z = finrank K (Z → K) := by simp
      _ = finrank K (LinearMap.range combined) := by rw [htop]; simp
      _ ≤ f := hcombined
  omega

/-- Exact feasibility ledger for the numerator-zero obstruction at the new
W133221 endpoint. -/
theorem target_m69_numerator_zero_arithmetic :
    127729 < 127730 ∧
    127730 ≤ 131071 + 2151 + 0 ∧
    0 + 0 + 2151 ≤ 2151 ∧
    2151 < 18415 ∧
    0 + 0 ≤ 8328 := by
  norm_num

/-- Even the older W133119 endpoint admits the same zero-set obstruction. -/
theorem target_m69_old_endpoint_numerator_zero_arithmetic :
    127729 < 127730 ∧
    127730 ≤ 131071 + 2049 + 0 ∧
    0 + 0 + 2049 ≤ 2049 := by
  norm_num

#print axioms not_surjective_of_restriction_factors_through_low_rank
#print axioms nodalLocator_127730_certificate
#print axioms target_m69_numerator_zero_arithmetic

end
end ProximityPrize.SubmissionLower.M69NumeratorZeroSetRankCountergate6900
