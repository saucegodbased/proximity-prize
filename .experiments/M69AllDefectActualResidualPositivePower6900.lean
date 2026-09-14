import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Generic receipts for the all-defect m69 positive-power split

The executable census proves that each literal incoming residual consists of
a terminal positive power and direct powers one through `M-y-1`.  The first
theorem records the resulting common `w` factor without fixing the number of
direct terms.

The second theorem is the exact one-channel interpolation argument used by
the census.  If a target vanishes wherever `w` does, then any positive power
of `w` times one polynomial prefix can realize it as soon as that prefix is
at least as large as the live set.  It does not assert that prefixes shared by
many coefficient equations can be allocated simultaneously.
-/

namespace ProximityPrize.SubmissionLower.M69AllDefectActualResidualPositivePower6900

open Polynomial
open scoped Finset

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

/-- An arbitrary terminal term of power `terminalRest+1`, together with an
arbitrary finite list of direct terms of powers `1,...,m`. -/
def positiveIncomingResidual {K : Type*} [CommRing K]
    (w c : K) (terminalRest : Nat) {m : Nat} (u : Fin m → K) : K :=
  w ^ (terminalRest + 1) * c +
    ∑ i : Fin m, w ^ (i.1 + 1) * u i

theorem positiveIncomingResidual_eq_mul {K : Type*} [CommRing K]
    (w c : K) (terminalRest : Nat) {m : Nat} (u : Fin m → K) :
    positiveIncomingResidual w c terminalRest u =
      w * (w ^ terminalRest * c + ∑ i : Fin m, w ^ i.1 * u i) := by
  simp only [positiveIncomingResidual, mul_add, Finset.mul_sum]
  congr 1
  · rw [pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [pow_succ]
    ring

theorem positiveIncomingResidual_eq_zero_of_w_eq_zero
    {K : Type*} [CommRing K]
    (w c : K) (terminalRest : Nat) {m : Nat} (u : Fin m → K)
    (hw : w = 0) :
    positiveIncomingResidual w c terminalRest u = 0 := by
  rw [positiveIncomingResidual_eq_mul, hw, zero_mul]

/-- Correct square-channel coprime relation for the physical multiplier
`w=N/E`.  There is no extra `X` in the denominator, hence no `X^2` on the
right after clearing `w^2`. -/
theorem physical_square_relation_forces_zero
    {K : Type*} [Field K] (E N H H2 : K[X])
    (hcop : IsCoprime E N) (he : 2049 ≤ E.natDegree)
    (hH : H.natDegree < 3246)
    (hrelation : N ^ 2 * H = E ^ 2 * H2) :
    H = 0 := by
  have hE : E ≠ 0 := by
    intro hzero
    simp only [hzero, natDegree_zero] at he
    omega
  have hdiv : E ^ 2 ∣ N ^ 2 * H := by
    refine ⟨H2, ?_⟩
    rw [hrelation]
  have hEH : E ^ 2 ∣ H :=
    (show IsCoprime (E ^ 2) (N ^ 2) from hcop.pow).dvd_of_dvd_mul_left hdiv
  obtain ⟨T, rfl⟩ := hEH
  by_cases hT : T = 0
  · simp [hT]
  · have hdegree : (E ^ 2 * T).natDegree =
        2 * E.natDegree + T.natDegree := by
      rw [natDegree_mul (pow_ne_zero 2 hE) hT, natDegree_pow]
    rw [hdegree] at hH
    omega

/-- A single positive-power channel realizes every target which vanishes on
the zero set, provided its polynomial prefix can interpolate the complement.
The exponent is written `powerRest+1` so positivity is structural. -/
theorem exists_positive_power_interpolant
    {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (nodes : I → K) (hnodes : Function.Injective nodes)
    (Z : Finset I) (w target : I → K)
    (hzero : ∀ i, w i = 0 ↔ i ∈ Z)
    (htarget : ∀ i, i ∈ Z → target i = 0)
    (powerRest : Nat) :
    ∃ A : K[X],
      A.degree < ((Finset.univ : Finset I) \ Z).card ∧
      ∀ i, w i ^ (powerRest + 1) * A.eval (nodes i) = target i := by
  classical
  let L : Finset I := (Finset.univ : Finset I) \ Z
  let residual : I → K := fun i ↦
    target i / w i ^ (powerRest + 1)
  let A : K[X] := Lagrange.interpolate L nodes residual
  have hLinj : Set.InjOn nodes L := hnodes.injOn
  refine ⟨A, Lagrange.degree_interpolate_lt residual hLinj, ?_⟩
  intro i
  by_cases hi : i ∈ Z
  · have hw : w i = 0 := (hzero i).mpr hi
    rw [hw, zero_pow (Nat.succ_ne_zero powerRest), zero_mul,
      htarget i hi]
  · have hiL : i ∈ L := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
    have hw : w i ≠ 0 := by
      exact fun hw ↦ hi ((hzero i).mp hw)
    have hwpow : w i ^ (powerRest + 1) ≠ 0 :=
      pow_ne_zero _ hw
    have hA : A.eval (nodes i) = residual i := by
      exact Lagrange.eval_interpolate_at_node residual hLinj hiL
    rw [hA]
    dsimp only [residual]
    exact mul_div_cancel₀ (target i) hwpow

/-- The executable's worst selected prefix has dimension 258868.  Thus the
uniform threshold 3276 leaves no more coordinates than that prefix. -/
theorem uniform_large_zero_live_capacity (z rho : Nat)
    (hz : 3276 ≤ z) (hrho : 258868 ≤ rho) :
    262144 - z ≤ rho := by
  omega

/-- Exact endpoint arithmetic for the best and worst selected m69 shapes. -/
theorem selected_prefix_threshold_arithmetic :
    262144 - 258926 = 3218 ∧
    262144 - 258868 = 3276 ∧
    3276 ≤ 149776 ∧
    258868 + 3276 = 262144 := by
  norm_num

#print axioms positiveIncomingResidual_eq_mul
#print axioms positiveIncomingResidual_eq_zero_of_w_eq_zero
#print axioms physical_square_relation_forces_zero
#print axioms exists_positive_power_interpolant
#print axioms uniform_large_zero_live_capacity
#print axioms selected_prefix_threshold_arithmetic

end
end ProximityPrize.SubmissionLower.M69AllDefectActualResidualPositivePower6900
