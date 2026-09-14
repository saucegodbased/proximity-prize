import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Corrected m69 square-dual recurrence

For the physical source `sum_t (N/E)^t * F_<f_t`, the Reed--Solomon dual
anchor is the same `X` at every prefix: `lambda*(N/E)^t = X*H_t`.
Consequently the two-step relation is

`N^2*K_j = E^2*K_(j+1)` on the evaluation domain.

There is no extra `X^2` on either side.  This file records two consequences
of the corrected relation: adjacent low kernels have polynomial rank-one
minors, and the last two kernels already close the no-wrap branch through
`deg N = 130508` under the uniform m69 caps.
-/

namespace ProximityPrize.SubmissionLower.M69CorrectedDualRecurrence6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The actual square recurrence after cancelling the fixed RS-dual `X`
anchor. -/
def CorrectedNodalSquareRecurrence
    {I K : Type*} [Field K] (nodes : I → K)
    (E N Kprev Knext : K[X]) : Prop :=
  ∀ i,
    (N ^ 2 * Kprev).eval (nodes i) =
      (E ^ 2 * Knext).eval (nodes i)

/-- Three consecutive corrected recurrences make the low kernels geometric
pointwise.  Their degrees are tiny enough that the nodal rank-one minor is an
honest polynomial identity. -/
theorem corrected_recurrence_cross_minor
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (hcard : Fintype.card I = 262144)
    (E N K0 K1 K2 : K[X])
    (hEroot : ∀ i, E.eval (nodes i) ≠ 0)
    (h01 : CorrectedNodalSquareRecurrence nodes E N K0 K1)
    (h12 : CorrectedNodalSquareRecurrence nodes E N K1 K2)
    (hK0 : K0.natDegree < 1192)
    (hK1 : K1.natDegree < 1192)
    (hK2 : K2.natDegree < 1192) :
    K0 * K2 = K1 ^ 2 := by
  let P : K[X] := K0 * K2 - K1 ^ 2
  have hPdegree : P.natDegree < 262144 := by
    have hleft : (K0 * K2).natDegree < 2384 := by
      exact natDegree_mul_le.trans_lt (by omega)
    have hright : (K1 ^ 2).natDegree < 2384 := by
      exact natDegree_pow_le.trans_lt (by omega)
    exact (natDegree_sub_le _ _).trans_lt
      ((max_lt hleft hright).trans_le (by norm_num))
  have hPeval : ∀ i, P.eval (nodes i) = 0 := by
    intro i
    have he2 : E.eval (nodes i) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (hEroot i)
    have h01i := h01 i
    have h12i := h12 i
    simp only [eval_mul, eval_pow] at h01i h12i
    have hproduct :
        E.eval (nodes i) ^ 2 *
            (K0.eval (nodes i) * K2.eval (nodes i)) =
          E.eval (nodes i) ^ 2 * K1.eval (nodes i) ^ 2 := by
      calc
        E.eval (nodes i) ^ 2 *
              (K0.eval (nodes i) * K2.eval (nodes i)) =
            (N.eval (nodes i) ^ 2 * K1.eval (nodes i)) *
              K0.eval (nodes i) := by rw [h12i]; ring
        _ = (N.eval (nodes i) ^ 2 * K0.eval (nodes i)) *
              K1.eval (nodes i) := by ring
        _ = E.eval (nodes i) ^ 2 * K1.eval (nodes i) ^ 2 := by
              rw [h01i]
              ring
    have hminor :
        K0.eval (nodes i) * K2.eval (nodes i) =
          K1.eval (nodes i) ^ 2 := mul_left_cancel₀ he2 hproduct
    simp only [P, eval_sub, eval_mul, eval_pow, hminor, sub_self]
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      P nodes.injective hPeval
    simpa only [hcard] using hPdegree
  exact sub_eq_zero.mp (by simpa only [P] using hPzero)

/-- Once a corrected no-wrap square relation is a polynomial equality,
coprimality and `2*deg E > deg Kprev` kill both kernels. -/
theorem corrected_short_relation_forces_zero
    {K : Type*} [Field K] (E N Kprev Knext : K[X])
    (hcop : IsCoprime E N)
    (heLower : 2151 ≤ E.natDegree)
    (hKprev : Kprev.natDegree < 1127)
    (hrelation : N ^ 2 * Kprev = E ^ 2 * Knext) :
    Kprev = 0 ∧ Knext = 0 := by
  have hE : E ≠ 0 := by
    intro hzero
    simp only [hzero, natDegree_zero] at heLower
    omega
  have hdiv : E ^ 2 ∣ N ^ 2 * Kprev := ⟨Knext, hrelation⟩
  have hEK : E ^ 2 ∣ Kprev :=
    (show IsCoprime (E ^ 2) (N ^ 2) from hcop.pow).dvd_of_dvd_mul_left hdiv
  have hKzero : Kprev = 0 := by
    obtain ⟨T, hT⟩ := hEK
    by_cases hTzero : T = 0
    · simp only [hT, hTzero, mul_zero]
    · exfalso
      have hdegree : Kprev.natDegree =
          2 * E.natDegree + T.natDegree := by
        rw [hT, natDegree_mul (pow_ne_zero 2 hE) hTzero, natDegree_pow]
      omega
  refine ⟨hKzero, ?_⟩
  rw [hKzero, mul_zero] at hrelation
  exact (mul_eq_zero.mp hrelation.symm).resolve_left (pow_ne_zero 2 hE)

/-- Uniform late-pair no-wrap theorem.  The all-shape census gives exclusive
caps `1127` and `1125` for the penultimate and last kernels.  This raises the
old direct-square cutoff from `129449` to `130508`. -/
theorem corrected_late_pair_nodal_relation_forces_zero
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (hcard : Fintype.card I = 262144)
    (E N Kprev Knext : K[X])
    (hcop : IsCoprime E N)
    (heLower : 2151 ≤ E.natDegree)
    (heUpper : E.natDegree ≤ 18414)
    (hnUpper : N.natDegree ≤ 130508)
    (hKprev : Kprev.natDegree < 1127)
    (hKnext : Knext.natDegree < 1125)
    (hrec : CorrectedNodalSquareRecurrence nodes E N Kprev Knext) :
    Kprev = 0 ∧ Knext = 0 := by
  let F : K[X] := N ^ 2 * Kprev - E ^ 2 * Knext
  have hleft : (N ^ 2 * Kprev).natDegree < 262144 := by
    calc
      (N ^ 2 * Kprev).natDegree
          ≤ (N ^ 2).natDegree + Kprev.natDegree := natDegree_mul_le
      _ ≤ 2 * N.natDegree + Kprev.natDegree :=
        Nat.add_le_add_right natDegree_pow_le _
      _ < 262144 := by omega
  have hright : (E ^ 2 * Knext).natDegree < 262144 := by
    calc
      (E ^ 2 * Knext).natDegree
          ≤ (E ^ 2).natDegree + Knext.natDegree := natDegree_mul_le
      _ ≤ 2 * E.natDegree + Knext.natDegree :=
        Nat.add_le_add_right natDegree_pow_le _
      _ < 262144 := by omega
  have hFdegree : F.natDegree < 262144 :=
    (natDegree_sub_le _ _).trans_lt (max_lt hleft hright)
  have hFeval : ∀ i, F.eval (nodes i) = 0 := by
    intro i
    simp only [F, eval_sub, hrec i, sub_self]
  have hFzero : F = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      F nodes.injective hFeval
    simpa only [hcard] using hFdegree
  have hrelation : N ^ 2 * Kprev = E ^ 2 * Knext :=
    sub_eq_zero.mp (by simpa only [F] using hFzero)
  exact corrected_short_relation_forces_zero
    E N Kprev Knext hcop heLower hKprev hrelation

theorem corrected_m69_no_wrap_arithmetic :
    2 * 130508 + 1126 = 262142 ∧
    262144 ≤ 2 * 130509 + 1126 ∧
    2 * 18414 + 1124 < 262144 ∧
    1126 < 2 * 2151 := by
  norm_num

#print axioms CorrectedNodalSquareRecurrence
#print axioms corrected_recurrence_cross_minor
#print axioms corrected_short_relation_forces_zero
#print axioms corrected_late_pair_nodal_relation_forces_zero
#print axioms corrected_m69_no_wrap_arithmetic

end
end ProximityPrize.SubmissionLower.M69CorrectedDualRecurrence6900
