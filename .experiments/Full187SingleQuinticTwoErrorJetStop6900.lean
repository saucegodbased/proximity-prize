import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Single-quintic two-error-jet STOP

For the literal quintic carrier

`p(X) * L^50 * J_L^5`,

the coefficient of its highest passive slope term `R^5` is `p*L^55`.
Matching any linear RHS makes this coefficient and its first X/contact jet
zero at every error node.  Since `L` is nonzero there, this forces both
`p(x)=0` and `p'(x)=0`.  For distinct error nodes, the square of their locator
therefore divides `p`.

The whole `H^2` price makes the pure `Z^5` coefficient miss the target source
cutoff by 78,702.  This is decisive for one quintic carrier.  A mixed family
can evade the pointwise conclusion only by cancelling its degree-five top
between multiple independent carriers; that is a separate matrix gate.
-/

namespace ProximityPrize.SubmissionLower.Full187SingleQuinticTwoErrorJetStop6900

open Polynomial
open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- Scalar form of the `R^5` leading-coefficient argument. -/
theorem scalar_two_top_jets_force_multiplier_two_jets
    (p p' L L' : K) (hL : L ≠ 0)
    (h0 : p * L ^ 55 = 0)
    (h1 : p' * L ^ 55 + p * (55 * L ^ 54 * L') = 0) :
    p = 0 ∧ p' = 0 := by
  have hL55 : L ^ 55 ≠ 0 := pow_ne_zero _ hL
  have hp : p = 0 := (mul_eq_zero.mp h0).resolve_right hL55
  subst p
  simp only [zero_mul, add_zero] at h1
  exact ⟨rfl, (mul_eq_zero.mp h1).resolve_right hL55⟩

/-- Polynomial evaluation version.  It is the exact gate used at each error
node after extracting the degree-five `R^5` contact coefficient. -/
theorem polynomial_two_top_jets_force_multiplier_two_jets
    (p L : K[X]) (x : K) (hL : L.eval x ≠ 0)
    (h0 : (p * L ^ 55).eval x = 0)
    (h1 : (p * L ^ 55).derivative.eval x = 0) :
    p.eval x = 0 ∧ p.derivative.eval x = 0 := by
  have h0' : p.eval x * (L.eval x) ^ 55 = 0 := by
    simpa using h0
  have h1' :
      p.derivative.eval x * (L.eval x) ^ 55 +
        p.eval x * (55 * (L.eval x) ^ 54 * L.derivative.eval x) = 0 := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_mul] at h1
    simpa [mul_assoc] using h1
  exact scalar_two_top_jets_force_multiplier_two_jets
    (p.eval x) (p.derivative.eval x) (L.eval x) (L.derivative.eval x)
      hL h0' h1'

/-- A double zero gives the expected squared linear factor. -/
theorem square_linear_dvd_of_two_jets
    (p : K[X]) (x : K)
    (h0 : p.eval x = 0) (h1 : p.derivative.eval x = 0) :
    (Polynomial.X - Polynomial.C x) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr h0
  have hq0 : q.eval x = 0 := by
    rw [hq] at h1
    simpa [Polynomial.derivative_mul] using h1
  obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr hq0
  refine ⟨r, ?_⟩
  rw [hq, hr]
  ring

/-- All distinct error nodes together force the square of the full error
locator. -/
theorem error_locator_square_dvd_of_two_top_jets
    {I : Type*} [Fintype I] [DecidableEq I]
    (node : I ↪ K) (p L : K[X])
    (hL : ∀ i, L.eval (node i) ≠ 0)
    (h0 : ∀ i, (p * L ^ 55).eval (node i) = 0)
    (h1 : ∀ i, (p * L ^ 55).derivative.eval (node i) = 0) :
    (∏ i, (Polynomial.X - Polynomial.C (node i)) ^ 2) ∣ p := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact (Polynomial.pairwise_coprime_X_sub_C node.injective hij).pow
  · intro i hi
    rcases polynomial_two_top_jets_force_multiplier_two_jets
      p L (node i) (hL i) (h0 i) (h1 i) with ⟨hp, hdp⟩
    exact square_linear_dvd_of_two_jets p (node i) hp hdp

/-- Exact target failure after the forced `H^2` price. -/
theorem target_double_error_factor_breaks_pure_Z5_tail :
    2 * 81731 + 50 * 180413 +
        5 * (180413 + 2 * 81731 - 1) = 10903482 ∧
      60 * 180413 = 10824780 ∧
      10903482 - 10824780 = 78702 ∧
      10824780 < 10903482 := by
  norm_num

end

end ProximityPrize.SubmissionLower.Full187SingleQuinticTwoErrorJetStop6900

#print axioms ProximityPrize.SubmissionLower.Full187SingleQuinticTwoErrorJetStop6900.scalar_two_top_jets_force_multiplier_two_jets
#print axioms ProximityPrize.SubmissionLower.Full187SingleQuinticTwoErrorJetStop6900.polynomial_two_top_jets_force_multiplier_two_jets
#print axioms ProximityPrize.SubmissionLower.Full187SingleQuinticTwoErrorJetStop6900.error_locator_square_dvd_of_two_top_jets
#print axioms ProximityPrize.SubmissionLower.Full187SingleQuinticTwoErrorJetStop6900.target_double_error_factor_breaks_pure_Z5_tail
