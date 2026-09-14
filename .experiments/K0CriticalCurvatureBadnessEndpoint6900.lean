import BadRowSecondInterpolatorUniqueness6900
import PeriodTwoSecondDerivativeZeroCount6900

/-!
# Bad-row endpoint for the critical raw-curvature staircase

The remaining compatible boundary line in the raw `{1,R}` controls is the
curvature covector.  The critical `Y^m S` staircase is expected to make its
scalar `lambdaS` satisfy `lambdaS * Q'' = 0`, where `Q` is the degree-`<g`
interpolant of the received direction on the selected agreement set.

This file proves that this is already a complete semantic endpoint.  Below
the characteristic, `Q''=0` would force `deg Q <= 1 <= w`, contradicting the
retained bad-row witness.  Thus the displayed recurrence kills `lambdaS`.
It does not assert or assume that the raw source supplies that recurrence.
-/

namespace ProximityPrize.SubmissionLower.K0CriticalCurvatureBadnessEndpoint6900

open ProximityPrize.Benchmark
open BadRowSecondInterpolatorUniqueness6900
open PeriodTwoSecondDerivativeZeroCount6900

noncomputable section

set_option autoImplicit false
set_option Elab.async false

/-- Any polynomial which interpolates the received direction on a bad
agreement set has nonzero second derivative, provided its degree is below
the characteristic and the code degree bound is at least one. -/
theorem bad_direction_interpolant_second_derivative_ne_zero
    {I K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field K] [Fintype K] [DecidableEq K] [CharP K 2130706433]
    (domain : I ↪ K) (w : Nat) (U : Fin 2 → I → K)
    (A : Finset I) (gamma : K) (P Q : Polynomial K)
    (hw : 1 ≤ w)
    (hPdegree : P.natDegree ≤ w)
    (hQchar : Q.natDegree < 2130706433)
    (hP : ∀ i ∈ A,
      P.eval (domain i) = U 0 i + gamma * U 1 i)
    (hQ : ∀ i ∈ A, Q.eval (domain i) = U 1 i)
    (hbad : ∃ j : Fin 2,
      LinearCode.projectedWord (U j) A ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code domain (w + 1)) A) :
    Q.derivative.derivative ≠ 0 := by
  intro hsecond
  have hQone : Q.natDegree ≤ 1 :=
    natDegree_le_one_of_second_derivative_eq_zero Q hQchar hsecond
  have hQdegree : Q.natDegree ≤ w := hQone.trans hw
  have hone : (1 : K) - gamma * 0 = 0 := by
    apply second_interpolant_is_proportional
      domain w U A gamma 0 1 P Q hPdegree hQdegree hP
    · intro i hi
      simpa using hQ i hi
    · exact hbad
  simpa using hone

/-- Over a field, a scalar multiple of a nonzero polynomial can vanish only
when the scalar vanishes. -/
theorem scalar_eq_zero_of_smul_polynomial_eq_zero
    {K : Type*} [Field K] (a : K) (Q : Polynomial K)
    (hQ : Q ≠ 0) (hzero : a • Q = 0) : a = 0 := by
  by_contra ha
  have hQzero : Q = 0 := by
    calc
      Q = 1 • Q := (one_smul K Q).symm
      _ = (a⁻¹ * a) • Q := by rw [inv_mul_cancel₀ ha]
      _ = a⁻¹ • (a • Q) := by rw [mul_smul]
      _ = 0 := by rw [hzero, smul_zero]
  exact hQ hQzero

/-- Exact consumer for the intended critical-staircase output
`lambdaS • Q'' = 0`. -/
theorem curvature_scalar_eq_zero_of_bad_direction_relation
    {I K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field K] [Fintype K] [DecidableEq K] [CharP K 2130706433]
    (domain : I ↪ K) (w : Nat) (U : Fin 2 → I → K)
    (A : Finset I) (gamma lambdaS : K) (P Q : Polynomial K)
    (hw : 1 ≤ w)
    (hPdegree : P.natDegree ≤ w)
    (hQchar : Q.natDegree < 2130706433)
    (hP : ∀ i ∈ A,
      P.eval (domain i) = U 0 i + gamma * U 1 i)
    (hQ : ∀ i ∈ A, Q.eval (domain i) = U 1 i)
    (hbad : ∃ j : Fin 2,
      LinearCode.projectedWord (U j) A ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code domain (w + 1)) A)
    (hcritical : lambdaS • Q.derivative.derivative = 0) :
    lambdaS = 0 := by
  apply scalar_eq_zero_of_smul_polynomial_eq_zero
    lambdaS Q.derivative.derivative
  · exact bad_direction_interpolant_second_derivative_ne_zero
      domain w U A gamma P Q hw hPdegree hQchar hP hQ hbad
  · exact hcritical

#print axioms bad_direction_interpolant_second_derivative_ne_zero
#print axioms scalar_eq_zero_of_smul_polynomial_eq_zero
#print axioms curvature_scalar_eq_zero_of_bad_direction_relation

end

end ProximityPrize.SubmissionLower.K0CriticalCurvatureBadnessEndpoint6900
