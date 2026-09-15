import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Monic residual division: exact regularity and degree gate

This is the smallest algebraic probe behind a proposed canonical
agreement-residual chart.  A monic locator makes division unique and removes
all Cramer denominators, but it does not make the quotient low-degree in the
locator coefficients.  Successive top-down cancellation accumulates one
locator coefficient at every step.

`inverseTail h z r` is the exact worst-case recurrence.  Although
`(X + h) * inverseTail` has only two nonzero boundary terms, the constant
coefficient of the quotient is `z * (-h)^r`.  At the benchmark residual
length `r = 81730`, this is an `81731`-degree monomial in `(z,h)`, already far
above the shallow source cap `1729`.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveResidualMonicDivisionDegreeGate6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

variable {K : Type*} [Field K]

/-- The quotient produced by cancelling one subleading monic-locator
coefficient through `r+1` consecutive high coefficients. -/
def inverseTail (h z : K) : Nat → K[X]
  | 0 => C z
  | r + 1 => X * inverseTail h z r + C (z * (-h) ^ (r + 1))

/-- Exact top-down monic-division cancellation. -/
theorem X_add_C_mul_inverseTail (h z : K) (r : Nat) :
    (X + C h) * inverseTail h z r =
      C z * X ^ (r + 1) - C (z * (-h) ^ (r + 1)) := by
  induction r with
  | zero =>
      simp only [inverseTail, Nat.zero_add, pow_one, add_mul]
      rw [← C_mul]
      have hz : z * -h = -(h * z) := by ring
      rw [hz, map_neg]
      ring
  | succ r ih =>
      rw [inverseTail]
      calc
        (X + C h) *
            (X * inverseTail h z r + C (z * (-h) ^ (r + 1))) =
            X * ((X + C h) * inverseTail h z r) +
              (X + C h) * C (z * (-h) ^ (r + 1)) := by ring
        _ = X * (C z * X ^ (r + 1) - C (z * (-h) ^ (r + 1))) +
              (X + C h) * C (z * (-h) ^ (r + 1)) := by rw [ih]
        _ = C z * X ^ (r + 1 + 1) -
              C (z * (-h) ^ (r + 1 + 1)) := by
          simp only [pow_succ]
          simp only [map_mul, map_neg]
          ring

/-- The bottom quotient coefficient carries the full accumulated locator
degree. -/
theorem inverseTail_coeff_zero (h z : K) (r : Nat) :
    (inverseTail h z r).coeff 0 = z * (-h) ^ r := by
  cases r with
  | zero => simp [inverseTail]
  | succ r =>
      rw [inverseTail, coeff_add, coeff_C_zero]
      simp only [coeff_zero_eq_eval_zero, eval_mul, eval_X, zero_mul,
        zero_add]

/-- Multiplying by any fixed monic prefix `G` preserves the same phenomenon:
all dependence on the moving subleading locator coefficient is pushed below
the high boundary after exact cancellation. -/
theorem prefixed_inverseTail_factorization
    (G : K[X]) (h z : K) (r : Nat) :
    ((X + C h) * G) * inverseTail h z r =
      G * (C z * X ^ (r + 1) - C (z * (-h) ^ (r + 1))) := by
  calc
    ((X + C h) * G) * inverseTail h z r =
        G * ((X + C h) * inverseTail h z r) := by ring
    _ = G * (C z * X ^ (r + 1) - C (z * (-h) ^ (r + 1))) := by
      rw [X_add_C_mul_inverseTail]

/-- Put `gamma = (-h)^(r+1)`.  The complete locator-residual product is then
affine in `gamma`, even though the quotient itself contains powers of `h`
through order `r`.  This is the exact obstruction to recovering a cheap
regular quotient merely from an affine product tail. -/
theorem prefixed_product_affine_in_power_parameter
    (G : K[X]) (h : K) (r : Nat) :
    ((X + C h) * G) * inverseTail h 1 r =
      G * X ^ (r + 1) - C ((-h) ^ (r + 1)) * G := by
  rw [prefixed_inverseTail_factorization]
  simp only [one_mul, map_one, one_mul]
  ring

/-- The exact numerical obstruction to inserting all canonical quotient
coefficients as shallow-source coordinates. -/
theorem benchmark_residual_regular_degree_exceeds_shallow_cap :
    1729 < 81730 + 1 := by
  norm_num

/-- The common-core model fits the target block exactly: a core of degree
`180412` plus `81732` possible extra roots fills all `262144` nodes.  The
power exponent appearing in the residual recurrence is coprime to the base
field's multiplicative-group order, so this obstruction is not caused by
colliding labels. -/
theorem benchmark_common_core_power_arithmetic :
    180412 + 81732 = 262144 ∧
    81730 + 1 = 81731 ∧
    Nat.gcd 81731 2130706432 = 1 := by
  norm_num

/-- An explicit characteristic-two interface counterexample: adjoining a
separable affine source coordinate does not make an unrelated graph
coordinate separable.  On the affine line, `T=X` has nonzero derivative while
the nonconstant graph coordinate `B=X^2` is Frobenius-closed. -/
theorem affine_coordinate_does_not_kill_pclosed_graph :
    let T : (ZMod 2)[X] := X
    let B : (ZMod 2)[X] := X ^ 2
    T.derivative ≠ 0 ∧ B ≠ 0 ∧ B.natDegree = 2 ∧ B.derivative = 0 := by
  dsimp only
  constructor
  · simp
  constructor
  · exact pow_ne_zero 2 X_ne_zero
  constructor
  · simp
  · rw [derivative_pow]
    have htwo : (2 : ZMod 2) = 0 := by decide
    change C (2 : ZMod 2) * X ^ (2 - 1) * derivative X = 0
    rw [htwo, map_zero, zero_mul, zero_mul]

#print axioms X_add_C_mul_inverseTail
#print axioms inverseTail_coeff_zero
#print axioms prefixed_inverseTail_factorization
#print axioms prefixed_product_affine_in_power_parameter
#print axioms benchmark_residual_regular_degree_exceeds_shallow_cap
#print axioms benchmark_common_core_power_arithmetic
#print axioms affine_coordinate_does_not_kill_pclosed_graph

end
end ProximityPrize.SubmissionLower.ProjectiveResidualMonicDivisionDegreeGate6900
