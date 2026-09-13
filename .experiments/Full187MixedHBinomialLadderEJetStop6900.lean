import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# First error-`E` jet obstruction for the mixed-H binomial ladder

Every source-legal binomial ladder obtained by expanding

`V^(60-2k) * (U*V^2-H^3*Z*J1)^k`, `1 <= k <= 3`,

vanishes at the pure-seed endpoint.  At an error, however, all terms except
the `i=0` binomial summand contain `H^3`; modulo `H` the ladder is a scalar
multiple of `V^60`.  On the constant-X error slice `V=1+E`, this locks the
first `E` jet to sixty times its value.  It cannot match the linear F0 slice
`a*(1+E)` at a nonzero value in the target's characteristic.
-/

namespace ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- The original three-row mixed-`H` checkerboard is literally the square
of one shifted normal binomial.  This makes the extension to the cubic
four-row ladder unambiguous. -/
theorem mixed_H_square_factorization (U H Z V J1 : K) :
    V ^ 56 * (U * V ^ 2 - H ^ 3 * Z * J1) ^ 2 =
      U ^ 2 * V ^ 60 - 2 * U * H ^ 3 * Z * V ^ 58 * J1 +
        H ^ 6 * Z ^ 2 * V ^ 56 * J1 ^ 2 := by
  ring

/-- The next source-legal member of the chain has four distinct normal/H
rows, rather than being a two-packet relation. -/
theorem mixed_H_cubic_factorization (U H Z V J1 : K) :
    V ^ 54 * (U * V ^ 2 - H ^ 3 * Z * J1) ^ 3 =
      U ^ 3 * V ^ 60 - 3 * U ^ 2 * H ^ 3 * Z * V ^ 58 * J1 +
        3 * U * H ^ 6 * Z ^ 2 * V ^ 56 * J1 ^ 2 -
          H ^ 9 * Z ^ 3 * V ^ 54 * J1 ^ 3 := by
  ring

/-- Exact strict source windows for the binomial-chain exponents.  Here
`deg q < e=81731`, `deg U <= g+e-1=262143`, and the four values in the
last line are the strict pure windows for `r=0,1,2,3`.  Thus only the
chains through the cubic are source-legal; the quartic already exceeds the
first window. -/
theorem binomial_ladder_source_window_ledger :
    343873 < 1017060 ∧ 326923 < 1000110 ∧
    606016 < 1017060 ∧ 589066 < 1000110 ∧ 572116 < 983160 ∧
    868159 < 1017060 ∧ 851209 < 1000110 ∧ 834259 < 983160 ∧
      817309 < 966210 ∧
    1017060 - 868159 = 148901 ∧
    1130302 - 1017060 = 113242 := by
  norm_num

/-- The derivative at `E=0` of the error reduction of every binomial-ladder
row.  The power `60` is independent of the binomial exponent `k`. -/
theorem V60_error_slice_derivative (a : K) :
    ((C a * (1 + X) ^ 60).derivative).eval 0 = 60 * a := by
  rw [derivative_mul, derivative_C, zero_mul, zero_add]
  rw [derivative_pow]
  simp
  ring

/-- The same coefficient is the first `T*R` coefficient: substitute the
single formal variable `X` by the passive minor `T*R`.  This is a coefficient
statement, so it makes no assumption about the remaining higher `T` terms
of the actual local chart. -/
theorem V60_first_passive_coefficient (a : K) :
    (C a * (1 + X) ^ 60).coeff 1 = 60 * a := by
  rw [coeff_C_mul]
  have hcoeff := Polynomial.coeff_derivative (((1 : K[X]) + X) ^ 60) 0
  norm_num at hcoeff
  calc
    a * (((1 : K[X]) + X) ^ 60).coeff 1 =
        a * ((((1 : K[X]) + X) ^ 60).derivative).coeff 0 := by rw [hcoeff]
    _ = a * ((((1 : K[X]) + X) ^ 60).derivative).eval 0 := by
      rw [coeff_zero_eq_eval_zero]
    _ = 60 * a := by
      rw [derivative_pow]
      simp
      ring

/-- A nonzero linear F0 error slice has derivative equal to its value, while
the mixed-H ladder has derivative sixty times that value.  Equality of both
the value and the first `E` derivative is impossible whenever 59 is nonzero
in the coefficient field. -/
theorem V60_cannot_match_linear_first_E_jet
    (a : K) (ha : a ≠ 0) (h59 : (59 : K) ≠ 0) :
    ¬ (((C a * (1 + X) ^ 60).eval 0 = (C a * (1 + X)).eval 0) ∧
      ((C a * (1 + X) ^ 60).derivative).eval 0 =
        ((C a * (1 + X)).derivative).eval 0) := by
  rintro ⟨_value, hderivative⟩
  rw [V60_error_slice_derivative] at hderivative
  norm_num at hderivative
  have hzero : (59 : K) * a = 0 := by
    linear_combination hderivative
  exact h59 ((mul_eq_zero.mp hzero).resolve_right ha)

end

end ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900

#print axioms ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900.V60_error_slice_derivative
#print axioms ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900.mixed_H_square_factorization
#print axioms ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900.mixed_H_cubic_factorization
#print axioms ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900.binomial_ladder_source_window_ledger
#print axioms ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900.V60_first_passive_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187MixedHBinomialLadderEJetStop6900.V60_cannot_match_linear_first_E_jet
