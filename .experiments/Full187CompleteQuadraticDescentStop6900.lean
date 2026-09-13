import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete quadratic descent behind the Full187 terminal STOP

The apparent enlargement

`T2(A) + V*T1(B) + C*V^2`

is the complete order-three quadratic agreement-contact family.  This file
records the exact product-rule descent showing that quadratic-zero contact
on the error set merely factors one copy of the error locator from the
*whole same family*.  It therefore does not escape the terminal cascade.

After the descent, the fixed-coordinate source tails are triangular:
`SZ` sees the `T2` parameter, then `RZ` sees the `V*T1` parameter, then `YZ`
sees the `V^2` parameter.  With `Q=H^2`, all three have the same forbidden
factor `L^58*H^3`, already 15,436 degrees outside the loosest target strip.
-/

namespace ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900

set_option autoImplicit false

variable {K : Type*} [Field K]

def T1 (B B' V W : K) : K := B * W - B' * V

def T2 (A A' A'' V W P : K) : K :=
  A * W ^ 2 - A' * V * W + A'' * V ^ 2 / 2 - A * V * P / 2

def quadraticFamily
    (A A' A'' B B' C V W P : K) : K :=
  T2 A A' A'' V W P + V * T1 B B' V W + C * V ^ 2

/-- Exact error-locator descent.  The left jets are the product-rule jets
of `H*a`, together with the unique two further parameters compatible with
quadratic-zero error contact.  No division by `H` is used. -/
theorem quadratic_error_descent_identity
    (H H' H'' a a' a'' b b' c V W P : K) (h2 : (2 : K) ≠ 0) :
    quadraticFamily
        (H * a)
        (H' * a + H * a')
        (H'' * a + 2 * H' * a' + H * a'')
        (H' * a + H * b)
        (H'' * a + H' * a' + H' * b + H * b')
        (H'' * a / 2 + H' * b + H * c)
        V W P =
      H * quadraticFamily a a' a'' b b' c V W P := by
  simp [quadraticFamily, T1, T2]
  field_simp [h2]
  ring

/-- The concrete completion proposed from `A=L*H`, `B=L*H'`,
`C=L*H''/2` is identically `H*T2(L)` and hence is not a new row. -/
theorem proposed_completion_is_old_T2
    (L L' L'' H H' H'' V W P : K) (h2 : (2 : K) ≠ 0) :
    quadraticFamily
        (L * H)
        (L' * H + L * H')
        (L'' * H + 2 * L' * H' + L * H'')
        (L * H')
        (L' * H' + L * H'')
        (L * H'' / 2)
        V W P =
      H * T2 L L' L'' V W P := by
  simp [quadraticFamily, T1, T2]
  field_simp [h2]
  ring

def fixedQuadraticFamily
    (A A' A'' B B' C Q Q' Q'' Y R S Z : K) : K :=
  quadraticFamily A A' A'' B B' C
    (Y - Z * Q) (R - Z * Q') (S - Z * Q'')

/-- Mixed finite difference extracting the exact `S*Z` coefficient. -/
theorem fixedQuadraticFamily_SZ
    (A A' A'' B B' C Q Q' Q'' : K) :
    fixedQuadraticFamily A A' A'' B B' C Q Q' Q'' 0 0 1 1 -
        fixedQuadraticFamily A A' A'' B B' C Q Q' Q'' 0 0 1 0 -
        fixedQuadraticFamily A A' A'' B B' C Q Q' Q'' 0 0 0 1 +
        fixedQuadraticFamily A A' A'' B B' C Q Q' Q'' 0 0 0 0 =
      A * Q / 2 := by
  simp [fixedQuadraticFamily, quadraticFamily, T1, T2]
  ring

/-- Once the `T2` parameter is zero, the `R*Z` coefficient is `-B*Q`. -/
theorem fixedQuadraticFamily_RZ_after_A_zero
    (B B' C Q Q' Q'' : K) :
    fixedQuadraticFamily 0 0 0 B B' C Q Q' Q'' 0 1 0 1 -
        fixedQuadraticFamily 0 0 0 B B' C Q Q' Q'' 0 1 0 0 -
        fixedQuadraticFamily 0 0 0 B B' C Q Q' Q'' 0 0 0 1 +
        fixedQuadraticFamily 0 0 0 B B' C Q Q' Q'' 0 0 0 0 =
      -B * Q := by
  simp [fixedQuadraticFamily, quadraticFamily, T1, T2]
  ring

/-- Once the first two parameters are zero, the `Y*Z` coefficient is
`-2*C*Q`. -/
theorem fixedQuadraticFamily_YZ_after_A_B_zero
    (C Q Q' Q'' : K) :
    fixedQuadraticFamily 0 0 0 0 0 C Q Q' Q'' 1 0 0 1 -
        fixedQuadraticFamily 0 0 0 0 0 C Q Q' Q'' 1 0 0 0 -
        fixedQuadraticFamily 0 0 0 0 0 C Q Q' Q'' 0 0 0 1 +
        fixedQuadraticFamily 0 0 0 0 0 C Q Q' Q'' 0 0 0 0 =
      -2 * C * Q := by
  simp [fixedQuadraticFamily, quadraticFamily, T1, T2]
  ring

/-- All three triangular tails have base degree `58g+3e`, beyond the
loosest `SZ` cutoff by 15,436. -/
theorem target_complete_quadratic_tail_gap :
    58 * 180413 + 3 * 81731 = 10709147 /\
      60 * 180413 - (131071 - 2) = 10693711 /\
      10709147 - 10693711 = 15436 /\
      10693711 < 10709147 := by
  norm_num

end ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900

#print axioms ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900.quadratic_error_descent_identity
#print axioms ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900.proposed_completion_is_old_T2
#print axioms ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900.fixedQuadraticFamily_SZ
#print axioms ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900.fixedQuadraticFamily_RZ_after_A_zero
#print axioms ProximityPrize.SubmissionLower.Full187CompleteQuadraticDescentStop6900.fixedQuadraticFamily_YZ_after_A_B_zero
