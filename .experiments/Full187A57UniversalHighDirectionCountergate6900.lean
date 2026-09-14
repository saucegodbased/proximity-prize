import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
# A57 frozen-Hankel rescue is not universal in the high-direction branch

The target-instance A57 repair reduces to `A + 37 * u1 * B` modulo
`X^262144-1`, with `deg A < 208036` and `deg B < 76965`.  This file records a
single exact missing coefficient for the legal high-degree direction
`u1 = X^132103`.
-/

namespace ProximityPrize.SubmissionLower.Full187A57UniversalHighDirectionCountergate6900

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

variable {K : Type} [Field K]

/-- Generic coefficient obstruction for a truncated low prefix plus a
monomial-shifted truncated prefix. -/
theorem monomial_shift_missing_coefficient
    (A B : K[X]) (c : K) (a b d k : Nat)
    (hA : A.natDegree < a) (hB : B.natDegree < b)
    (hak : a ≤ k) (hk : k = b + d) :
    (A + Polynomial.C c * X ^ d * B).coeff k = 0 := by
  have hA0 : A.coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_le hak)
  have hB0 : B.coeff b = 0 :=
    coeff_eq_zero_of_natDegree_lt hB
  rw [coeff_add, hA0, zero_add, mul_assoc, coeff_C_mul, hk,
    coeff_X_pow_mul, hB0, mul_zero]

/-- The coefficient `X^209068` is absent from every A57 correction using the
high-degree monomial direction `X^132103`.  The largest shifted `B`
coefficient is `132103 + 76964 = 209067`. -/
theorem monomial_high_direction_missing_coefficient
    (A B : K[X]) (hA : A.natDegree < 208036)
    (hB : B.natDegree < 76965) :
    (A + Polynomial.C (37 : K) * X ^ 132103 * B).coeff 209068 = 0 := by
  apply monomial_shift_missing_coefficient A B (37 : K)
    208036 76965 132103 209068 hA hB
  · norm_num
  · norm_num

/-- The adversarial direction lies exactly in the open high-degree branch. -/
theorem monomial_direction_degree :
    (X ^ 132103 : K[X]).natDegree = 132103 := by
  simp

/-- It is root-free on every nonzero evaluation node, including the complete
multiplicative NTT domain. -/
theorem monomial_direction_nonzero_at_nonzero
    (x : K) (hx : x ≠ 0) :
    (X ^ 132103 : K[X]).eval x ≠ 0 := by
  simp [hx]

end ProximityPrize.SubmissionLower.Full187A57UniversalHighDirectionCountergate6900

#print axioms ProximityPrize.SubmissionLower.Full187A57UniversalHighDirectionCountergate6900.monomial_high_direction_missing_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187A57UniversalHighDirectionCountergate6900.monomial_direction_degree
#print axioms ProximityPrize.SubmissionLower.Full187A57UniversalHighDirectionCountergate6900.monomial_direction_nonzero_at_nonzero
