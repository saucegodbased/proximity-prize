import K0CriticalRawSTwoSeedStaircase6900
import Mathlib.Data.Rat.Defs

/-!
# The naive critical lift has a three-band X-taper obstruction

This file isolates the exact obstruction to globalizing the node-local
critical `S * (Y-W)^47` relation by simply replacing the node values with a
degree-`<g` direction polynomial.  It also checks that two applications of
the raw `R--S` connection (hence at most two ordinary X derivatives of a
coefficient) do not repair that obstruction.
-/

namespace ProximityPrize.SubmissionLower.K0CriticalTailTaperObstruction6900

open Polynomial

set_option autoImplicit false

noncomputable section

def poleDegree : Nat := 47 * 180413

/-- Strict X width of the raw shape `S * Y^y` at the smallest exact-G
target stratum. -/
def rawSYWidth (y : Nat) : Nat :=
  poleDegree - 131071 * y - 131069

/-- If a degree-`g-1` direction is inserted in the naive binomial lift, the
coefficient of `S * Y^y * Z^(47-y)` has this possible X degree. -/
def naiveDirectionDegree (y : Nat) : Nat :=
  (47 - y) * 180412

theorem target_three_bad_bands_and_first_good_band :
    rawSYWidth 0 = 8348342 ∧ naiveDirectionDegree 0 = 8479364 ∧
    rawSYWidth 1 = 8217271 ∧ naiveDirectionDegree 1 = 8298952 ∧
    rawSYWidth 2 = 8086200 ∧ naiveDirectionDegree 2 = 8118540 ∧
    rawSYWidth 3 = 7955129 ∧ naiveDirectionDegree 3 = 7938128 := by
  norm_num [rawSYWidth, naiveDirectionDegree, poleDegree]

/-- Exactly the first three lower-Y bands can overflow in the worst case;
from `y=3` onward even the maximal degree `(47-y)(g-1)` fits. -/
theorem naive_tail_bad_below_three_good_from_three
    (y : Nat) (hy : y ≤ 47) :
    (y < 3 → rawSYWidth y ≤ naiveDirectionDegree y) ∧
      (3 ≤ y → naiveDirectionDegree y < rawSYWidth y) := by
  simp only [rawSYWidth, naiveDirectionDegree, poleDegree]
  omega

/-- Two ordinary derivatives cannot move any of the three overflowing
coefficient bands into its legal strict X window.  Thus the literal
two-step base--R--S connection does not, coefficientwise, span the
`g-w` tail of the naive lift. -/
theorem two_connection_steps_do_not_repair_first_three_bands :
    rawSYWidth 0 ≤ naiveDirectionDegree 0 - 2 ∧
      rawSYWidth 1 ≤ naiveDirectionDegree 1 - 2 ∧
      rawSYWidth 2 ≤ naiveDirectionDegree 2 - 2 := by
  norm_num [rawSYWidth, naiveDirectionDegree, poleDegree]

/-- Degree of a twice differentiated monomial when the falling-factorial
coefficient survives.  Keeping the exponent symbolic avoids evaluating a
multi-million-term polynomial. -/
theorem natDegree_second_derivative_X_pow
    {K : Type*} [Field K] (n : Nat) (hn : 2 ≤ n)
    (hcast : (n : K) * (n - 1 : Nat) ≠ 0) :
    (((X : K[X]) ^ n).derivative.derivative).natDegree = n - 2 := by
  rw [derivative_X_pow, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X_pow]
  have hcoeff : (n : K) * ((n - 1 : Nat) : K) ≠ 0 := by
    simpa only [Nat.cast_sub (by omega)] using hcast
  rw [← mul_assoc, ← C_mul,
    natDegree_C_mul_X_pow _ _ hcoeff]
  omega

/-- Concrete characteristic-zero witness: the second derivative of the
worst first coefficient still has degree far beyond the legal S window. -/
theorem monomial_second_derivative_still_outside_taper :
    rawSYWidth 0 ≤
      (((X : ℚ[X]) ^ 8479364).derivative.derivative).natDegree := by
  rw [natDegree_second_derivative_X_pow 8479364 (by norm_num) (by norm_num)]
  norm_num [rawSYWidth, poleDegree]

/-- The local nilpotent staircase itself has tiny passive support.  Even
after allowing the robust critical prefix `Z^0,Z^1`, every companion term
has passive exponent at most 48, independently of any Newton quotient
degree. -/
theorem shifted_critical_passive_degree_le_48
    (y z b : Nat) (hy : y < 47) (hz : z ≤ 47 - y) (hb : b ≤ 1) :
    y + (z + b) ≤ 48 := by
  omega

#print axioms target_three_bad_bands_and_first_good_band
#print axioms naive_tail_bad_below_three_good_from_three
#print axioms two_connection_steps_do_not_repair_first_three_bands
#print axioms monomial_second_derivative_still_outside_taper
#print axioms shifted_critical_passive_degree_le_48

end

end ProximityPrize.SubmissionLower.K0CriticalTailTaperObstruction6900
