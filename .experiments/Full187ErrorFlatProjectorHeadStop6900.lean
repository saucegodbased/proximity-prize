import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full187 error-flat Taylor projector: exact identities and source-head STOP

The classical local projector idea is algebraically sound.  In the retained
control `Q=H^2`, write the error contact chart as

`Y = 1 + E + T*R - T^2*S/2 + Z*Q`.

Then `U1=Y` gives an order-one error-flat factor `1-U1`; subtracting a
first-order Taylor coordinate times `R` gives order two; and subtracting a
second-order coordinate times `R`, adding its square times `S/2`, and
removing `Z*Q` gives order three.

But a projector which is zero at the candidate graph and equals one through
error contact order sixty must already have pure-`Y` degree at least twenty:
on `R=S=Z=0`, error contact is `Y=1+E` and `E` has weight three.  Multiplying
any of the locator normals `F0,F1,F2` by such a nonconstant projector leaves
a top `Y^n*Y/R/S` coefficient containing `L^59`.  The literal Full187 width
for that active shape is smaller even for `n=1`, and at `n=20` misses by
2,572,076--2,572,078 degrees.  Thus the proposed `Fi*(1-K)` projector route
is source-impossible before denominator normalization is considered.

This stops only multiplicative error-flat projectors preserving the locator
normal by a factor.  It does not stop cancellations among unrelated literal
source rows.
-/

namespace ProximityPrize.SubmissionLower.Full187ErrorFlatProjectorHeadStop6900

open Polynomial

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- The raw order-one error-flat unit. -/
theorem error_flat_unit_one_identity
    (E T R S Z Q Y : K)
    (hY : Y = 1 + E + T * R - T ^ 2 * S / 2 + Z * Q) :
    1 - Y = -E - T * R + T ^ 2 * S / 2 - Z * Q := by
  rw [hY]
  ring

/-- If `tau1=T+O(T^2)`, subtracting `tau1*R` removes the order-one
transverse term.  The displayed identity retains every leakage term. -/
theorem error_flat_unit_two_identity
    (E T R S Z Q Y tau1 : K)
    (hY : Y = 1 + E + T * R - T ^ 2 * S / 2 + Z * Q) :
    1 - (Y - tau1 * R) =
      -E - (T - tau1) * R + T ^ 2 * S / 2 - Z * Q := by
  rw [hY]
  ring

/-- If `tau2=T+O(T^3)`, its square is `T^2+O(T^3)`.  The denominator-free
shape of the order-three retraction is therefore
`Y-tau2*R+tau2^2*S/2-Z*Q`. -/
theorem error_flat_unit_three_identity
    (E T R S Z Q Y tau2 : K)
    (hY : Y = 1 + E + T * R - T ^ 2 * S / 2 + Z * Q) :
    1 - (Y - tau2 * R + tau2 ^ 2 * S / 2 - Z * Q) =
      -E - (T - tau2) * R + (T ^ 2 - tau2 ^ 2) * S / 2 := by
  rw [hY]
  ring

/-- Univariate Hermite obstruction behind every such projector.  Vanishing
at the candidate point `Y=0` and agreement with one to order twenty at
`Y=1` force degree at least twenty. -/
theorem error_projector_degree_at_least_twenty
    (P : K[X]) (hzero : P.eval 0 = 0)
    (hflat : (Polynomial.X - 1) ^ 20 ∣ 1 - P) :
    20 ≤ P.natDegree := by
  have hdiff : (1 : K[X]) - P ≠ 0 := by
    intro h
    have heval := congrArg (Polynomial.eval 0) h
    simp [hzero] at heval
  have hdegree := Polynomial.natDegree_le_of_dvd hflat hdiff
  have hlinear : (Polynomial.X - (1 : K[X])).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C (1 : K)
  rw [Polynomial.natDegree_pow, hlinear] at hdegree
  have hupper := Polynomial.natDegree_sub_le (1 : K[X]) P
  by_contra hsmall
  have hP : P.natDegree < 20 := Nat.lt_of_not_ge hsmall
  have hOne : (1 : K[X]).natDegree < 20 := by simp
  omega

/-- Already one extra active projector degree is incompatible with the
`L^59*Y` diagonal of `F0`. -/
theorem any_nonconstant_F0_projector_head_red
    (n : Nat) (hn : 1 ≤ n) :
    60 * 180413 - 131071 * (n + 1) ≤ 59 * 180413 := by
  omega

/-- The same statement for the `L^59*R` diagonal of `F1`. -/
theorem any_nonconstant_F1_projector_head_red
    (n : Nat) (hn : 1 ≤ n) :
    60 * 180413 - 131071 * n - (131071 - 1) ≤ 59 * 180413 := by
  omega

/-- And for the `L^59*S` diagonal of `F2`. -/
theorem any_nonconstant_F2_projector_head_red
    (n : Nat) (hn : 1 ≤ n) :
    60 * 180413 - 131071 * n - (131071 - 2) ≤ 59 * 180413 := by
  omega

/-- Exact gaps at the unavoidable minimum projector degree `n=20`. -/
theorem target_minimum_projector_head_gaps :
    59 * 180413 - (60 * 180413 - 131071 * 21) = 2572078 ∧
      59 * 180413 -
          (60 * 180413 - 131071 * 20 - (131071 - 1)) = 2572077 ∧
      59 * 180413 -
          (60 * 180413 - 131071 * 20 - (131071 - 2)) = 2572076 := by
  norm_num

/-- The suggested compact factorizations have respectively 29,30,31
projector factors and therefore much larger diagonal overruns. -/
theorem suggested_unit_product_head_gaps :
    8 + 11 + 10 = 29 ∧
      10 + 10 + 10 = 30 ∧
      11 + 11 + 9 = 31 ∧
      59 * 180413 - (60 * 180413 - 131071 * 30) = 3751717 ∧
      59 * 180413 -
          (60 * 180413 - 131071 * 30 - (131071 - 1)) = 3882787 ∧
      59 * 180413 -
          (60 * 180413 - 131071 * 31 - (131071 - 2)) = 4013857 := by
  norm_num

end


end ProximityPrize.SubmissionLower.Full187ErrorFlatProjectorHeadStop6900

#print axioms ProximityPrize.SubmissionLower.Full187ErrorFlatProjectorHeadStop6900.error_flat_unit_three_identity
#print axioms ProximityPrize.SubmissionLower.Full187ErrorFlatProjectorHeadStop6900.error_projector_degree_at_least_twenty
#print axioms ProximityPrize.SubmissionLower.Full187ErrorFlatProjectorHeadStop6900.any_nonconstant_F0_projector_head_red
#print axioms ProximityPrize.SubmissionLower.Full187ErrorFlatProjectorHeadStop6900.target_minimum_projector_head_gaps
