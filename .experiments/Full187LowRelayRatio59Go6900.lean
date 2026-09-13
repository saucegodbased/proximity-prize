import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full187 low normal relay: the ratio-59 first-jet bridge

The mixed-`H` binomial ladder at normal degree 60 reduces modulo the error
locator to a multiple of `V^60`, and consequently has first `E` and `T*R`
ratios 60.  Dropping the normal degree by one and supplying the one missing
agreement-contact factor gives the two-row relay

`L * (U*V^59 - H^3*Z*V^57*J1)`.

It still cancels at the pure seed `V=-H^2*Z, J1=H*U*Z`, but its nonzero
error reduction is `L*U*V^59`, whose two first ratios are 59.  Pairing it
with the degree-60 two-row binomial permits the exact first-jet convex
combination `-58 V^60 + 59 V^59`, which has value and first jet both one.

This is a first-jet producer only.  It does not claim the remaining Hasse
layers, the three prescribed RHS, or the independent Z direction.
-/

namespace ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [CommRing K]

/-- The already-known degree-60 two-row seed cancellation. -/
theorem high_binomial_pure_seed_cancel (H U Z : K) :
    U * (-(H ^ 2 * Z)) ^ 60 -
        H ^ 3 * Z * (-(H ^ 2 * Z)) ^ 58 * (H * U * Z) = 0 := by
  ring

/-- The smallest lower-normal-degree relay.  The normal weighted degrees
are 59 for both `V^59` and `V^57*J1`; the external `L` supplies the one
remaining agreement-contact order. -/
theorem low_relay_pure_seed_cancel (L H U Z : K) :
    L * (U * (-(H ^ 2 * Z)) ^ 59 -
        H ^ 3 * Z * (-(H ^ 2 * Z)) ^ 57 * (H * U * Z)) = 0 := by
  ring

/-- The first `J2`/`S` candidate from the same-stratum checkerboard does
cancel at the pure seed.  Its least `J1,J2` degree is two, so it cannot
change a value or a first normal jet at the normalized base where both
normal coordinates vanish. -/
theorem j2_three_row_pure_seed_cancel (H U B Z : K) :
    B * (-(H ^ 2 * Z)) ^ 52 * (H * U * Z) ^ 4 -
        (B - U ^ 2) * (-(H ^ 2 * Z)) ^ 53 * (H * U * Z) ^ 2 * (B * Z) -
          U ^ 2 * (-(H ^ 2 * Z)) ^ 54 * (B * Z) ^ 2 = 0 := by
  ring

/-- The three-row high square is included to make the 5-row relay test
literal rather than an appeal to a homogeneous abstraction. -/
theorem high_square_pure_seed_cancel (H U Z : K) :
    U ^ 2 * (-(H ^ 2 * Z)) ^ 60 -
        2 * U * H ^ 3 * Z * (-(H ^ 2 * Z)) ^ 58 * (H * U * Z) +
          H ^ 6 * Z ^ 2 * (-(H ^ 2 * Z)) ^ 56 * (H * U * Z) ^ 2 = 0 := by
  ring

/-- The four-row high cubic is the source-legal maximum of the original
binomial chain.  It supplies the 6-row test when paired with the low relay. -/
theorem high_cubic_pure_seed_cancel (H U Z : K) :
    U ^ 3 * (-(H ^ 2 * Z)) ^ 60 -
        3 * U ^ 2 * H ^ 3 * Z * (-(H ^ 2 * Z)) ^ 58 * (H * U * Z) +
          3 * U * H ^ 6 * Z ^ 2 * (-(H ^ 2 * Z)) ^ 56 * (H * U * Z) ^ 2 -
            H ^ 9 * Z ^ 3 * (-(H ^ 2 * Z)) ^ 54 * (H * U * Z) ^ 3 = 0 := by
  ring

/-- Literal normal/contact bookkeeping for the two-row lower relay. -/
theorem low_relay_normal_degree_and_caps :
    59 = 59 + 2 * 0 + 3 * 0 ∧
      59 = 57 + 2 * 1 + 3 * 0 ∧
      60 - 59 = 1 ∧
      57 + 1 ≤ 82 ∧ 1 ≤ 21 ∧ 0 ≤ 10 ∧ 57 + 1 + 1 ≤ 2703 := by
  norm_num

/-- Exact strict literal-strip ledger.  For normal degree `n` and normal
stratum `r=c+2d`, the established pure-tail window is
`n*(g-2e)-(g-2e-1)*r`.  The two new low rows have common positive margin
475823 after a degree-`<e` CRT multiplier.  The recorded 2-, 5-, and 6-row
high partners are included so every tested packet has literal positive
margins term by term. -/
theorem literal_strip_ledger :
    343873 < 1017060 ∧ 326923 < 1000110 ∧
      1017060 - 343873 = 673187 ∧
      1000110 - 326923 = 673187 ∧
    524286 < 1000109 ∧ 507336 < 983159 ∧
      1000109 - 524286 = 475823 ∧
      983159 - 507336 = 475823 ∧
    606016 < 1017060 ∧ 589066 < 1000110 ∧ 572116 < 983160 ∧
      1017060 - 606016 = 411044 ∧
    868159 < 1017060 ∧ 851209 < 1000110 ∧ 834259 < 983160 ∧
      817309 < 966210 ∧ 1017060 - 868159 = 148901 := by
  norm_num

/-- The degree-59 relay has a different reduction ratio from the degree-60
ladder.  This is the scalar calculation behind the first `E` *and* first
`T*R` coefficient, since both occur linearly through the same local
increment of `V`. -/
theorem ratio_59_relay_matches_value_and_first_jet (f : K) :
    let P : K[X] :=
      C (-(58 : K) * f) * (1 + X) ^ 60 +
        C ((59 : K) * f) * (1 + X) ^ 59
    P.eval 0 = f ∧ P.derivative.eval 0 = f := by
  dsimp
  constructor
  · simp
    ring
  · have h60 (a : K) :
        ((C a * (1 + X) ^ 60).derivative).eval 0 = 60 * a := by
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
      rw [derivative_pow]
      simp
      ring
    have h59 (a : K) :
        ((C a * (1 + X) ^ 59).derivative).eval 0 = 59 * a := by
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
      rw [derivative_pow]
      simp
      ring
    rw [derivative_add, eval_add, h60, h59]
    ring

/-- The two scalar amplitudes used above are forced by value and first-jet
matching: the degree-60 amplitude is `-58*f` and the degree-59 amplitude is
`59*f`.  Thus this is not a heuristic ratio average. -/
theorem ratio_solution_is_exact (A B f : K)
    (hvalue : A + B = f) (hjet : 60 * A + 59 * B = f) :
    A = -(58 : K) * f ∧ B = (59 : K) * f := by
  constructor
  · linear_combination hjet - 59 * hvalue
  · linear_combination 60 * hvalue - hjet

end

end ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900

#print axioms ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900.low_relay_pure_seed_cancel
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900.j2_three_row_pure_seed_cancel
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900.literal_strip_ledger
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900.ratio_59_relay_matches_value_and_first_jet
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayRatio59Go6900.ratio_solution_is_exact
