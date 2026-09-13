import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-!
# Full187 pure-V fat-point arithmetic gate

This is deliberately only the target arithmetic half of the bivariate
fat-point reduction.  The missing algebraic assertion is the proposed
coefficient-independent injectivity of the filtered product ideal; the
companion Singular receipt gives a small counterexample to such a statement
under only `2e < g < 3e`.  In particular this file does not conceal that
missing theorem behind an axiom.
-/

namespace ProximityPrize.SubmissionLower.Full187PureVFatPointArithmeticGate6900

open Nat
open scoped BigOperators

/-- The literal weighted cutoff for `wt X=1`, `wt V=2e`. -/
def cutoff : Nat := 60 * 180413

/-- The target vertical weight. -/
def vWeight : Nat := 2 * 81731

/-- The coefficient width in the pure `V^b` lane after the mandatory
agreement-locator head has saturated. -/
def highLaneWidth (b : Nat) : Nat := cutoff - vWeight * b

theorem target_chamber :
    2 * 81731 < 180413 ∧ 180413 < 3 * 81731 := by
  norm_num

theorem cutoff_value : cutoff = 10824780 := by
  norm_num [cutoff]

theorem vertical_weight_value : vWeight = 163462 := by
  norm_num [vWeight]

/-- The ceiling is genuinely `b=66`, rather than the rounded-down `65`
which disappears in several small controls. -/
theorem b66_is_last_positive_high_lane :
    highLaneWidth 66 = 36288 ∧ 0 < highLaneWidth 66 ∧
      highLaneWidth 67 = 0 := by
  norm_num [highLaneWidth, cutoff, vWeight]

theorem no_high_lane_after_66 (b : Nat) (hb : 67 ≤ b) :
    cutoff ≤ vWeight * b := by
  norm_num [cutoff, vWeight] at *
  omega

/-- The last legal coefficient strip is smaller than one error-locator
degree.  This is an exact boundary fact, not a divisibility conclusion. -/
theorem b66_width_below_error_locator_degree :
    highLaneWidth 66 < 81731 := by
  norm_num [highLaneWidth, cutoff, vWeight]

/-- With the actual NTT inverse representative `A=N⁻¹ X H'`, one has
`deg A=e`, not `e-1`.  The old fixed-stratum endpoint calculation therefore
has this strictly stronger arithmetic form.  It still says nothing about
arbitrary cancellation between different `H`-adic strata. -/
theorem corrected_inverse_packet_endpoint_stop
    (a j r n : Nat)
    (hcontact : 60 ≤ a + r)
    (hendpoints : j + r ≤ n)
    (hcap : n ≤ 66) :
    ¬ a * 81731 + (n - j) * 81731 < 16951 * j := by
  omega

/-- Below the saturation point, the `b`-th lane has exactly the strict
width `b(g-2e)`. -/
theorem unsaturated_width_identity (b : Nat) (hb : b ≤ 60) :
    60 * 180413 - 2 * 81731 * b - (60 - b) * 180413 =
      b * (180413 - 2 * 81731) := by
  omega

/-- The 65 legal lanes `b=2,...,66` have the exact total recorded by the
full source ledger.  This is a closed arithmetic identity, not a finite
rank computation. -/
theorem all_pure_v_source_columns :
    (Finset.Icc 2 60).sum (fun b ↦ b * (180413 - 2 * 81731)) +
      (Finset.Icc 61 66).sum (fun b ↦ cutoff - vWeight * b) =
        33673037 := by
  norm_num [cutoff, vWeight]
  decide

end ProximityPrize.SubmissionLower.Full187PureVFatPointArithmeticGate6900

#print axioms ProximityPrize.SubmissionLower.Full187PureVFatPointArithmeticGate6900.target_chamber
#print axioms ProximityPrize.SubmissionLower.Full187PureVFatPointArithmeticGate6900.b66_is_last_positive_high_lane
#print axioms ProximityPrize.SubmissionLower.Full187PureVFatPointArithmeticGate6900.all_pure_v_source_columns
