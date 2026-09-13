import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Target arithmetic for the centered Wronskian shell

This file formalizes only the conditional raw source-strip budget.  It does
not construct the coefficient polynomials or prove `THREE-RHS`.
-/

namespace ProximityPrize.SubmissionLower.Full187CenteredWronskianTargetStrip6900

set_option autoImplicit false

/-- A depth-three error-node Hermite representative is far below every
componentwise source cap found by the exact raw-strip audit. -/
theorem depthThree_fits_component_caps :
    3 * 81731 - 1 = 245192 ∧
      245192 < 918379 ∧
      245192 < 1017060 ∧
      245192 < 1000109 := by
  norm_num

/-- The collected boundary-zero head is legal even when its three
coefficient components are each bounded only by the depth-three budget. -/
theorem boundaryZero_depthThree_margin :
    507335 + 2 * 81731 * 59 = 10151593 ∧
      10151593 < 10824780 ∧
      10824780 - 10151593 = 673187 := by
  norm_num

/-- Every nonterminal pure `c` coefficient fits its literal tapered strip.
The margin grows with `y` because `2e-w=32391>0`. -/
theorem scalar_pure_rows_fit (y : Nat) (hy0 : 1 ≤ y) (hy : y ≤ 60) :
    245192 + 2 * 81731 * (60 - y) < 10824780 - 131071 * y := by
  omega

/-- Every pure contribution from the centered first-jet coefficient fits.
This is the `A Lambda Xi'` part after collecting the `y=0` head. -/
theorem firstJet_pure_rows_fit (y : Nat) (hy0 : 1 ≤ y) (hy : y ≤ 58) :
    245192 + 180413 + (119 - 2 * y) * 81731 - 1 <
      10824780 - 131071 * y := by
  omega

/-- Every `R`-bearing coefficient fits its own one-narrower strip. -/
theorem firstJet_R_rows_fit (y : Nat) (hy : y ≤ 58) :
    245192 + 180413 + (117 - 2 * y) * 81731 <
      10824780 - 131071 * y - 131070 := by
  omega

/-- Every collected `B0` pure coefficient fits, including `y=0`. -/
theorem boundaryCofactor_rows_fit (y : Nat) (hy : y ≤ 59) :
    507335 + 2 * 81731 * (59 - y) <
      10824780 - 131071 * y := by
  omega

/-- Every `Z^k` shift of a shell shape stays below active cap 82, uses at
most one slope carrier, and fits the passive endpoint 2703.  The base shell
starts at seed exponent at least 23 and shifts through `k=2620`. -/
theorem shell_shape_caps
    (y r z k : Nat) (hr : r ≤ 1) (hz : 23 ≤ z)
    (hgrade : y + r + z = 83) (hk : k ≤ 2620) :
    y + r ≤ 82 ∧ r ≤ 21 ∧ 0 ≤ 10 ∧ y + r + z + k ≤ 2703 := by
  omega

end ProximityPrize.SubmissionLower.Full187CenteredWronskianTargetStrip6900
