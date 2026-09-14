import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic stop for the Guruswami lattice at lower-6900

This file contains only the integer inequalities used by
`K0_GURUSWAMI_LATTICE_TAPER_RED_6900.md`.  It makes no interpolation-rank
claim.
-/

namespace K0GuruswamiLatticeTaperRed6900

set_option autoImplicit false

def nodeCount : ℕ := 262144
def degreeWeight : ℕ := 131071
def contactOrder : ℕ := 47
def agreement : ℕ := 180413
def sourceCutoff : ℕ := contactOrder * agreement

theorem sourceCutoff_eq : sourceCutoff = 8_479_411 := by
  norm_num [sourceCutoff, contactOrder, agreement]

/-- Twice the exact shifted determinant average is strictly larger than
twice the K0 cutoff for every enlarged degree allowed by the active cap.

The determinant degree is
`n*m*(m+1)/2 + w*u*(u+1)/2`; multiplication by two removes all division.
-/
theorem shiftedDeterminantAverage_exceeds_taper
    (u : ℕ) (hlo : 47 ≤ u) (hhi : u ≤ 64) :
    2 * (u + 1) * sourceCutoff <
      nodeCount * contactOrder * (contactOrder + 1) +
        degreeWeight * u * (u + 1) := by
  interval_cases u <;>
    norm_num [sourceCutoff, nodeCount, contactOrder, degreeWeight, agreement]

/-- At the largest source-legal enlarged degree `u=64`, the exact excess
after clearing the denominator `65` is `17,164,397`. -/
theorem legalEndpoint_exact_gap :
    65 * sourceCutoff + 17_164_397 = 568_326_112 := by
  norm_num [sourceCutoff, contactOrder, agreement]

/-- Even the unconstrained integer optimum `u=66` remains above the K0
cutoff. -/
theorem unconstrainedOptimum_exact_gap :
    67 * sourceCutoff + 17_375_876 = 585_496_413 := by
  norm_num [sourceCutoff, contactOrder, agreement]

/-- The natural primitive order-two tangent separator has generic weighted
degree `2*n-2`, already larger than two agreement units. -/
theorem primitiveTangentSlope_fails :
    2 * agreement < 2 * nodeCount - 2 := by
  norm_num [agreement, nodeCount]

/-- Consequently every individual order-47 product of the generic global
factors has degree at least `47*(n-1)`, far outside the source taper. -/
theorem genericOrder47Factor_fails :
    sourceCutoff < contactOrder * (nodeCount - 1) := by
  norm_num [sourceCutoff, contactOrder, agreement, nodeCount]

#print axioms shiftedDeterminantAverage_exceeds_taper
#print axioms primitiveTangentSlope_fails
#print axioms genericOrder47Factor_fails

end K0GuruswamiLatticeTaperRed6900
