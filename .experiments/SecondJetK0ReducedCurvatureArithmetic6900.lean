import ProximityPrize.Benchmark.TargetLower

/-!
# Reduced-curvature k=0 arithmetic at lower 6900

This receipt checks a strictly shallower alternative to the current m47
profile.  Replacing `(s,L)=(8,3757)` by `(6,5107)` keeps the same terminal
strip `(m,B,U)=(47,16,64)`, hence the same error-CRT width, while removing
two raw curvature layers.  The larger passive-seed cap buys a larger positive
source margin and still fits the exact-stratum consumer allowance.

This is a numerical gate only.  It does not prove conormal rank four.
-/

namespace ProximityPrize.SubmissionLower.SecondJetK0ReducedCurvatureArithmetic6900

set_option autoImplicit false

def agreement : Nat := 180413
def cutoff (_h : Nat) : Nat := 47 * agreement

def activeChartCost (J L : Nat) : Nat :=
  9 * J ^ 4 + 30 * J ^ 3 * L

def inactiveChartCost (J L : Nat) : Nat := activeChartCost J (L + J)

def allChartCost (J L : Nat) : Nat :=
  48 * activeChartCost J L + 4 * inactiveChartCost J L

/-- All seven curvature bands have the required local active-degree cap. -/
theorem caps_47_six :
    ∀ h : Fin 7, 64 ≤ (cutoff h.val + 16 - 1) / 131071 := by
  decide

def sourceColumns : Nat := 84_240_729_954_206
def localRankBound : Nat := 321_352_836

theorem source_margin_47_six :
    262144 * localRankBound + 12_113_822 = sourceColumns := by
  norm_num [localRankBound, sourceColumns]

theorem source_strict_47_six :
    262144 * localRankBound < sourceColumns := by
  norm_num [localRankBound, sourceColumns]

/-- The terminal `Y^(B+m+1)` strip is unchanged from the s=8 profile. -/
theorem terminal_raw_width :
    47 * 180413 - 131071 * (16 + 47 + 1) = 90_867 ∧
      262144 - 180413 = 81_731 ∧ 81_731 < 90_867 := by
  norm_num

theorem active_projection_caps_lt_characteristic :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * 5107) < 2_130_706_433 := by
  norm_num

theorem inactive_projection_caps_lt_characteristic :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * (5107 + 64)) <
      2_130_706_433 := by
  norm_num

theorem one_stratum_chart_cost :
    allChartCost 64 5107 = 2_098_345_279_488 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_chart_cost :
    81_732 * allChartCost 64 5107 = 171_501_956_383_113_216 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_fit_target_mca :
    81_732 * allChartCost 64 5107 < 254_684_620_614_660_120 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_target_mca_residual :
    254_684_620_614_660_120 -
        81_732 * allChartCost 64 5107 = 83_182_664_231_546_904 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

#print axioms source_strict_47_six
#print axioms terminal_raw_width
#print axioms all_exact_strata_fit_target_mca

end ProximityPrize.SubmissionLower.SecondJetK0ReducedCurvatureArithmetic6900
