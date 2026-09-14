import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic for a retuned k=0 candidate-major source

This is a numerical/source receipt, not a rank-defect recovery theorem or a
benchmark candidate.  The profile `(m,B,s,U,L,k,n0)=(47,16,8,64,3757,0,1)`
keeps enough terminal X width for the literal error set.  A full four-normal
minor has an 801-level agreement window; 103 retuned source cutoffs span the
whole possible agreement range.  The missing semantic input is that original
badness forces full conormal rank four for each retuned contact kernel.
-/

namespace ProximityPrize.SubmissionLower.SecondJetK0RetunedWindowArithmetic6900

set_option autoImplicit false

def agreement : Nat := 180413
def cutoff (_h : Nat) : Nat := 47 * agreement

def activeChartCost (J L : Nat) : Nat :=
  9 * J ^ 4 + 30 * J ^ 3 * L

def inactiveChartCost (J L : Nat) : Nat := activeChartCost J (L + J)

def allChartCost (J L : Nat) : Nat :=
  48 * activeChartCost J L + 4 * inactiveChartCost J L

theorem caps_47 :
    ∀ h : Fin 9, 64 ≤ (cutoff h.val + 16 - 1) / 131071 := by
  decide

def sourceColumns : Nat := 65_061_789_117_960
def localRankBound : Nat := 248_191_020

theorem source_margin_47 :
    262144 * localRankBound + 2_371_080 = sourceColumns := by
  norm_num [localRankBound, sourceColumns]

theorem source_margin_47_literal :
    262144 * 248_191_020 + 2_371_080 = 65_061_789_117_960 := by
  norm_num

theorem source_strict_47 :
    262144 * localRankBound < sourceColumns := by
  norm_num [localRankBound, sourceColumns]

/-! The last raw terminal strip is wider than all target error nodes.  This
does not by itself prove the required coupled Schur/error-peeling theorem. -/
theorem terminal_raw_width :
    47 * 180413 - 131071 * (16 + 47 + 1) = 90_867 ∧
      262144 - 180413 = 81_731 ∧ 81_731 < 90_867 := by
  norm_num

/-! Full four-minor residual:
`3*(A-w)-1-(4*m-3)*r = 148025-185*r`. -/
theorem full_minor_window :
    3 * (180413 - 131071) - 1 = 148_025 ∧
      4 * 47 - 3 = 185 ∧
      185 * 800 ≤ 148_025 ∧ 148_025 < 185 * 801 := by
  norm_num

theorem one_hundred_three_windows_cover_span :
    262144 - 180413 < 103 * 801 := by norm_num

theorem active_projection_caps_lt_characteristic :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * 3757) < 2_130_706_433 := by
  norm_num

theorem inactive_projection_caps_lt_characteristic :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * (3757 + 64)) <
      2_130_706_433 := by norm_num

theorem one_window_chart_cost :
    allChartCost 64 3757 = 1_546_270_015_488 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_windows_chart_cost :
    103 * allChartCost 64 3757 = 159_265_811_595_264 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_windows_fit_target_mca :
    103 * allChartCost 64 3757 < 254_684_620_614_660_120 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

/-! The source/consumer ledger is cheap enough that no width-801 grouping is
needed for the theorem search: one may stratify by the *exact* maximal actual
agreement cardinality.  This keeps `D = 47 * g` and makes every point outside
`G` a genuine nonzero-residual error.  The displayed allowance is the same
post-scalar MCA allowance used above; no extra budget is introduced. -/
theorem exact_agreement_strata_count :
    262144 - 180413 + 1 = 81_732 := by
  norm_num

theorem all_exact_strata_chart_cost :
    81_732 * allChartCost 64 3757 = 126_379_740_905_865_216 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_fit_target_mca :
    81_732 * allChartCost 64 3757 < 254_684_620_614_660_120 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_target_mca_residual :
    254_684_620_614_660_120 -
        81_732 * allChartCost 64 3757 = 128_304_879_708_794_904 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

end ProximityPrize.SubmissionLower.SecondJetK0RetunedWindowArithmetic6900

#print axioms ProximityPrize.SubmissionLower.SecondJetK0RetunedWindowArithmetic6900.source_strict_47
#print axioms ProximityPrize.SubmissionLower.SecondJetK0RetunedWindowArithmetic6900.full_minor_window
#print axioms ProximityPrize.SubmissionLower.SecondJetK0RetunedWindowArithmetic6900.all_windows_fit_target_mca
#print axioms ProximityPrize.SubmissionLower.SecondJetK0RetunedWindowArithmetic6900.all_exact_strata_fit_target_mca
