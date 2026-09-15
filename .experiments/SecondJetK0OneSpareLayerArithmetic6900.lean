import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic for one spare passive layer at lower 6900

This is a parameter-legality receipt, not a rank-four source theorem or a
benchmark candidate.  It changes the literal k0 profile from
`(m,B,s,U,L)=(47,16,8,64,3757)` to `(47,16,8,64,3758)`.  The extra layer
makes multiplication by the passive variable legal on the whole old source.
The companion relative-contact experiment records why this source inclusion
does not by itself make the relative connecting map surjective.

All arithmetic below is kernel checked with `norm_num`; there is no `decide`
or `native_decide`.
-/

namespace ProximityPrize.SubmissionLower.SecondJetK0OneSpareLayerArithmetic6900

set_option autoImplicit false

def agreement : Nat := 180413
def cutoff (_h : Nat) : Nat := 47 * agreement

def activeChartCost (J L : Nat) : Nat :=
  9 * J ^ 4 + 30 * J ^ 3 * L

def inactiveChartCost (J L : Nat) : Nat := activeChartCost J (L + J)

def allChartCost (J L : Nat) : Nat :=
  48 * activeChartCost J L + 4 * inactiveChartCost J L

/-- The active cap/cutoff premise is unchanged by increasing the passive cap. -/
theorem caps_47 :
    ∀ h : Fin 9, 64 ≤ (cutoff h.val + 16 - 1) / 131071 := by
  intro h
  norm_num [cutoff, agreement]

def sourceColumns : Nat := 65_079_223_811_319
def localRankBound : Nat := 248_257_440

/-- Exact full-source surplus at `L=3758`. -/
theorem source_margin_47_one_spare :
    262144 * localRankBound + 25_459_959 = sourceColumns := by
  norm_num [localRankBound, sourceColumns]

theorem source_strict_47_one_spare :
    262144 * localRankBound < sourceColumns := by
  norm_num [localRankBound, sourceColumns]

/-- One extra passive layer buys this much additional source surplus. -/
theorem source_margin_increment :
    25_459_959 - 2_371_080 = 23_088_879 := by
  norm_num

/-- The terminal X/error-CRT width is independent of the passive cap. -/
theorem terminal_raw_width :
    47 * 180413 - 131071 * (16 + 47 + 1) = 90_867 ∧
      262144 - 180413 = 81_731 ∧ 81_731 < 90_867 := by
  norm_num

theorem active_projection_caps_lt_characteristic :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * 3758) < 2_130_706_433 := by
  norm_num

/-- The inactive seed-adding shear replaces `L` by `L+U`. -/
theorem inactive_projection_caps_lt_characteristic :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * (3758 + 64)) <
      2_130_706_433 := by
  norm_num

theorem active_projection_cap_value :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * 3758) = 139_321_344 := by
  norm_num

theorem inactive_projection_cap_value :
    3 * (64 ^ 3 + 3 * 64 ^ 2 * (3758 + 64)) = 141_680_640 := by
  norm_num

theorem one_stratum_chart_cost :
    allChartCost 64 3758 = 1_546_678_960_128 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_chart_cost :
    81_732 * allChartCost 64 3758 = 126_413_164_769_181_696 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_fit_target_mca :
    81_732 * allChartCost 64 3758 < 254_684_620_614_660_120 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_exact_strata_target_mca_residual :
    254_684_620_614_660_120 -
        81_732 * allChartCost 64 3758 = 128_271_455_845_478_424 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

end ProximityPrize.SubmissionLower.SecondJetK0OneSpareLayerArithmetic6900

#print axioms ProximityPrize.SubmissionLower.SecondJetK0OneSpareLayerArithmetic6900.source_strict_47_one_spare
#print axioms ProximityPrize.SubmissionLower.SecondJetK0OneSpareLayerArithmetic6900.inactive_projection_caps_lt_characteristic
#print axioms ProximityPrize.SubmissionLower.SecondJetK0OneSpareLayerArithmetic6900.all_exact_strata_fit_target_mca
