import Fin4FiftyTwoChartConsumer6900

/-!
# Target arithmetic for the native k=4 second-jet incidence route

The target-positive profile

`(m,B,s,U,L,k,n0) = (148,64,30,200,5465,4,5)`

has source margin `3,553,593,355`.  Applying four derivatives in the
curvature variable lowers the ordinary active-degree cap to `U-4=196` and
the total/seed cap to `L-4=5461`.  This file checks that the already-built
52-chart Fin4 consumer remains far inside both the characteristic and MCA
budgets at those caps.  It is only the arithmetic endpoint: the pointwise
rank-four/source-to-component theorem is deliberately not assumed here.
-/

namespace ProximityPrize.SubmissionLower.SecondJetK4NativeIncidenceArithmetic6900

open Fin4FiftyTwoChartConsumer6900

set_option autoImplicit false

theorem active_projection_caps_lt_characteristic :
    ∀ i, currentTwoBlockProjectionCap 196 5461 i < 2_130_706_433 := by
  apply currentTwoBlockProjectionCap_lt_char <;> norm_num

theorem inactive_projection_caps_lt_characteristic :
    ∀ i, currentTwoBlockProjectionCap 196 (5461 + 196) i <
      2_130_706_433 := by
  apply currentTwoBlockProjectionCap_lt_char <;> norm_num

theorem active_chart_cost_exact :
    activeChartCost 196 5461 = 1_246_845_984_384 := by
  norm_num [activeChartCost]

theorem inactive_chart_cost_exact :
    inactiveChartCost 196 5461 = 1_291_119_656_064 := by
  norm_num [inactiveChartCost, activeChartCost]

theorem all_chart_cost_exact :
    allChartCost 196 5461 = 65_013_085_874_688 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem all_chart_cost_fits_MCA :
    allChartCost 196 5461 < 254_684_620_614_660_120 := by
  norm_num [allChartCost, inactiveChartCost, activeChartCost]

theorem source_margin_gt_four : 4 < 3_553_593_355 := by
  norm_num

end ProximityPrize.SubmissionLower.SecondJetK4NativeIncidenceArithmetic6900

#print axioms ProximityPrize.SubmissionLower.SecondJetK4NativeIncidenceArithmetic6900.active_projection_caps_lt_characteristic
#print axioms ProximityPrize.SubmissionLower.SecondJetK4NativeIncidenceArithmetic6900.inactive_projection_caps_lt_characteristic
#print axioms ProximityPrize.SubmissionLower.SecondJetK4NativeIncidenceArithmetic6900.all_chart_cost_fits_MCA
