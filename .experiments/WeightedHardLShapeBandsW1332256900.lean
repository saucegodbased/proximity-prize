import WeightedHardDBandW1332256900

/-! Combined three-way hard L-shaped product-band gate at W=133225. -/
namespace ProximityPrize.SubmissionLower.WeightedHardLShapeBandsW1332256900

open Order2SourceBasisScaffold
open WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900
open WeightedHardJBandW1332256900
open WeightedHardCornerBandW1332256900
open WeightedHardDBandW1332256900

set_option autoImplicit false
set_option Elab.async false
noncomputable section

theorem hard_lshape_product_band_lt_kernel {K : Type*} [Field K]
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P) (fuel : Nat)
    (hprofile : 213≤jetDegree P ∨ 56≤derivativeDegree P ∨
      (212≤jetDegree P ∧ 55≤derivativeDegree P)) :
    helperProductBandSum P fuel<133651239658485317 := by
  rcases hprofile with hjet | hder | hcorner
  · exact (j213_product_band_le P hP hrho hjet fuel).trans_lt (by norm_num)
  · exact (d56_product_band_le P hP hder fuel).trans_lt (by norm_num)
  · exact (corner_product_band_le P hP hcorner.2 hcorner.1 fuel).trans_lt
      (by norm_num)

theorem conservative_hard_margins :
    133651239658485317-133317603599174280=333636059311037 ∧
    133651239658485317-133608913383780120=42326274705197 ∧
    133651239658485317-90689359599610200=42961880058875117 := by
  norm_num

end
end ProximityPrize.SubmissionLower.WeightedHardLShapeBandsW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedHardLShapeBandsW1332256900.hard_lshape_product_band_lt_kernel
