import WeightedBatchFactorChoice6900

/-! W=133221 facade for the squarefree positive-T factor selector.

All factorization, normalization, and complementary-product results are
parameter-free and are re-exported from the existing module.  The only
helper-dependent statement is the stage cap: the W=133221 helper has
derivative cap `5008 = 2 * 2504`, so every positive-T product reaches a
stage `j ≤ 2504`.
-/
namespace ProximityPrize.SubmissionLower.WeightedBatchFactorChoiceW1332216900

open WeightedSourceBoxQuotient6900
open Order2SourceBasisScaffold

set_option autoImplicit false
set_option Elab.async false

export WeightedBatchFactorChoice6900
  (product_ne_zero product_pairwise_isRelPrime exists_factor_complement
    positiveT_derivativeDegree positiveT_product_derivativeDegree
    activeFactors_not_associated positiveTFactors_not_associated
    positiveT_subset_escape)

noncomputable section

variable {K : Type*} [Field K]

/-- The exact W=133221 helper-stage cap.  The lower bound `2` is supplied by
every nonempty product of positive-T factors. -/
theorem positiveT_stage_le (P : Poly4 K) (j : Nat)
    (hrho : 2≤derivativeDegree P)
    (hj : j*derivativeDegree P≤5008) : j≤2504 := by
  nlinarith

end
end ProximityPrize.SubmissionLower.WeightedBatchFactorChoiceW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedBatchFactorChoiceW1332216900.positiveT_stage_le
