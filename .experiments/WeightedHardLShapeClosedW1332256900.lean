import WeightedHardLShapeBandsW1332256900
import WeightedHardLShapeHelperCertificateW1332256900

/-!
# Closed W=133225 hard L-shaped active-factor theorem

This is the final seam between the separately compiled three-way arithmetic
band and the source/escape/deflation/factor-certificate pipeline.
-/
namespace ProximityPrize.SubmissionLower.WeightedHardLShapeClosedW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold
open Order2ValueYCapAllFactorScaffold
open Order2HereditaryCommonNodeFlagCount6900
open WeightedSourceBoxQuotient6900 WeightedActualProductBandGate6900
open WeightedHardJBandW1332256900
open WeightedHardLShapeBandsW1332256900
open WeightedHardLShapeHelperKernelW1332256900
open WeightedHardLShapeHelperCertificateW1332256900
open WeightedIdentityCoupledPartitionAdapterW1332256900
open WeightedIdentityHardLShapeIntegrationW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3500
noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Definition-level adapter between the band module's variable-fuel sum and
the helper-kernel module's fixed-fuel sum. -/
theorem actual_band_producer
    (P : MvPolynomial (Fin 4) K) (hP : P≠0)
    (hrho : 2≤derivativeDegree P)
    (hprofile : 213≤jetDegree P ∨ 56≤derivativeDegree P ∨
      (212≤jetDegree P ∧ 55≤derivativeDegree P)) :
    productBandSum K P<133651239658485317 := by
  have h := hard_lshape_product_band_lt_kernel P hP hrho 2624 hprofile
  simpa only [WeightedHardLShapeHelperKernelW1332256900.productBandSum,
    WeightedHardLShapeHelperKernelW1332256900.stageMax,
    WeightedHardLShapeHelperKernelW1332256900.sourceCutoff,
    WeightedHardLShapeHelperKernelW1332256900.wordDegree,
    WeightedHardLShapeHelperKernelW1332256900.derivativeCap,
    WeightedHardLShapeHelperKernelW1332256900.stageDelta,
    WeightedHardJBandW1332256900.helperProductBandSum] using h

theorem actual_hard_lshape_hstep [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262143) :
    ∀ T, T⊆positiveTFactors Q → T.Nonempty → LHeavy id T →
      ∃ F∈T,∃ H,JointRegularHelper nodeSet nodes values F H := by
  exact hard_lshape_hstep_of_band_producer Q nodeSet nodes values hinj hnodes
    actual_band_producer

/-- Every source, band, partition, incidence and coupled-budget premise of
the hard active-factor count is now discharged. -/
theorem hard_lshape_active_scaled [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet)
    (hnodes : nodeSet.card=
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤133225)
    (hagrees : ∀ P∈Gamma,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a≤
        (nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v 1453806) :
    (∑ F∈positiveTFactors Q,
        (WeightedIdentityHardLShapeIntegrationW1332256900.regularFamily
          F Gamma).card)*
        (RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a-
          RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v)^2≤
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement := by
  apply hard_lshape_active_scaled_of_joint_step Q hQ hQT hQRT hQJ Gamma
    nodeSet x u hinj hnodes hdegree hagrees hcommon
  apply actual_hard_lshape_hstep Q nodeSet x u hinj
  rw [hnodes]
  norm_num [RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n]

end
end ProximityPrize.SubmissionLower.WeightedHardLShapeClosedW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedHardLShapeClosedW1332256900.actual_band_producer
#print axioms ProximityPrize.SubmissionLower.WeightedHardLShapeClosedW1332256900.actual_hard_lshape_hstep
#print axioms ProximityPrize.SubmissionLower.WeightedHardLShapeClosedW1332256900.hard_lshape_active_scaled
