import WeightedExtendedLShapeBandsW1332266900
import WeightedExtendedLShapeHelperCertificateW1332266900

/-!
# Closed W=133226 extended-L active-factor bound

This module joins the three exact relaxed product bands to the finite-kernel
escape/certificate and the semantic extended-L terminal consumer.  It leaves
no helper-producing premise.
-/
namespace ProximityPrize.SubmissionLower.WeightedExtendedLShapeClosedW1332266900

open scoped BigOperators
open Order2SourceBasisScaffold
open Order2ValueYCapAllFactorScaffold
open Order2HereditaryCommonNodeFlagCount6900
open WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900
open WeightedIdentityExtendedLShapeIntegrationW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The independently checked relaxed bands instantiate exactly the product
band required by the helper kernel. -/
theorem product_band_producer
    (P : MvPolynomial (Fin 4) K) (hP : P≠0)
    (_hrho : 2≤derivativeDegree P)
    (hprofile : (213≤jetDegree P ∧ 4≤derivativeDegree P) ∨
      (33≤jetDegree P ∧ 56≤derivativeDegree P) ∨
      (212≤jetDegree P ∧ 55≤derivativeDegree P)) :
    WeightedExtendedLShapeHelperKernelW1332266900.productBandSum K P<
      132483198112574379 := by
  have h :=
    WeightedExtendedLShapeBandsW1332266900.extended_lshape_product_band_lt_kernel
      P hP hprofile 2624
  simpa only [
    WeightedExtendedLShapeBandsW1332266900.helperProductBandSum,
    WeightedExtendedLShapeBandsW1332266900.sourceCutoff,
    WeightedExtendedLShapeBandsW1332266900.wordDegree,
    WeightedExtendedLShapeBandsW1332266900.derivativeCap,
    WeightedExtendedLShapeBandsW1332266900.stageDelta,
    WeightedExtendedLShapeBandsW1332266900.kernelLower,
    WeightedExtendedLShapeHelperKernelW1332266900.productBandSum,
    WeightedExtendedLShapeHelperKernelW1332266900.stageMax,
    WeightedExtendedLShapeHelperKernelW1332266900.sourceCutoff,
    WeightedExtendedLShapeHelperKernelW1332266900.wordDegree,
    WeightedExtendedLShapeHelperKernelW1332266900.derivativeCap,
    WeightedExtendedLShapeHelperKernelW1332266900.stageDelta] using h

/-- Concrete strict extended-L descent step at all 262144 nodes. -/
theorem extended_lshape_hstep [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card=262144) :
    ∀ T, T⊆positiveTFactors Q → T.Nonempty → ExtendedHeavy id T →
      ∃ F∈T,∃ H,JointRegularHelper nodeSet nodes values F H := by
  apply WeightedExtendedLShapeHelperCertificateW1332266900.extended_lshape_hstep_of_band_producer
    Q nodeSet nodes values hinj (by omega)
  exact product_band_producer

/-- Closed active-factor count for the W=133226 all-node branch. -/
theorem extended_lshape_active_card_le [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hnodes : nodeSet.card=262144)
    (hdegree : ∀ P∈Gamma,P.natDegree≤133226)
    (hagrees : ∀ P∈Gamma,
      180413≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u 68769 1453806) :
    (∑ F∈positiveTFactors Q,(regularFamily F Gamma).card)≤
      247945303343219481 := by
  apply extended_lshape_active_card_le_of_joint_step Q hQ hQT hQRT hQJ
    Gamma nodeSet x u hinj
  · simpa only [WeightedIdentityExtendedLShapeArithmeticW1332266900.n] using
      hnodes
  · intro P hP
    simpa only [WeightedIdentityExtendedLShapeArithmeticW1332266900.w] using
      hdegree P hP
  · intro P hP
    simpa only [WeightedIdentityExtendedLShapeArithmeticW1332266900.a] using
      hagrees P hP
  · simpa only [WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.small] using hcommon
  · exact extended_lshape_hstep Q nodeSet x u hinj hnodes

#print axioms product_band_producer
#print axioms extended_lshape_hstep
#print axioms extended_lshape_active_card_le

end
end ProximityPrize.SubmissionLower.WeightedExtendedLShapeClosedW1332266900
