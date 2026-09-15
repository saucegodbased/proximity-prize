import WeightedExtendedLShapeHelperKernelW1332266900
import WeightedExtendedLShapeDeflatedCapacityW1332266900
import WeightedBatchFactorChoice6900
import WeightedIdentityExtendedLShapeIntegrationW1332266900

/-!
# Exact W=133226 helper certificates for extended L-shaped subsets

This is the semantic adapter between the finite-prefix kernel escape and the
strict L-terminal consumer.  The only deliberately external producer is the
strict product-band inequality.  In particular, this module does not import
the comparatively expensive three-way band proof.

The interpolation kernel is indexed by the finite node set itself.  Thus its
rank hypothesis uses exactly `nodeSet.card <= 262144`, with no finiteness or
cardinality assumption on an ambient index type.
-/
namespace ProximityPrize.SubmissionLower.WeightedExtendedLShapeHelperCertificateW1332266900

open scoped BigOperators
open RCN081 RCN095
open Order2SourceBasisScaffold
open Order2SourceSpecializationScaffold
open Order2ValueYCapAllFactorScaffold
open Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter
open WeightedSourceIndex6900 WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900
open WeightedBatchFactorChoice6900
open WeightedIdentityExtendedLShapeIntegrationW1332266900
open WeightedExtendedLShapeHelperKernelW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3500

noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The common weighted helper box has exactly the nested flag
`(10745,2624,2624)` consumed by the W=133226 coupled count. -/
theorem joint_helper_box_flag (H : MvPolynomial (Fin 4) K)
    (hbox : H∈globalOrder2CoefficientBox K
      WeightedExtendedLShapeDeflatedCapacityW1332266900.sourceCutoff
      WeightedExtendedLShapeDeflatedCapacityW1332266900.wordDegree
      WeightedExtendedLShapeDeflatedCapacityW1332266900.jetCap
      WeightedExtendedLShapeDeflatedCapacityW1332266900.derivativeCap
      WeightedExtendedLShapeDeflatedCapacityW1332266900.totalCap) :
    PolynomialInFlag
      WeightedIdentityExtendedLShapeIntegrationW1332266900.R.helperFlag
      (rtySource H) := by
  apply WeightedFactorFlagBudgetW1332246900.rtySource_in_flag_of_weights
  · apply (weightedTotalDegree_le_iff (![0,0,0,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [WeightedIdentityExtendedLShapeIntegrationW1332266900.R.helperFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
      WeightedExtendedLShapeDeflatedCapacityW1332266900.totalCap] using
      (hbox he).2.2.1
  · apply (weightedTotalDegree_le_iff (![0,0,1,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [WeightedIdentityExtendedLShapeIntegrationW1332266900.R.helperFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
      WeightedExtendedLShapeDeflatedCapacityW1332266900.derivativeCap,
      WeightedExtendedLShapeDeflatedCapacityW1332266900.totalCap] using
      (hbox he).2.1
  · apply (weightedTotalDegree_le_iff (![0,1,1,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [WeightedIdentityExtendedLShapeIntegrationW1332266900.R.helperFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
      WeightedExtendedLShapeDeflatedCapacityW1332266900.jetCap,
      WeightedExtendedLShapeDeflatedCapacityW1332266900.derivativeCap,
      WeightedExtendedLShapeDeflatedCapacityW1332266900.totalCap] using
      (hbox he).1

/-- Direct adapter from the deflated cutoff-two source to the exact semantic
helper package used by the extended L-shape descent. -/
theorem jointRegularHelper_of_deflated_source [CharP K 2130706433]
    (nodeSet : Finset I) (x u : I→K) (hinj : Set.InjOn x nodeSet)
    (F C G : MvPolynomial (Fin 4) K) (j : Nat)
    (hF : Prime F) (hFC : ¬F∣C) (hFG : ¬F∣G)
    (hj : j≤WeightedExtendedLShapeDeflatedCapacityW1332266900.stageMax)
    (hC : C≠0) (hG : G≠0)
    (hcontact : ∀ i∈nodeSet,
      contactTruncation K
        WeightedExtendedLShapeDeflatedCapacityW1332266900.contactOrder
        (localSubstitution K (x i) (u i) ((F*C)^j*G))=0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (WeightedExtendedLShapeDeflatedCapacityW1332266900.sourceCutoff-
        j*WeightedExtendedLShapeDeflatedCapacityW1332266900.stageDelta)
      WeightedExtendedLShapeDeflatedCapacityW1332266900.wordDegree
      WeightedExtendedLShapeDeflatedCapacityW1332266900.derivativeCap) :
    JointRegularHelper nodeSet x u F (C^j*G) := by
  have hQ : (F*C)^j*G≠0 :=
    mul_ne_zero (pow_ne_zero j (mul_ne_zero hF.ne_zero hC)) hG
  refine ⟨hF,
    WeightedExtendedLShapeDeflatedCapacityW1332266900.deflated_helper_ne_zero
      F C G j hQ,
    joint_helper_box_flag (C^j*G) ?_,
    WeightedExtendedLShapeDeflatedCapacityW1332266900.deflated_helper_proper
      F C G j hF hFC hFG,?_⟩
  · exact WeightedExtendedLShapeDeflatedCapacityW1332266900.deflated_helper_mem_globalBox
      F C G j hF.ne_zero hQ htight
  · intro P hP ha hFzero hregular
    let support := nodeSet.filter fun i => P.eval (x i)=u i
    apply WeightedExtendedLShapeDeflatedCapacityW1332266900.deflated_helper_vanishes
      F C G P x u support j 2130706433
      (CharP.char_prime_of_ne_zero K (by norm_num))
      (by norm_num [WeightedExtendedLShapeDeflatedCapacityW1332266900.stageMax])
      hj (hinj.mono (Finset.filter_subset _ _))
      (CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num))
      hP ha hQ
    · intro i hi
      exact hcontact i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact htight
    · exact hFzero
    · exact hregular

/-- A factor certificate retains the exact current subset, complementary
product, escape stage, and residual source.  Its final field is precisely the
joint-profile helper consumed by the strict L-shape count. -/
def JointBatchHelperCertificate
    (Q : MvPolynomial (Fin 4) K) (nodeSet : Finset I)
    (nodes values : I→K) (F : MvPolynomial (Fin 4) K) : Prop :=
  ∃ (s : Finset (MvPolynomial (Fin 4) K)) (j : Nat)
    (C G : MvPolynomial (Fin 4) K),
    s⊆positiveTFactors Q ∧ F∈s ∧ (∏ A∈s,A)=F*C ∧
    j≤2624 ∧ C≠0 ∧ G≠0 ∧ ¬F∣C ∧ ¬F∣G ∧
    JointRegularHelper nodeSet nodes values F (C^j*G)

theorem jointBatchHelperCertificate_regular
    (Q : MvPolynomial (Fin 4) K) (nodeSet : Finset I)
    (nodes values : I→K) (F : MvPolynomial (Fin 4) K)
    (hcert : JointBatchHelperCertificate Q nodeSet nodes values F) :
    ∃ H,JointRegularHelper nodeSet nodes values F H := by
  obtain ⟨s,j,C,G,hs,hF,hprod,hj,hC,hG,hFC,hFG,hreg⟩ := hcert
  exact ⟨C^j*G,hreg⟩

/-- The exact certificate assembly.  The numerical premise is the sole
remaining output expected from a product-band producer. -/
theorem heavy_subset_certificate_of_band [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s.Nonempty) (hsub : s⊆positiveTFactors Q)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262144)
    (hband : productBandSum K (∏ F∈s,F)<132483198112574379) :
    ∃ F∈s,JointBatchHelperCertificate Q nodeSet nodes values F := by
  classical
  let Node := {i : I // i∈nodeSet}
  let x : Node→K := fun i => nodes i.1
  let u : Node→K := fun i => values i.1
  let product : MvPolynomial (Fin 4) K := ∏ F∈s,F
  have hirr : ∀ F∈s,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hsub hF)).1
  have hproduct : product≠0 := product_ne_zero s id hirr
  have hrho : 2≤derivativeDegree product :=
    positiveT_product_derivativeDegree s id hs hirr
      (fun F hF => (positiveTFactors_spec Q F (hsub hF)).2.2)
  have hnodeCard : Fintype.card Node≤262144 := by
    simpa only [Node,Fintype.card_coe] using hnodes
  have htwo : (2:K)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num)
  have hband' : productBandSum K product<kernelLower := by
    simpa only [product,kernelLower] using hband
  obtain ⟨j,G,hj,hG,hnot,hkernel,hquotient,htight,hcontact,
      horiginal,hmain,hder⟩ :=
    product_escape_of_band_lt_lower K Node htwo x u hnodeCard product
      hproduct hrho hband'
  obtain ⟨_,_,F,hFs,C,hFprime,hFG,hprod,hFC,hC⟩ :=
    positiveT_subset_escape Q G s hsub hnot
  have hp : product=F*C := hprod
  have htight' : (F*C)^j*G∈weightedCoefficientBox K
      (2130677530-j*47189) 133226 5248 := by
    rw [←hp]
    simpa only [sourceCutoff,stageDelta,wordDegree,derivativeCap] using htight
  have hcontact' : ∀ i∈nodeSet,contactTruncation K 11810
      (localSubstitution K (nodes i) (values i) ((F*C)^j*G))=0 := by
    intro i hi
    have h := hcontact (⟨i,hi⟩ : Node)
    rw [←hp]
    simpa only [x,u,contactOrder] using h
  have hregular : JointRegularHelper nodeSet nodes values F (C^j*G) := by
    apply jointRegularHelper_of_deflated_source nodeSet nodes values hinj
      F C G j hFprime hFC hFG
    · simpa only [stageMax,
        WeightedExtendedLShapeDeflatedCapacityW1332266900.stageMax] using hj
    · exact hC
    · exact hG
    · simpa only [
        WeightedExtendedLShapeDeflatedCapacityW1332266900.contactOrder] using
        hcontact'
    · simpa only [
        WeightedExtendedLShapeDeflatedCapacityW1332266900.sourceCutoff,
        WeightedExtendedLShapeDeflatedCapacityW1332266900.stageDelta,
        WeightedExtendedLShapeDeflatedCapacityW1332266900.wordDegree,
        WeightedExtendedLShapeDeflatedCapacityW1332266900.derivativeCap] using
        htight'
  exact ⟨F,hFs,s,j,C,G,hsub,hFs,hprod,
    (by simpa only [stageMax] using hj),hC,hG,hFC,hFG,hregular⟩

/-- Direct count-facing form of the certificate assembly. -/
theorem heavy_subset_joint_helper_of_band [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s.Nonempty) (hsub : s⊆positiveTFactors Q)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262144)
    (hband : productBandSum K (∏ F∈s,F)<132483198112574379) :
    ∃ F∈s,∃ H,JointRegularHelper nodeSet nodes values F H := by
  obtain ⟨F,hF,hcert⟩ := heavy_subset_certificate_of_band Q s hs hsub
    nodeSet nodes values hinj hnodes hband
  exact ⟨F,hF,jointBatchHelperCertificate_regular Q nodeSet nodes values F
    hcert⟩

/-- The exact `hstep` expected by `hard_lshape_active_scaled_of_joint_step`.
The caller may instantiate `bandProducer` with any independently compiled
three-way product-band theorem. -/
theorem extended_lshape_hstep_of_band_producer [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262144)
    (bandProducer : ∀ (P : MvPolynomial (Fin 4) K),P≠0 →
      2≤derivativeDegree P →
      ((213≤jetDegree P ∧ 4≤derivativeDegree P) ∨
        (33≤jetDegree P ∧ 56≤derivativeDegree P) ∨
        (212≤jetDegree P ∧ 55≤derivativeDegree P)) →
      productBandSum K P<132483198112574379) :
    ∀ T, T⊆positiveTFactors Q → T.Nonempty → ExtendedHeavy id T →
      ∃ F∈T,∃ H,JointRegularHelper nodeSet nodes values F H := by
  intro T hsub hs hheavy
  let product : MvPolynomial (Fin 4) K := ∏ F∈T,F
  have hirr : ∀ F∈T,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hsub hF)).1
  have hproduct : product≠0 := product_ne_zero T id hirr
  have hrho : 2≤derivativeDegree product :=
    positiveT_product_derivativeDegree T id hs hirr
      (fun F hF => (positiveTFactors_spec Q F (hsub hF)).2.2)
  have hprofile : (213≤jetDegree product ∧ 4≤derivativeDegree product) ∨
      (33≤jetDegree product ∧ 56≤derivativeDegree product) ∨
      (212≤jetDegree product ∧ 55≤derivativeDegree product) := by
    simpa only [ExtendedHeavy,product,id_eq] using hheavy
  apply heavy_subset_joint_helper_of_band Q T hs hsub nodeSet nodes values
    hinj hnodes
  simpa only [product] using bandProducer product hproduct hrho hprofile

#print axioms joint_helper_box_flag
#print axioms jointRegularHelper_of_deflated_source
#print axioms jointBatchHelperCertificate_regular
#print axioms heavy_subset_certificate_of_band
#print axioms heavy_subset_joint_helper_of_band
#print axioms extended_lshape_hstep_of_band_producer

end
end ProximityPrize.SubmissionLower.WeightedExtendedLShapeHelperCertificateW1332266900
