import WeightedHardLShapeHelperKernelW1332256900
import WeightedHardLShapeDeflatedCapacityW1332256900
import WeightedBatchFactorChoice6900
import WeightedIdentityHardLShapeIntegrationW1332256900

/-!
# Exact W=133225 helper certificates for hard L-shaped subsets

This is the semantic adapter between the finite-prefix kernel escape and the
strict L-terminal consumer.  The only deliberately external producer is the
strict product-band inequality.  In particular, this module does not import
the comparatively expensive three-way band proof.

The interpolation kernel is indexed by the finite node set itself.  Thus its
rank hypothesis uses exactly `nodeSet.card <= 262143`, with no finiteness or
cardinality assumption on an ambient index type.
-/
namespace ProximityPrize.SubmissionLower.WeightedHardLShapeHelperCertificateW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold
open Order2ValueYCapAllFactorScaffold
open WeightedSourceIndex6900 WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900
open WeightedBatchFactorChoice6900
open WeightedIdentityCoupledPartitionAdapterW1332256900
open WeightedIdentityHardLShapeIntegrationW1332256900
open WeightedHardLShapeHelperKernelW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3500

noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

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
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262143)
    (hband : productBandSum K (∏ F∈s,F)<133651239658485317) :
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
  have hnodeCard : Fintype.card Node≤262143 := by
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
      (2130677530-j*47190) 133225 5248 := by
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
        WeightedHardLShapeDeflatedCapacityW1332256900.stageMax] using hj
    · exact hC
    · exact hG
    · simpa only [
        WeightedHardLShapeDeflatedCapacityW1332256900.contactOrder] using
        hcontact'
    · simpa only [
        WeightedHardLShapeDeflatedCapacityW1332256900.sourceCutoff,
        WeightedHardLShapeDeflatedCapacityW1332256900.stageDelta,
        WeightedIdentityHardLShapeIntegrationW1332256900.w,
        WeightedHardLShapeDeflatedCapacityW1332256900.derivativeCap] using
        htight'
  exact ⟨F,hFs,s,j,C,G,hsub,hFs,hprod,
    (by simpa only [stageMax] using hj),hC,hG,hFC,hFG,hregular⟩

/-- Direct count-facing form of the certificate assembly. -/
theorem heavy_subset_joint_helper_of_band [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s.Nonempty) (hsub : s⊆positiveTFactors Q)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262143)
    (hband : productBandSum K (∏ F∈s,F)<133651239658485317) :
    ∃ F∈s,∃ H,JointRegularHelper nodeSet nodes values F H := by
  obtain ⟨F,hF,hcert⟩ := heavy_subset_certificate_of_band Q s hs hsub
    nodeSet nodes values hinj hnodes hband
  exact ⟨F,hF,jointBatchHelperCertificate_regular Q nodeSet nodes values F
    hcert⟩

/-- The exact `hstep` expected by `hard_lshape_active_scaled_of_joint_step`.
The caller may instantiate `bandProducer` with any independently compiled
three-way product-band theorem. -/
theorem hard_lshape_hstep_of_band_producer [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K)
    (nodeSet : Finset I) (nodes values : I→K)
    (hinj : Set.InjOn nodes nodeSet) (hnodes : nodeSet.card≤262143)
    (bandProducer : ∀ (P : MvPolynomial (Fin 4) K),P≠0 →
      2≤derivativeDegree P →
      (213≤jetDegree P ∨ 56≤derivativeDegree P ∨
        (212≤jetDegree P ∧ 55≤derivativeDegree P)) →
      productBandSum K P<133651239658485317) :
    ∀ T, T⊆positiveTFactors Q → T.Nonempty → LHeavy id T →
      ∃ F∈T,∃ H,JointRegularHelper nodeSet nodes values F H := by
  intro T hsub hs hheavy
  let product : MvPolynomial (Fin 4) K := ∏ F∈T,F
  have hirr : ∀ F∈T,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hsub hF)).1
  have hproduct : product≠0 := product_ne_zero T id hirr
  have hrho : 2≤derivativeDegree product :=
    positiveT_product_derivativeDegree T id hs hirr
      (fun F hF => (positiveTFactors_spec Q F (hsub hF)).2.2)
  have hprofile : 213≤jetDegree product ∨ 56≤derivativeDegree product ∨
      (212≤jetDegree product ∧ 55≤derivativeDegree product) := by
    simpa only [LHeavy,product,id_eq] using hheavy
  apply heavy_subset_joint_helper_of_band Q T hs hsub nodeSet nodes values
    hinj hnodes
  simpa only [product] using bandProducer product hproduct hrho hprofile

#print axioms jointBatchHelperCertificate_regular
#print axioms heavy_subset_certificate_of_band
#print axioms heavy_subset_joint_helper_of_band
#print axioms hard_lshape_hstep_of_band_producer

end
end ProximityPrize.SubmissionLower.WeightedHardLShapeHelperCertificateW1332256900
