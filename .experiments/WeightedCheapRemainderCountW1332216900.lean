import WeightedFactorFlagBudgetW1332216900
import WeightedBatchFactorChoice6900
import WeightedRepresentativeCountLedgerW1332216900

/-! Cheap remainder count, charged over individual original factors.
No regularity of their possibly colliding product is assumed. -/
namespace ProximityPrize.SubmissionLower.WeightedCheapRemainderCountW1332216900
open scoped BigOperators
open RCN001 RCN066 RCN071 RCN081 RCN084 RCN095 RCN135 RCN136 RCN319
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2ReducedCutScaffold Order2FlagTwoCutAdapter
open Order2FlagComponentAssignedAdapter
open Order2HereditaryCommonNodeFlagCount6900 Order2HereditaryActiveSurface6900
open WeightedSourceBoxQuotient6900 WeightedActualProductBandGate6900
open WeightedFactorFlagBudgetW1332216900 WeightedBatchFactorChoice6900
open WeightedRepresentativeCountLedgerW1332216900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 650000
variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

def regularFamily (F : MvPolynomial (Fin 4) K) (Gamma : Finset (Polynomial K)) :
    Finset (Polynomial K) :=
  Gamma.filter fun P => jetSpecialization2 P F=0 ∧
    jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0

def cheapReducedCut (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  rtySurfaceMap (polynomialEmbedding K)
    (reducedAgreementNumerator2 F 27 w (fun j => (j.factorial : K)⁻¹) x u)

theorem cheapReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F w x u-cheapReducedCut F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F 27 w
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,cheapReducedCut,map_sub,rtySurfaceMapHom_apply] using h

theorem cheapReducedCut_in_flag (F : MvPolynomial (Fin 4) K)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤54)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤207) (x u : K) :
    PolynomialInFlag cheapAgreement (cheapReducedCut F x u) := by
  have hTdegree : F.degreeOf 3≤27 := by rw [← T_weight_eq_degreeOf]; exact hT
  apply (support_subset_flagSupport_iff _ _).mp
  exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F w 207 54 27
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hTdegree hRT hJ (fun j => (j.factorial : K)⁻¹) x u

theorem cheap_regular_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤54)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤207)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=262144)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    Gamma.card*(a-v)^2≤(n-v)^2*
      flagMixed (exactFlag (rtySource F)) cheapAgreement cheapAgreement := by
  have hsource : PolynomialInFlag cheapFlag (rtySource F) :=
    rtySource_in_flag_of_weights F cheapFlag hT hRT hJ
  have hsmallCurve : small*(a-v)≤(nodes.card-v)*cheapAgreement.all := by
    rw [hn]
    exact small_absorption_gates.1
  have hsmallSurface : small*(a-v)^2≤(nodes.card-v)^2*cheapAgreement.all^2 := by
    rw [hn]
    exact small_absorption_gates.2.1
  have hgate : (cheapAgreement.yz+cheapAgreement.all)*cheapFlag.all+
      (cheapFlag.yz+cheapFlag.all)*cheapAgreement.all<prime := by
    have h := source_and_projection_gates
    rw [h.2.2.2.2.2.1]
    exact h.2.2.2.2.2.2.1
  have h := original_regular_of_congruent_active_flags F hF Gamma nodes x u hinj
    prime w a v small (by norm_num [w]) (by norm_num [w,prime])
    (by norm_num [prime]) (by norm_num [w,a]) (by norm_num [v,a])
    (by rw [hn]; norm_num [a]) hdegree hsolution hregular hagreement hcommon
    (fun i => cheapReducedCut F (x i) (u i))
    (fun i _ => cheapReducedCut_congruent F (x i) (u i))
    (exactFlag (rtySource F)) cheapFlag cheapAgreement
    (polynomialIn_exactFlag _) hsource
    (fun i _ => cheapReducedCut_in_flag F hT hRT hJ (x i) (u i))
    hsmallCurve hsmallSurface source_and_projection_gates.1 hgate
  simpa only [hn,n] using h

/-- Sum the regular solution families of the original remaining factors.
The common-node premise is hereditary on Gamma and is merely restricted to
each factor family. No common-curve or product-regularity premise is added. -/
theorem cheap_remainder_scaled [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s⊆positiveTFactors Q)
    (hJ : jetDegree (∏ F∈s,F)≤207) (hrho : derivativeDegree (∏ F∈s,F)≤54)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=262144)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (∑ F∈s,(regularFamily F Gamma).card)*(a-v)^2≤
      twoIncidenceNumerator cheapFlag cheapAgreement := by
  let product : MvPolynomial (Fin 4) K := ∏ F∈s,F
  have hirr : ∀ F∈s,Irreducible F := fun F hF => (positiveTFactors_spec Q F (hs hF)).1
  have hproduct : product≠0 := product_ne_zero s id hirr
  have hweights := cheap_product_weight_bounds product hJ hrho
  have hfactor (F : ↥s) :
      (regularFamily F.1 Gamma).card*(a-v)^2≤(n-v)^2*
        flagMixed (exactFlag (rtySource F.1)) cheapAgreement cheapAgreement := by
    have hdvd : F.1∣product := Finset.dvd_prod_of_mem id F.2
    have hT := (weightedTotalDegree_le_of_dvd ![0,0,0,1] F.1 product hdvd hproduct).trans hweights.1
    have hRT := (weightedTotalDegree_le_of_dvd ![0,0,1,1] F.1 product hdvd hproduct).trans hweights.2.1
    have hTotal := (weightedTotalDegree_le_of_dvd ![0,1,1,1] F.1 product hdvd hproduct).trans hweights.2.2
    have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
    exact cheap_regular_scaled F.1 (hirr F.1 F.2).ne_zero hT hRT hTotal
      (regularFamily F.1 Gamma) nodes x u hinj hn
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2.1)
      (fun P hP => (Finset.mem_filter.mp hP).2.2)
      (fun P hP => hagreement P (hsub hP)) (hereditaryCommonCap_mono hcommon hsub)
  have hsum := exactFlag_cumulative_of_weight_bounds s product hproduct dvd_rfl
    cheapFlag hweights.1 hweights.2.1 hweights.2.2
  have h := aggregate_scaled_flags (fun F : ↥s => (regularFamily F.1 Gamma).card)
    (fun F : ↥s => exactFlag (rtySource F.1)) cheapFlag cheapAgreement cheapAgreement
    ((a-v)^2) ((n-v)^2) hfactor hsum.1 hsum.2.1 hsum.2.2
  have heq : (∑ F : ↥s, (regularFamily F.1 Gamma).card)=
      ∑ F∈s,(regularFamily F Gamma).card :=
    Finset.sum_coe_sort s (fun F : MvPolynomial (Fin 4) K => (regularFamily F Gamma).card)
  rw [heq] at h
  unfold twoIncidenceNumerator
  exact h

theorem cheap_remainder_card_le [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s⊆positiveTFactors Q)
    (hJ : jetDegree (∏ F∈s,F)≤207) (hrho : derivativeDegree (∏ F∈s,F)≤54)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=262144)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (∑ F∈s,(regularFamily F Gamma).card)≤cheapRegularCap := by
  exact count_le_of_scaled _ _ _ _ (by norm_num [a,v])
    (cheap_remainder_scaled Q s hs hJ hrho Gamma nodes x u hinj hn hdegree hagreement hcommon)
    active_scaled_caps.1

end
end ProximityPrize.SubmissionLower.WeightedCheapRemainderCountW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedCheapRemainderCountW1332216900.cheapReducedCut_in_flag
#print axioms ProximityPrize.SubmissionLower.WeightedCheapRemainderCountW1332216900.cheap_regular_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedCheapRemainderCountW1332216900.cheap_remainder_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedCheapRemainderCountW1332216900.cheap_remainder_card_le
