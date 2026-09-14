import Order2FixedSecondSourceAdapter
import WeightedRepresentativeCountLedgerW1332216900
import WeightedBatchHelperCertificateW1332216900

/-! Proper-helper one-incidence count with the actual hereditary cap. Global
prime contraction is applied before generic factor counting; original-factor
regularity is retained at collisions. -/
namespace ProximityPrize.SubmissionLower.WeightedProperHelperCountW1332216900
open scoped Classical BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135 RCN136 RCN319
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter Order2FlagComponentAssignedAdapter
open Order2FixedSecondSourceAdapter Order2HereditaryCommonNodeFlagCount6900
open Order2SourceBasisScaffold Order2ReducedCutScaffold
open WeightedBatchHelperCertificateW1332216900 WeightedRepresentativeCountLedgerW1332216900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
variable {K : Type} [Field K]
local instance {A : Type*} : DecidableEq A := Classical.decEq A

theorem fixed_second_hereditary_scaled
    (F H : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hpos : 0<F.degreeOf 1+F.degreeOf 2+F.degreeOf 3) (hproper : ¬F∣H)
    (Gamma : Finset (Polynomial K)) {I : Type} (nodes : Finset I) (x u : I→K)
    (pchar W A V small : Nat) [CharP K pchar]
    (hchar : W<pchar) (hVA : V<A) (hAn : A≤nodes.card)
    (hdegree : ∀ P∈Gamma,P.natDegree≤W)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hHsolution : ∀ P∈Gamma,jetSpecialization2 P H=0)
    (hagrees : ∀ P∈Gamma,A≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u V small)
    (cut : I→MvPolynomial (Fin 3) (GenericField K))
    (hcongruent : ∀ i∈nodes,rtySource F∣rtyAgreement F W (x i) (u i)-cut i)
    (pCount pGate q r : FlagDegree)
    (hSourceCount : PolynomialInFlag pCount (rtySource F))
    (hSourceGate : PolynomialInFlag pGate (rtySource F))
    (hSecond : PolynomialInFlag q (rtySource H))
    (hCut : ∀ i∈nodes,PolynomialInFlag r (cut i))
    (hsmall : small*(A-V)≤(nodes.card-V)*r.all)
    (hSourceDegree : pGate.zOnly+pGate.yz+pGate.all<pchar)
    (hgateR : q.all*(pGate.zOnly+pGate.yz+pGate.all)+
      pGate.all*(q.zOnly+q.yz+q.all)<pchar)
    (hgateY : (q.yz+q.all)*pGate.all+(pGate.yz+pGate.all)*q.all<pchar) :
    Gamma.card*(A-V)≤(nodes.card-V)*flagMixed pCount q r := by
  classical
  let S (g : ↑(activeFactors (rtySource F) (rtySource H))) :=
    fixedSecondFactorPolynomials F H Gamma g
  have hSourceNe : rtySource F≠0 :=
    (MvPolynomial.renameEquiv (GenericField K) rtyCycle).injective.ne
      (surfaceMap_ne_zero (polynomialEmbedding K)
        (polynomialEmbedding_injective K) F hF.ne_zero)
  have hcover : Gamma⊆Finset.univ.biUnion S := by
    intro P hP
    have hz : MvPolynomial.eval (rtyJetPoint2 P) (rtySource F)=0 := by
      rw [rtySource,eval_rtySurface_jetPoint2,hsolution P hP,map_zero]
    have hd : MvPolynomial.eval (rtyJetPoint2 P)
        (MvPolynomial.pderiv (1 : Fin 3) (rtySource F))≠0 := by
      rw [rtySource,pderiv_middle_rtySurfaceMap,eval_rtySurface_jetPoint2]
      intro heq
      apply hregular P hP
      apply polynomialEmbedding_injective K
      simpa only [map_zero] using heq
    obtain ⟨g,hg⟩ := exists_fixedSecond_activeFactor_of_regular_point
      F H hF hpos hproper (rtyJetPoint2 P) hz hd
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hP,hg⟩⟩
  have hfactor (g : ↑(activeFactors (rtySource F) (rtySource H))) :
      (S g).card*(A-V)≤(nodes.card-V)*flagMixed (exactFlag g.1) q r := by
    have hg := activeFactors_spec (rtySource F) (rtySource H) g
    have hsub : S g⊆Gamma := Finset.filter_subset _ _
    have hHpoint : ∀ P∈S g,MvPolynomial.eval (rtyJetPoint2 P) (rtySource H)=0 := by
      intro P hP
      rw [rtySource,eval_rtySurface_jetPoint2,hHsolution P (hsub hP),map_zero]
    have hgpGate : PolynomialInFlag pGate g.1 :=
      polynomialInFlag_of_dvd pGate g.1 (rtySource F) hg.2.1 hSourceNe hSourceGate
    have hgates := literalProjectionGates_of_flag_bounds pchar g.1
      (rtySource H) (rtyRegularity F) pGate q hg.1 hg.2.2.1
      hgpGate hSecond hSourceDegree hgateR hgateY
    exact proper_cut_of_literal_gates F g.1 (rtySource H) hg.1 hg.2.1
      hg.2.2.1 hg.2.2.2 (S g) nodes x u pchar W A V small hchar hVA hAn
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => hsolution P (hsub hP))
      (fun P hP => hregular P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2) hHpoint
      (fun P hP => hagrees P (hsub hP))
      (hereditaryCommonCap_mono hcommon hsub) cut hcongruent
      (exactFlag g.1) q r (polynomialIn_exactFlag g.1) hSecond hCut hsmall
      hgates.1 hgates.2
  calc
    Gamma.card*(A-V)≤(Finset.univ.biUnion S).card*(A-V) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
    _≤(∑ g : ↑(activeFactors (rtySource F) (rtySource H)),(S g).card)*(A-V) :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _=∑ g : ↑(activeFactors (rtySource F) (rtySource H)),(S g).card*(A-V) := by
      rw [Finset.sum_mul]
    _≤∑ g : ↑(activeFactors (rtySource F) (rtySource H)),
        (nodes.card-V)*flagMixed (exactFlag g.1) q r :=
      Finset.sum_le_sum fun g _ => hfactor g
    _=(nodes.card-V)*(∑ g : ↑(activeFactors (rtySource F) (rtySource H)),
        flagMixed (exactFlag g.1) q r) := by rw [Finset.mul_sum]
    _≤(nodes.card-V)*flagMixed pCount q r := Nat.mul_le_mul_left _
      (activeFactors_mixed_sum_le (rtySource F) (rtySource H) hSourceNe
        pCount q r hSourceCount)

def regularFamily (Gamma : Finset (Polynomial K)) (F : MvPolynomial (Fin 4) K) :
    Finset (Polynomial K) := Gamma.filter fun P => jetSpecialization2 P F=0 ∧
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0

theorem rtySource_in_flag_of_caps (F : MvPolynomial (Fin 4) K) (p : FlagDegree)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤p.all)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤p.yz+p.all)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤p.zOnly+p.yz+p.all) :
    PolynomialInFlag p (rtySource F) := by
  apply (support_subset_flagSupport_iff _ _).mp
  have h := rtySurfaceMap_nested_weights_le (polynomialEmbedding K) F
  apply support_subset_flagSupport_of_weighted_degrees
  · exact h.1.trans hT
  · exact h.2.1.trans hRT
  · exact h.2.2.trans hJet

theorem helper_box_flag (H : MvPolynomial (Fin 4) K)
    (hbox : H∈globalOrder2CoefficientBox K 2032893684 133221 15259 5008 2504) :
    PolynomialInFlag helperFlag (rtySource H) := by
  apply rtySource_in_flag_of_caps
  · apply (weightedTotalDegree_le_iff (![0,0,0,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [helperFlag] using (hbox he).2.2.1
  · apply (weightedTotalDegree_le_iff (![0,0,1,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [helperFlag] using (hbox he).2.1
  · apply (weightedTotalDegree_le_iff (![0,1,1,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [helperFlag] using (hbox he).1

def primaryReducedCut (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  rtySurfaceMap (polynomialEmbedding K)
    (reducedAgreementNumerator2 F 118 133221 (fun j => (j.factorial : K)⁻¹) x u)

theorem primaryReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F 133221 x u-primaryReducedCut F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F 118 133221
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,primaryReducedCut,map_sub,rtySurfaceMapHom_apply] using h

theorem regularHelper_factor_scaled_le [CharP K 2130706433]
    {I : Type} (nodes : Finset I) (x u : I→K) (hnodes : nodes.card=262144)
    (F H : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf (3 : Fin 4))
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤118)
    (hTdegree : F.degreeOf (3 : Fin 4)≤118)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤236)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤721)
    (hHelper : RegularHelper x u F H)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagrees : ∀ P∈Gamma,180413≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u 68740 2458014) :
    (regularFamily Gamma F).card*(180413-68740)≤
      (262144-68740)*flagMixed (exactFlag (rtySource F)) helperFlag primaryAgreement := by
  obtain ⟨hF,hH,hHbox,hproper,hvanish⟩ := hHelper
  have hsub : regularFamily Gamma F⊆Gamma := Finset.filter_subset _ _
  have hSource : PolynomialInFlag primaryFlag (rtySource F) :=
    rtySource_in_flag_of_caps F primaryFlag hT hRT hJet
  have hCut : ∀ i∈nodes,PolynomialInFlag primaryAgreement
      (primaryReducedCut F (x i) (u i)) := by
    intro i hi
    apply (support_subset_flagSupport_iff _ _).mp
    exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F
      133221 721 236 118 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hTdegree hRT hJet (fun j => (j.factorial : K)⁻¹) (x i) (u i)
  have hHsolution : ∀ P∈regularFamily Gamma F,jetSpecialization2 P H=0 := by
    intro P hP
    obtain ⟨hPG,hPF,hPreg⟩ := Finset.mem_filter.mp hP
    exact hvanish P (nodes.filter fun i => P.eval (x i)=u i)
      (hdegree P hPG) (hagrees P hPG)
      (fun i hi => (Finset.mem_filter.mp hi).2) hPF hPreg
  have hh := fixed_second_hereditary_scaled F H hF.irreducible (by omega) hproper
    (regularFamily Gamma F) nodes x u 2130706433 133221 180413 68740 2458014
    (by norm_num) (by norm_num) (by rw [hnodes]; norm_num)
    (fun P hP => hdegree P (hsub hP))
    (fun P hP => (Finset.mem_filter.mp hP).2.1)
    (fun P hP => (Finset.mem_filter.mp hP).2.2) hHsolution
    (fun P hP => hagrees P (hsub hP))
    (hereditaryCommonCap_mono hcommon hsub)
    (fun i => primaryReducedCut F (x i) (u i))
    (fun i hi => primaryReducedCut_congruent F (x i) (u i))
    (exactFlag (rtySource F)) primaryFlag helperFlag primaryAgreement
    (polynomialIn_exactFlag _) hSource (helper_box_flag H hHbox) hCut
    (by rw [hnodes]; exact small_absorption_gates.2.2)
    (by norm_num [primaryFlag])
    (by norm_num [primaryFlag,helperFlag])
    (by norm_num [primaryFlag,helperFlag])
  simpa only [hnodes] using hh

#print axioms fixed_second_hereditary_scaled
#print axioms regularHelper_factor_scaled_le
end
end ProximityPrize.SubmissionLower.WeightedProperHelperCountW1332216900
