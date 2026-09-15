import WeightedProperHelperCountW1332246900
import WeightedCutoff2BatchHelperW1332256900
import WeightedCutoff2RepresentativeLedgerW1332256900

/-! Proper-helper incidence count for the cutoff-two profile and arbitrary `card≤262142`. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2ProperHelperCountW1332256900

open scoped Classical BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135 RCN136 RCN319
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter Order2FlagComponentAssignedAdapter
open Order2HereditaryCommonNodeFlagCount6900
open Order2SourceBasisScaffold Order2ReducedCutScaffold
open WeightedCutoff2BatchHelperW1332256900
open WeightedCutoff2RepresentativeLedgerW1332256900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
variable {K : Type} [Field K]
local instance {A : Type*} : DecidableEq A := Classical.decEq A

def regularFamily (Gamma : Finset (Polynomial K)) (F : MvPolynomial (Fin 4) K) :
    Finset (Polynomial K) := Gamma.filter fun P => jetSpecialization2 P F=0 ∧
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0

theorem helper_box_flag (H : MvPolynomial (Fin 4) K)
    (hbox : H∈globalOrder2CoefficientBox K 2130677530 133225 15993 5248 2624) :
    PolynomialInFlag helperFlag (rtySource H) := by
  apply WeightedProperHelperCountW1332246900.rtySource_in_flag_of_caps
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
    (reducedAgreementNumerator2 F 122 133225 (fun j => (j.factorial : K)⁻¹) x u)

theorem primaryReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F 133225 x u-primaryReducedCut F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F 122 133225
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,primaryReducedCut,map_sub,rtySurfaceMapHom_apply] using h

theorem regularHelper_factor_scaled_le [CharP K 2130706433]
    {I : Type} (nodes : Finset I) (x u : I→K) (hnodes : nodes.card≤n)
    (hAn : a≤nodes.card)
    (F H : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf (3 : Fin 4))
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤122)
    (hTdegree : F.degreeOf (3 : Fin 4)≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤244)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤739)
    (hHelper : RegularHelper x u F H)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (regularFamily Gamma F).card*(a-v)≤
      (n-v)*flagMixed (exactFlag (rtySource F)) helperFlag primaryAgreement := by
  obtain ⟨hF,hH,hHbox,hproper,hvanish⟩ := hHelper
  have hsub : regularFamily Gamma F⊆Gamma := Finset.filter_subset _ _
  have hSource : PolynomialInFlag primaryFlag (rtySource F) :=
    WeightedProperHelperCountW1332246900.rtySource_in_flag_of_caps F primaryFlag hT hRT hJet
  have hCut : ∀ i∈nodes,PolynomialInFlag primaryAgreement
      (primaryReducedCut F (x i) (u i)) := by
    intro i hi
    apply (support_subset_flagSupport_iff _ _).mp
    exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F
      133225 739 244 122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hTdegree hRT hJet (fun j => (j.factorial : K)⁻¹) (x i) (u i)
  have hHsolution : ∀ P∈regularFamily Gamma F,jetSpecialization2 P H=0 := by
    intro P hP
    obtain ⟨hPG,hPF,hPreg⟩ := Finset.mem_filter.mp hP
    exact hvanish P (nodes.filter fun i => P.eval (x i)=u i)
      (hdegree P hPG) (hagrees P hPG)
      (fun i hi => (Finset.mem_filter.mp hi).2) hPF hPreg
  have hav : a-v≤nodes.card-v := Nat.sub_le_sub_right hAn v
  have hsmall : small*(a-v)≤(nodes.card-v)*primaryAgreement.all := by
    calc
      small*(a-v) ≤ primaryAgreement.all*(a-v) :=
        Nat.mul_le_mul_right _ (by norm_num [small,primaryAgreement,honestReducedAgreementFlag,w])
      _ = (a-v)*primaryAgreement.all := Nat.mul_comm _ _
      _ ≤ (nodes.card-v)*primaryAgreement.all := Nat.mul_le_mul_right _ hav
  have hh := WeightedProperHelperCountW1332246900.fixed_second_hereditary_scaled
    F H hF.irreducible (by omega) hproper
    (regularFamily Gamma F) nodes x u 2130706433 w a v small
    (by norm_num [w]) (by norm_num [v,a]) hAn
    (fun P hP => hdegree P (hsub hP))
    (fun P hP => (Finset.mem_filter.mp hP).2.1)
    (fun P hP => (Finset.mem_filter.mp hP).2.2) hHsolution
    (fun P hP => hagrees P (hsub hP))
    (hereditaryCommonCap_mono hcommon hsub)
    (fun i => primaryReducedCut F (x i) (u i))
    (fun i hi => primaryReducedCut_congruent F (x i) (u i))
    (exactFlag (rtySource F)) primaryFlag helperFlag primaryAgreement
    (polynomialIn_exactFlag _) hSource (helper_box_flag H hHbox) hCut hsmall
    (by norm_num [primaryFlag])
    (by norm_num [primaryFlag,helperFlag])
    (by norm_num [primaryFlag,helperFlag])
  exact hh.trans (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hnodes v))

end
end ProximityPrize.SubmissionLower.WeightedCutoff2ProperHelperCountW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ProperHelperCountW1332256900.regularHelper_factor_scaled_le
