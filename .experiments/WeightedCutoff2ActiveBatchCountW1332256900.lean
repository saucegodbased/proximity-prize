import WeightedCutoff2ProperHelperCountW1332256900
import WeightedFactorFlagBudgetW1332246900
import WeightedHeavyBatchPartitionW1332246900
import WeightedCutoff2CheapRemainderCountW1332256900
import WeightedCutoff2ShortenedJohnsonW1332256900

/-! End-to-end active-factor count for the cutoff-two small-identity-core branch. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2ActiveBatchCountW1332256900

open scoped Classical BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter Order2HereditaryCommonNodeFlagCount6900
open WeightedCutoff2RepresentativeLedgerW1332256900
open WeightedCutoff2BatchHelperW1332256900
open WeightedCutoff2ProperHelperCountW1332256900
open WeightedFactorFlagBudgetW1332246900
open WeightedHeavyBatchPartitionW1332246900
open WeightedCutoff2ShortenedJohnsonW1332256900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] [CharP K 2130706433]
local instance {A : Type*} : DecidableEq A := Classical.decEq A

theorem exited_certificates_scaled_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hTdegree : Q.degreeOf (3 : Fin 4)≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤739)
    (exited : Finset (MvPolynomial (Fin 4) K))
    (hE : exited⊆positiveTFactors Q)
    {I : Type} (nodes : Finset I) (x u : I→K)
    (hnodes : nodes.card≤n) (hAn : a≤nodes.card)
    (hcert : ∀ F∈exited,BatchHelperCertificate Q x u F)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,a≤
      (nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (∑ F∈exited,(regularFamily Gamma F).card)*(a-v)≤
      oneIncidenceNumerator primaryFlag helperFlag primaryAgreement := by
  have hper (F : ↑exited) :
      (regularFamily Gamma F.1).card*(a-v)≤
        (n-v)*flagMixed (exactFlag (rtySource F.1)) helperFlag primaryAgreement := by
    obtain ⟨hFirred,hFdiv,hFpositive⟩ := positiveTFactors_spec Q F.1 (hE F.2)
    obtain ⟨H,hH⟩ := batchHelperCertificate_regular Q x u F.1 (hcert F.1 F.2)
    exact regularHelper_factor_scaled_le nodes x u hnodes hAn F.1 H hFpositive
      ((weightedTotalDegree_le_of_dvd ![0,0,0,1] F.1 Q hFdiv hQ).trans hT)
      ((degreeOf_le_of_dvd (3 : Fin 4) F.1 Q hFdiv hQ).trans hTdegree)
      ((weightedTotalDegree_le_of_dvd ![0,0,1,1] F.1 Q hFdiv hQ).trans hRT)
      ((weightedTotalDegree_le_of_dvd ![0,1,1,1] F.1 Q hFdiv hQ).trans hJet)
      hH Gamma hdegree hagrees hcommon
  have hbudget := exactFlag_cumulative_of_weight_bounds exited Q hQ
    (positiveT_subset_product_dvd exited Q hQ hE) primaryFlag hT hRT hJet
  have hsum := aggregate_scaled_flags
    (fun F : ↑exited => (regularFamily Gamma F.1).card)
    (fun F : ↑exited => exactFlag (rtySource F.1))
    primaryFlag helperFlag primaryAgreement (a-v) (n-v)
    hper hbudget.1 hbudget.2.1 hbudget.2.2
  have heq : (∑ F : ↑exited,(regularFamily Gamma F.1).card)=
      ∑ F∈exited,(regularFamily Gamma F).card :=
    Finset.sum_coe_sort exited
      (fun F : MvPolynomial (Fin 4) K => (regularFamily Gamma F).card)
  rw [heq] at hsum
  unfold oneIncidenceNumerator
  exact hsum

theorem exited_certificates_card_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hTdegree : Q.degreeOf (3 : Fin 4)≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤739)
    (exited : Finset (MvPolynomial (Fin 4) K)) (hE : exited⊆positiveTFactors Q)
    {I : Type} (nodes : Finset I) (x u : I→K)
    (hnodes : nodes.card≤n) (hAn : a≤nodes.card)
    (hcert : ∀ F∈exited,BatchHelperCertificate Q x u F)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (∑ F∈exited,(regularFamily Gamma F).card)≤exitedHelperCap :=
  count_le_of_scaled _ _ _ _ (by norm_num [a,v])
    (exited_certificates_scaled_le Q hQ hT hTdegree hRT hJet exited hE
      nodes x u hnodes hAn hcert Gamma hdegree hagrees hcommon)
    active_scaled_caps.2

theorem activeTRegular_card_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hTdegree : Q.degreeOf (3 : Fin 4)≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤739)
    (Gamma : Finset (Polynomial K)) {I : Type} [Fintype I]
    (x u : I→K) (hinj : Function.Injective x)
    (hn : Fintype.card I≤n) (hAn : a≤Fintype.card I)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,a≤
      ((Finset.univ : Finset I).filter fun i => P.eval (x i)=u i).card) :
    (activeTRegularPolynomials Q Gamma).card≤cheapRegularCap+exitedHelperCap := by
  classical
  have hnodes : (Finset.univ : Finset I).card≤n := by simpa using hn
  have hAnodes : a≤(Finset.univ : Finset I).card := by simpa using hAn
  have hcommon : HereditaryCommonCap Gamma Finset.univ x u v small :=
    scalar_hereditary_common_nodes_card_le_68759
      Gamma Finset.univ x u hinj.injOn hnodes hAnodes hdegree hagrees
  have h2 : (2 : K)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num)
  have hprime : Nat.Prime 2130706433 :=
    CharP.char_prime_of_ne_zero K (by norm_num)
  have hstep (s : Finset (MvPolynomial (Fin 4) K))
      (hs : s⊆positiveTFactors Q) (hne : s.Nonempty) (hh : HeavyProduct id s) :
      ∃ F∈s,BatchHelperCertificate Q x u F := by
    exact heavy_subset_certificate Q s hne hs x u hinj hn h2
      2130706433 hprime (by norm_num) hh
  obtain ⟨exited,rest,hrest,hEx,hdisjoint,hunion,hcheap,hcert⟩ :=
    heavy_products_partition id (positiveTFactors Q)
      (BatchHelperCertificate Q x u) hstep
  have hE : exited⊆positiveTFactors Q := by
    rw [hEx]
    exact Finset.sdiff_subset
  have hExit := exited_certificates_card_le Q hQ hT hTdegree hRT hJet
    exited hE Finset.univ x u hnodes hAnodes hcert Gamma hdegree hagrees hcommon
  have hRest : (∑ F∈rest,
      (WeightedCutoff2CheapRemainderCountW1332256900.regularFamily F Gamma).card)≤
        cheapRegularCap :=
    WeightedCutoff2CheapRemainderCountW1332256900.cheap_remainder_card_le
      Q rest hrest hcheap.1 hcheap.2 Gamma Finset.univ x u hinj.injOn
      hnodes hAnodes hdegree hagrees hcommon
  have hcover : activeTRegularPolynomials Q Gamma⊆
      (positiveTFactors Q).biUnion (regularFamily Gamma) := by
    intro P hP
    obtain ⟨hPG,F,hF,hzero,hreg⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_biUnion.mpr
      ⟨F,hF,Finset.mem_filter.mpr ⟨hPG,hzero,hreg⟩⟩
  have hcard : (activeTRegularPolynomials Q Gamma).card≤
      ∑ F∈positiveTFactors Q,(regularFamily Gamma F).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsplit := sum_exited_add_rest (positiveTFactors Q) rest hrest
    (fun F => (regularFamily Gamma F).card)
  rw [← hEx] at hsplit
  calc
    (activeTRegularPolynomials Q Gamma).card ≤
        ∑ F∈positiveTFactors Q,(regularFamily Gamma F).card := hcard
    _ = (∑ F∈exited,(regularFamily Gamma F).card)+
        (∑ F∈rest,(regularFamily Gamma F).card) := hsplit.symm
    _ ≤ exitedHelperCap+cheapRegularCap := Nat.add_le_add hExit hRest
    _ = cheapRegularCap+exitedHelperCap := Nat.add_comm _ _

end
end ProximityPrize.SubmissionLower.WeightedCutoff2ActiveBatchCountW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ActiveBatchCountW1332256900.activeTRegular_card_le
