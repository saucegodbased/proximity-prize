import WeightedProperHelperCountW1332216900
import WeightedFactorFlagBudgetW1332216900
import WeightedHeavyBatchPartitionW1332216900
import WeightedCheapRemainderCountW1332216900
import WeightedShortenedJohnsonW1332216900

/-! Actual active-T count at W=133221. Heavy subset certificates are
constructed by the proved helper source/kernel/escape producer. Cheap and
exited branches count original factor families against one degree ledger. -/
namespace ProximityPrize.SubmissionLower.WeightedActiveBatchCountW1332216900

open scoped Classical BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter Order2HereditaryCommonNodeFlagCount6900
open WeightedRepresentativeCountLedgerW1332216900
open WeightedBatchHelperCertificateW1332216900
open WeightedProperHelperCountW1332216900
open WeightedFactorFlagBudgetW1332216900
open WeightedHeavyBatchPartitionW1332216900
open WeightedShortenedJohnsonW1332216900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] [CharP K 2130706433]
local instance {A : Type*} : DecidableEq A := Classical.decEq A

/-- Sum helper incidence inequalities before taking a ceiling, so the exited
factors share the enclosing primary flag. -/
theorem exited_certificates_scaled_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤118)
    (hTdegree : Q.degreeOf (3 : Fin 4)≤118)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤236)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤721)
    (exited : Finset (MvPolynomial (Fin 4) K))
    (hE : exited⊆positiveTFactors Q)
    {I : Type} (nodes : Finset I) (x u : I→K)
    (hnodes : nodes.card=262144)
    (hcert : ∀ F∈exited,BatchHelperCertificate Q x u F)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagrees : ∀ P∈Gamma,180413≤
      (nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u 68740 2458014) :
    (∑ F∈exited,(regularFamily Gamma F).card)*(a-v)≤
      oneIncidenceNumerator primaryFlag helperFlag primaryAgreement := by
  have hper (F : ↥exited) :
      (regularFamily Gamma F.1).card*(a-v)≤
        (n-v)*flagMixed (exactFlag (rtySource F.1)) helperFlag primaryAgreement := by
    obtain ⟨hFirred,hFdiv,hFpositive⟩ := positiveTFactors_spec Q F.1 (hE F.2)
    obtain ⟨H,hH⟩ := batchHelperCertificate_regular Q x u F.1 (hcert F.1 F.2)
    exact regularHelper_factor_scaled_le nodes x u hnodes F.1 H hFpositive
      ((weightedTotalDegree_le_of_dvd ![0,0,0,1] F.1 Q hFdiv hQ).trans hT)
      ((degreeOf_le_of_dvd (3 : Fin 4) F.1 Q hFdiv hQ).trans hTdegree)
      ((weightedTotalDegree_le_of_dvd ![0,0,1,1] F.1 Q hFdiv hQ).trans hRT)
      ((weightedTotalDegree_le_of_dvd ![0,1,1,1] F.1 Q hFdiv hQ).trans hJet)
      hH Gamma hdegree hagrees hcommon
  have hbudget := exactFlag_cumulative_of_weight_bounds exited Q hQ
    (positiveT_subset_product_dvd exited Q hQ hE) primaryFlag hT hRT hJet
  have hsum := aggregate_scaled_flags
    (fun F : ↥exited => (regularFamily Gamma F.1).card)
    (fun F : ↥exited => exactFlag (rtySource F.1))
    primaryFlag helperFlag primaryAgreement (a-v) (n-v)
    hper hbudget.1 hbudget.2.1 hbudget.2.2
  have heq : (∑ F : ↥exited,(regularFamily Gamma F.1).card)=
      ∑ F∈exited,(regularFamily Gamma F).card :=
    Finset.sum_coe_sort exited
      (fun F : MvPolynomial (Fin 4) K => (regularFamily Gamma F).card)
  rw [heq] at hsum
  unfold oneIncidenceNumerator
  exact hsum

theorem exited_certificates_card_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤118)
    (hTdegree : Q.degreeOf (3 : Fin 4)≤118)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤236)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤721)
    (exited : Finset (MvPolynomial (Fin 4) K))
    (hE : exited⊆positiveTFactors Q)
    {I : Type} (nodes : Finset I) (x u : I→K)
    (hnodes : nodes.card=262144)
    (hcert : ∀ F∈exited,BatchHelperCertificate Q x u F)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagrees : ∀ P∈Gamma,180413≤
      (nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u 68740 2458014) :
    (∑ F∈exited,(regularFamily Gamma F).card)≤exitedHelperCap :=
  count_le_of_scaled _ _ _ _ (by norm_num [a,v])
    (exited_certificates_scaled_le Q hQ hT hTdegree hRT hJet exited hE
      nodes x u hnodes hcert Gamma hdegree hagrees hcommon)
    active_scaled_caps.2

/-- Final active-T regular-family count with the W=133221 helper and the
`q=2458014`, `v=68740` shortened-Johnson specialization. -/
theorem activeTRegular_card_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤118)
    (hTdegree : Q.degreeOf (3 : Fin 4)≤118)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤236)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤721)
    (Gamma : Finset (Polynomial K)) {I : Type} [Fintype I]
    (x u : I→K) (hinj : Function.Injective x)
    (hn : Fintype.card I=262144)
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagrees : ∀ P∈Gamma,180413≤
      ((Finset.univ : Finset I).filter fun i => P.eval (x i)=u i).card) :
    (activeTRegularPolynomials Q Gamma).card≤cheapRegularCap+exitedHelperCap := by
  classical
  have hnodes : (Finset.univ : Finset I).card=262144 := by
    rw [Finset.card_univ,hn]
  have hcommon : HereditaryCommonCap Gamma Finset.univ x u 68740 2458014 :=
    scalar_hereditary_common_nodes_card_le_68757
      Gamma Finset.univ x u hinj.injOn hnodes hdegree hagrees
  have h2 : (2 : K)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num)
  have hprime : Nat.Prime 2130706433 :=
    CharP.char_prime_of_ne_zero K (by norm_num)
  have hstep (s : Finset (MvPolynomial (Fin 4) K))
      (hs : s⊆positiveTFactors Q) (hne : s.Nonempty) (hh : HeavyProduct id s) :
      ∃ F∈s,BatchHelperCertificate Q x u F := by
    exact heavy_subset_certificate Q s hne hs x u hinj (by omega) h2
      2130706433 hprime (by norm_num) hh
  obtain ⟨exited,rest,hrest,hEx,hdisjoint,hunion,hcheap,hcert⟩ :=
    heavy_products_partition id (positiveTFactors Q)
      (BatchHelperCertificate Q x u) hstep
  have hE : exited⊆positiveTFactors Q := by
    rw [hEx]
    exact Finset.sdiff_subset
  have hExit := exited_certificates_card_le Q hQ hT hTdegree hRT hJet
    exited hE Finset.univ x u hnodes hcert Gamma hdegree hagrees hcommon
  have hRest : (∑ F∈rest,
      (WeightedCheapRemainderCountW1332216900.regularFamily F Gamma).card)≤
        cheapRegularCap :=
    WeightedCheapRemainderCountW1332216900.cheap_remainder_card_le Q rest hrest
      hcheap.1 hcheap.2 Gamma Finset.univ x u hinj.injOn hnodes
      hdegree hagrees hcommon
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
end ProximityPrize.SubmissionLower.WeightedActiveBatchCountW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedActiveBatchCountW1332216900.exited_certificates_scaled_le
#print axioms ProximityPrize.SubmissionLower.WeightedActiveBatchCountW1332216900.exited_certificates_card_le
#print axioms ProximityPrize.SubmissionLower.WeightedActiveBatchCountW1332216900.activeTRegular_card_le
