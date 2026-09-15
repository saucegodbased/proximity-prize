import WeightedIdentityOneExceptionLedgerW1332256900
import WeightedFactorFlagBudgetW1332246900
import WeightedBatchFactorChoice6900

/-!
# The W=133225 L-shaped terminal corner

The terminal union

* `jetDegree <= 211` and `derivativeDegree <= 55`, or
* `jetDegree <= 212` and `derivativeDegree <= 54`

keeps the old `J211/D55` two-incidence cap.  If a remaining product is at the
single excluded corner `(J,D)=(212,55)` and has at least two positive-T
factors, every individual factor still has jet degree at most `211`.
Consequently the old reduced agreement flag may be used factorwise, while
only the cumulative source flag grows by one `zOnly` unit.

This file proves that semantic adapter and its exact arithmetic.  It does not
dispose of a singleton irreducible factor of degrees `(212,55)`.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityLShapeCornerW1332256900

open scoped BigOperators
open RCN001 RCN066 RCN071 RCN081 RCN084 RCN095 RCN135 RCN136 RCN319
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2ReducedCutScaffold Order2FlagTwoCutAdapter
open Order2FlagComponentAssignedAdapter
open Order2HereditaryCommonNodeFlagCount6900 Order2HereditaryActiveSurface6900
open WeightedSourceBoxQuotient6900 WeightedActualProductBandGate6900
open WeightedBatchFactorChoice6900
open WeightedFactorFlagBudgetW1332246900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

def n : Nat := 262143
def w : Nat := 133225
def a : Nat := 180413
def v : Nat := 68763
def small : Nat := 1453806
def prime : Nat := 2130706433
def coreFloor : Nat := 263611557201785349

def armAFlag : FlagDegree := ⟨156,28,27⟩
def armBFlag : FlagDegree := ⟨158,27,27⟩
def cornerFlag : FlagDegree := ⟨157,28,27⟩
def armAAgreement : FlagDegree := honestReducedAgreementFlag w 211 55 27
def armBAgreement : FlagDegree := honestReducedAgreementFlag w 212 54 27
def fullCornerAgreement : FlagDegree := honestReducedAgreementFlag w 212 55 27

def ceilQuotient (num den : Nat) : Nat := (num+den-1)/den
def twoIncidenceNumerator (p q : FlagDegree) : Nat :=
  (n-v)^2*flagMixed p q q
def capFor (p q : FlagDegree) : Nat :=
  ceilQuotient (twoIncidenceNumerator p q) ((a-v)^2)

def armACap : Nat := capFor armAFlag armAAgreement
def armBCap : Nat := capFor armBFlag armBAgreement
def cornerOldAgreementCap : Nat := capFor cornerFlag armAAgreement
def fullCornerCap : Nat := capFor cornerFlag fullCornerAgreement

theorem lshape_flags_exact :
    armAAgreement=⟨41432976,7593825,6927700⟩ ∧
    armBAgreement=⟨41965876,7327375,6927700⟩ ∧
    fullCornerAgreement=⟨41699426,7593825,6927700⟩ := by
  norm_num [armAAgreement,armBAgreement,fullCornerAgreement,
    honestReducedAgreementFlag,w]

theorem lshape_mixed_costs_exact :
    flagMixed armAFlag armAAgreement armAAgreement=82448135047096675 ∧
    flagMixed armBFlag armBAgreement armBAgreement=81150690383165475 ∧
    flagMixed cornerFlag armAAgreement armAAgreement=82601343557291675 ∧
    flagMixed cornerFlag fullCornerAgreement fullCornerAgreement=
      82913653212689175 := by
  norm_num [armAFlag,armBFlag,cornerFlag,armAAgreement,armBAgreement,
    fullCornerAgreement,honestReducedAgreementFlag,w,flagMixed]

theorem lshape_caps_exact :
    armACap=247335521894435962 ∧
    armBCap=243443327693811957 ∧
    cornerOldAgreementCap=247795130917806876 ∧
    fullCornerCap=248732026234678355 := by
  norm_num [armACap,armBCap,cornerOldAgreementCap,fullCornerCap,capFor,
    twoIncidenceNumerator,ceilQuotient,n,v,a,lshape_mixed_costs_exact]

theorem corner_increment_and_preexit_headroom_exact :
    cornerOldAgreementCap-armACap=459609023370914 ∧
    coreFloor-(cornerOldAgreementCap+
      WeightedIdentityOneExceptionLedgerW1332256900.minimumPrimaryCleanupCap)=
        293703028276199 ∧
    fullCornerCap+
      WeightedIdentityOneExceptionLedgerW1332256900.minimumPrimaryCleanupCap-
        coreFloor=643192288595280 := by
  rw [lshape_caps_exact.1,lshape_caps_exact.2.2.1,
    lshape_caps_exact.2.2.2]
  norm_num [coreFloor,
    WeightedIdentityOneExceptionLedgerW1332256900.minimumPrimaryCleanupCap,
    WeightedIdentityOneExceptionLedgerW1332256900.primaryCleanupFor,
    WeightedIdentityOneExceptionLedgerW1332256900.firstOrderRegularCap,
    WeightedIdentityOneExceptionLedgerW1332256900.firstOrderSingularCap,
    WeightedIdentityOneExceptionLedgerW1332256900.firstOrderMixedCost,
    WeightedIdentityOneExceptionLedgerW1332256900.ceilQuotient,
    WeightedIdentityOneExceptionLedgerW1332256900.n,
    WeightedIdentityOneExceptionLedgerW1332256900.v,
    WeightedIdentityOneExceptionLedgerW1332256900.w,
    WeightedIdentityOneExceptionLedgerW1332256900.a]

def regularFamily (F : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) : Finset (Polynomial K) :=
  Gamma.filter fun P => jetSpecialization2 P F=0 ∧
    jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0

def oldReducedCut (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  rtySurfaceMap (polynomialEmbedding K)
    (reducedAgreementNumerator2 F 27 w
      (fun j => (j.factorial : K)⁻¹) x u)

theorem oldReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F w x u-oldReducedCut F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F 27 w
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,oldReducedCut,map_sub,
    rtySurfaceMapHom_apply] using h

theorem oldReducedCut_in_flag (F : MvPolynomial (Fin 4) K)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤55)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤211)
    (x u : K) : PolynomialInFlag armAAgreement (oldReducedCut F x u) := by
  have hTdegree : F.degreeOf 3≤27 := by
    rw [← T_weight_eq_degreeOf]
    exact hT
  apply (support_subset_flagSupport_iff _ _).mp
  exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F w 211 55 27
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hTdegree hRT hJ (fun j => (j.factorial : K)⁻¹) x u

theorem individual_old_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤55)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤211)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    Gamma.card*(a-v)^2≤(n-v)^2*
      flagMixed (exactFlag (rtySource F)) armAAgreement armAAgreement := by
  have hsource : PolynomialInFlag armAFlag (rtySource F) :=
    rtySource_in_flag_of_weights F armAFlag hT hRT hJ
  have hsmallCurve : small*(a-v)≤(nodes.card-v)*armAAgreement.all := by
    rw [hn]
    norm_num [small,a,v,n,armAAgreement,honestReducedAgreementFlag,w]
  have hsmallSurface : small*(a-v)^2≤
      (nodes.card-v)^2*armAAgreement.all^2 := by
    rw [hn]
    norm_num [small,a,v,n,armAAgreement,honestReducedAgreementFlag,w]
  have hgate : (armAAgreement.yz+armAAgreement.all)*armAFlag.all+
      (armAFlag.yz+armAFlag.all)*armAAgreement.all<prime := by
    norm_num [armAAgreement,armAFlag,honestReducedAgreementFlag,w,prime]
  have h := original_regular_of_congruent_active_flags F hF Gamma nodes x u hinj
    prime w a v small (by norm_num [w]) (by norm_num [w,prime])
    (by norm_num [prime]) (by norm_num [w,a]) (by norm_num [v,a])
    (by rw [hn]; norm_num [n,a]) hdegree hsolution hregular hagreement hcommon
    (fun i => oldReducedCut F (x i) (u i))
    (fun i _ => oldReducedCut_congruent F (x i) (u i))
    (exactFlag (rtySource F)) armAFlag armAAgreement
    (polynomialIn_exactFlag _) hsource
    (fun i _ => oldReducedCut_in_flag F hT hRT hJ (x i) (u i))
    hsmallCurve hsmallSurface (by norm_num [armAFlag,prime]) hgate
  rw [hn] at h
  exact h

theorem positiveT_factor_jet_pos (Q F : MvPolynomial (Fin 4) K)
    (hF : F∈positiveTFactors Q) : 0<jetDegree F := by
  classical
  have hT : 0<F.degreeOf 3 := (positiveTFactors_spec Q F hF).2.2
  have hF0 : F≠0 := (positiveTFactors_spec Q F hF).1.ne_zero
  obtain ⟨e,he,heq⟩ := Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF0) (fun e => e (3 : Fin 4))
  have hepos : 0<e 3 := by
    rw [MvPolynomial.degreeOf_eq_sup,heq] at hT
    exact hT
  have hj := MvPolynomial.le_weightedTotalDegree jetWeights he
  rw [jetWeight_eq] at hj
  have he3 : e 3≤e 1+e 2+e 3 := by omega
  exact hepos.trans_le (he3.trans hj)

theorem factor_jet_le_211_of_two (Q : MvPolynomial (Fin 4) K)
    (s : Finset (MvPolynomial (Fin 4) K)) (hs : s⊆positiveTFactors Q)
    (hcard : 2≤s.card)
    (hJ : jetDegree (∏ F∈s,F)≤212) :
    ∀ F∈s,jetDegree F≤211 := by
  classical
  intro F hFs
  obtain ⟨A,hAs,B,hBs,hAB⟩ := Finset.one_lt_card.mp (by omega : 1<s.card)
  have hother : ∃ G∈s,G≠F := by
    by_cases hAF : A=F
    · refine ⟨B,hBs,?_⟩
      intro hBF
      exact hAB (hAF.trans hBF.symm)
    · exact ⟨A,hAs,hAF⟩
  obtain ⟨G,hGs,hGF⟩ := hother
  have hirr : ∀ H∈s,Irreducible H := fun H hHs =>
    (positiveTFactors_spec Q H (hs hHs)).1
  have hprod : (∏ H∈s,H)≠0 := product_ne_zero s id hirr
  have hsum := RCN071.weightedTotalDegree_prod_eq jetWeights s id
    (fun H hHs => (hirr H hHs).ne_zero)
  have hGpos : 1≤jetDegree G := positiveT_factor_jet_pos Q G (hs hGs)
  have hGerase : G∈s.erase F := Finset.mem_erase.mpr ⟨hGF,hGs⟩
  have hGsum : jetDegree G≤∑ H∈s.erase F,jetDegree H := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hGerase
  have hsplit := Finset.sum_erase_add s (fun H => jetDegree H) hFs
  change jetDegree (∏ H∈s,H)=∑ H∈s,jetDegree H at hsum
  have htotal : jetDegree F+jetDegree G≤jetDegree (∏ H∈s,H) := by
    rw [hsum]
    calc
      jetDegree F+jetDegree G≤
          jetDegree F+∑ H∈s.erase F,jetDegree H :=
        Nat.add_le_add_left hGsum _
      _ = (∑ H∈s.erase F,jetDegree H)+jetDegree F := Nat.add_comm _ _
      _ = ∑ H∈s,jetDegree H := hsplit
  omega

/-- The old agreement cut remains valid factorwise at the excluded corner,
provided the product has at least two positive-T factors.  Only the aggregate
source flag pays the extra jet unit. -/
theorem nonsingleton_corner_remainder_scaled [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K)
    (s : Finset (MvPolynomial (Fin 4) K)) (hs : s⊆positiveTFactors Q)
    (hcard : 2≤s.card)
    (hJ : jetDegree (∏ F∈s,F)≤212)
    (hrho : derivativeDegree (∏ F∈s,F)≤55)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (∑ F∈s,(regularFamily F Gamma).card)*(a-v)^2≤
      twoIncidenceNumerator cornerFlag armAAgreement := by
  let product : MvPolynomial (Fin 4) K := ∏ F∈s,F
  have hirr : ∀ F∈s,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hs hF)).1
  have hproduct : product≠0 := product_ne_zero s id hirr
  have hweights := derivative_nested_bounds product
  have hdiv : derivativeDegree product/2≤55/2 := Nat.div_le_div_right hrho
  have hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] product≤27 :=
    hweights.1.trans (by norm_num at hdiv ⊢; exact hdiv)
  have hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] product≤55 :=
    hweights.2.trans hrho
  have hfactorJ := factor_jet_le_211_of_two Q s hs hcard hJ
  have hfactor (F : ↥s) :
      (regularFamily F.1 Gamma).card*(a-v)^2≤(n-v)^2*
        flagMixed (exactFlag (rtySource F.1)) armAAgreement armAAgreement := by
    have hdvd : F.1∣product := Finset.dvd_prod_of_mem id F.2
    have hFT := (weightedTotalDegree_le_of_dvd ![0,0,0,1]
      F.1 product hdvd hproduct).trans hT
    have hFRT := (weightedTotalDegree_le_of_dvd ![0,0,1,1]
      F.1 product hdvd hproduct).trans hRT
    have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
    exact individual_old_scaled F.1 (hirr F.1 F.2).ne_zero hFT hFRT
      (hfactorJ F.1 F.2) (regularFamily F.1 Gamma) nodes x u hinj hn
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2.1)
      (fun P hP => (Finset.mem_filter.mp hP).2.2)
      (fun P hP => hagreement P (hsub hP))
      (hereditaryCommonCap_mono hcommon hsub)
  have hsum := exactFlag_cumulative_of_weight_bounds s product hproduct dvd_rfl
    cornerFlag hT hRT hJ
  have h :=
    WeightedRepresentativeCountLedgerW1332246900.aggregate_scaled_flags
      (fun F : ↥s => (regularFamily F.1 Gamma).card)
      (fun F : ↥s => exactFlag (rtySource F.1))
      cornerFlag armAAgreement armAAgreement ((a-v)^2) ((n-v)^2)
      hfactor hsum.1 hsum.2.1 hsum.2.2
  have heq : (∑ F : ↥s,(regularFamily F.1 Gamma).card)=
      ∑ F∈s,(regularFamily F Gamma).card :=
    Finset.sum_coe_sort s
      (fun F : MvPolynomial (Fin 4) K => (regularFamily F Gamma).card)
  rw [heq] at h
  exact h

theorem nonsingleton_corner_remainder_card_le [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K)
    (s : Finset (MvPolynomial (Fin 4) K)) (hs : s⊆positiveTFactors Q)
    (hcard : 2≤s.card)
    (hJ : jetDegree (∏ F∈s,F)≤212)
    (hrho : derivativeDegree (∏ F∈s,F)≤55)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodes x u v small) :
    (∑ F∈s,(regularFamily F Gamma).card)≤cornerOldAgreementCap := by
  apply WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
    _ _ _ _ (by norm_num [a,v])
    (nonsingleton_corner_remainder_scaled Q s hs hcard hJ hrho Gamma nodes
      x u hinj hn hdegree hagreement hcommon)
  norm_num [cornerOldAgreementCap,capFor,ceilQuotient,twoIncidenceNumerator,
    n,v,a,lshape_mixed_costs_exact]

end
end ProximityPrize.SubmissionLower.WeightedIdentityLShapeCornerW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedIdentityLShapeCornerW1332256900.factor_jet_le_211_of_two
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityLShapeCornerW1332256900.nonsingleton_corner_remainder_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityLShapeCornerW1332256900.nonsingleton_corner_remainder_card_le
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityLShapeCornerW1332256900.corner_increment_and_preexit_headroom_exact
