import WeightedHardLShapeDeflatedCapacityW1332256900
import WeightedIdentityCoupledPartitionAdapterW1332256900
import WeightedIdentityLShapeCornerW1332256900
import WeightedProperHelperCountW1332246900

/-!
# Hard one-exception L-shape integration at W=133225

This module gives the single-profile helper its exact count-facing interface,
supplies the missing arm-B old-cut incidence theorem, and connects both to the
strict L-terminal coupled partition.  The final theorem leaves only the
three-way source/helper producer as a premise.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityHardLShapeIntegrationW1332256900

open scoped Classical BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135 RCN136 RCN319
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter Order2FlagComponentAssignedAdapter
open Order2FixedSecondSourceAdapter Order2HereditaryCommonNodeFlagCount6900
open Order2HereditaryActiveSurface6900
open Order2SourceBasisScaffold Order2SourceSpecializationScaffold
open Order2ReducedCutScaffold
open WeightedSourceBoxQuotient6900 WeightedActualProductBandGate6900
open WeightedSourceIndex6900
open WeightedBatchFactorChoice6900 WeightedFactorFlagBudgetW1332246900
open WeightedIdentityCoupledPartitionAdapterW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

namespace R
abbrev n := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n
abbrev a := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a
abbrev v := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v
abbrev armAFlag := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag
abbrev armAExitFlag := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag
abbrev armAAgreement := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement
abbrev armBFlag := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBFlag
abbrev armBExitFlag := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBExitFlag
abbrev armBAgreement := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBAgreement
abbrev primaryFlag := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryFlag
abbrev primaryAgreement := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement
abbrev jointHelperFlag := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag
abbrev jointCommonNumerator := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator
end R

def w : Nat := 133225
def small : Nat := 1453806
def prime : Nat := 2130706433

/-- Exact semantic payload required from the cutoff-two source producer. -/
def JointRegularHelper (nodeSet : Finset I) (nodes values : I→K)
    (F H : MvPolynomial (Fin 4) K) : Prop :=
  Prime F ∧ H≠0 ∧
  H∈globalOrder2CoefficientBox K
      WeightedHardLShapeDeflatedCapacityW1332256900.sourceCutoff w
      WeightedHardLShapeDeflatedCapacityW1332256900.jetCap
      WeightedHardLShapeDeflatedCapacityW1332256900.derivativeCap
      WeightedHardLShapeDeflatedCapacityW1332256900.totalCap ∧
  ¬F∣H ∧
  ∀ (P : Polynomial K), P.natDegree≤w →
    R.a≤(nodeSet.filter fun i => P.eval (nodes i)=values i).card →
    localJetSpecialization2 P F=0 →
    localJetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0 →
    localJetSpecialization2 P H=0

/-- Direct adapter from the deflated cutoff-two source data to the sole
certificate consumed by strict L-descent. -/
theorem jointRegularHelper_of_deflated_source
    [CharP K 2130706433]
    (nodeSet : Finset I) (x u : I→K) (hinj : Set.InjOn x nodeSet)
    (F C G : MvPolynomial (Fin 4) K) (j : Nat)
    (hF : Prime F) (hFC : ¬F∣C) (hFG : ¬F∣G)
    (hj : j≤WeightedHardLShapeDeflatedCapacityW1332256900.stageMax)
    (hC : C≠0) (hG : G≠0)
    (hcontact : ∀ i∈nodeSet,
      contactTruncation K
        WeightedHardLShapeDeflatedCapacityW1332256900.contactOrder
        (localSubstitution K (x i) (u i) ((F*C)^j*G))=0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (WeightedHardLShapeDeflatedCapacityW1332256900.sourceCutoff-
        j*WeightedHardLShapeDeflatedCapacityW1332256900.stageDelta)
      w WeightedHardLShapeDeflatedCapacityW1332256900.derivativeCap) :
    JointRegularHelper nodeSet x u F (C^j*G) := by
  have hQ : (F*C)^j*G≠0 :=
    mul_ne_zero (pow_ne_zero j (mul_ne_zero hF.ne_zero hC)) hG
  refine ⟨hF,
    WeightedHardLShapeDeflatedCapacityW1332256900.deflated_helper_ne_zero
      F C G j hQ,
    ?_,
    WeightedHardLShapeDeflatedCapacityW1332256900.deflated_helper_proper
      F C G j hF hFC hFG,?_⟩
  · exact WeightedHardLShapeDeflatedCapacityW1332256900.deflated_helper_mem_globalBox
      F C G j hF.ne_zero hQ htight
  · intro P hP ha hFzero hregular
    let support := nodeSet.filter fun i => P.eval (x i)=u i
    apply WeightedHardLShapeDeflatedCapacityW1332256900.deflated_helper_vanishes
      F C G P x u support j 2130706433
      (CharP.char_prime_of_ne_zero K (by norm_num))
      (by norm_num [prime,
        WeightedHardLShapeDeflatedCapacityW1332256900.stageMax]) hj
      (hinj.mono (Finset.filter_subset _ _))
      (CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num))
      hP ha hQ
    · intro i hi
      exact hcontact i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact htight
    · exact hFzero
    · exact hregular

theorem joint_helper_box_flag (H : MvPolynomial (Fin 4) K)
    (hbox : H∈globalOrder2CoefficientBox K
      WeightedHardLShapeDeflatedCapacityW1332256900.sourceCutoff w
      WeightedHardLShapeDeflatedCapacityW1332256900.jetCap
      WeightedHardLShapeDeflatedCapacityW1332256900.derivativeCap
      WeightedHardLShapeDeflatedCapacityW1332256900.totalCap) :
    PolynomialInFlag R.jointHelperFlag (rtySource H) := by
  apply WeightedFactorFlagBudgetW1332246900.rtySource_in_flag_of_weights
  · apply (weightedTotalDegree_le_iff (![0,0,0,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [R.jointHelperFlag,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
      WeightedHardLShapeDeflatedCapacityW1332256900.totalCap] using
      (hbox he).2.2.1
  · apply (weightedTotalDegree_le_iff (![0,0,1,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [R.jointHelperFlag,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
      WeightedHardLShapeDeflatedCapacityW1332256900.derivativeCap,
      WeightedHardLShapeDeflatedCapacityW1332256900.totalCap] using
      (hbox he).2.1
  · apply (weightedTotalDegree_le_iff (![0,1,1,1] : Fin 4→Nat) H _).mpr
    intro e he
    rw [weight_fin4]
    simpa [R.jointHelperFlag,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
      WeightedHardLShapeDeflatedCapacityW1332256900.jetCap,
      WeightedHardLShapeDeflatedCapacityW1332256900.derivativeCap,
      WeightedHardLShapeDeflatedCapacityW1332256900.totalCap] using
      (hbox he).1

def primaryReducedCut (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  rtySurfaceMap (polynomialEmbedding K)
    (reducedAgreementNumerator2 F 122 w
      (fun j => (j.factorial : K)⁻¹) x u)

theorem primaryReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F w x u-primaryReducedCut F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F 122 w
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,primaryReducedCut,map_sub,
    rtySurfaceMapHom_apply] using h

def regularFamily (F : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) : Finset (Polynomial K) :=
  Gamma.filter fun P => jetSpecialization2 P F=0 ∧
    jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0

/-- One-incidence count for one exited factor and the exact joint flag. -/
theorem joint_regularHelper_factor_scaled_le [CharP K 2130706433]
    (nodeSet : Finset I) (x u : I→K) (hnodes : nodeSet.card=R.n)
    (F H : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf (3 : Fin 4))
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤244)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤740)
    (hHelper : JointRegularHelper nodeSet x u F H)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v small) :
    (regularFamily F Gamma).card*(R.a-R.v)≤(R.n-R.v)*
      flagMixed (exactFlag (rtySource F)) R.jointHelperFlag
        R.primaryAgreement := by
  obtain ⟨hF,hH,hHbox,hproper,hvanish⟩ := hHelper
  have hsub : regularFamily F Gamma⊆Gamma := Finset.filter_subset _ _
  have hSource : PolynomialInFlag R.primaryFlag (rtySource F) :=
    WeightedFactorFlagBudgetW1332246900.rtySource_in_flag_of_weights F
      R.primaryFlag hT hRT hJet
  have hTdegree : F.degreeOf (3 : Fin 4)≤122 := by
    rw [← T_weight_eq_degreeOf]
    exact hT
  have hCut : ∀ i∈nodeSet,PolynomialInFlag R.primaryAgreement
      (primaryReducedCut F (x i) (u i)) := by
    intro i hi
    apply (support_subset_flagSupport_iff _ _).mp
    exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F
      w 740 244 122 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hTdegree hRT hJet (fun j => (j.factorial : K)⁻¹) (x i) (u i)
  have hHsolution : ∀ P∈regularFamily F Gamma,jetSpecialization2 P H=0 := by
    intro P hP
    obtain ⟨hPG,hPF,hPreg⟩ := Finset.mem_filter.mp hP
    exact hvanish P (hdegree P hPG) (hagrees P hPG) hPF hPreg
  have hh :=
    WeightedProperHelperCountW1332246900.fixed_second_hereditary_scaled
      F H hF.irreducible (by omega) hproper
      (regularFamily F Gamma) nodeSet x u prime w R.a R.v small
      (by norm_num [w,prime]) (by norm_num [R.v,R.a,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a])
      (by rw [hnodes]; norm_num [R.n,R.a,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a])
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2.1)
      (fun P hP => (Finset.mem_filter.mp hP).2.2) hHsolution
      (fun P hP => hagrees P (hsub hP))
      (hereditaryCommonCap_mono hcommon hsub)
      (fun i => primaryReducedCut F (x i) (u i))
      (fun i hi => primaryReducedCut_congruent F (x i) (u i))
      (exactFlag (rtySource F)) R.primaryFlag R.jointHelperFlag
      R.primaryAgreement (polynomialIn_exactFlag _) hSource
      (joint_helper_box_flag H hHbox) hCut
      (by rw [hnodes]; norm_num [small,R.a,R.v,R.n,R.primaryAgreement,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement])
      (by norm_num [R.primaryFlag,prime,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryFlag])
      (by norm_num [R.primaryFlag,R.jointHelperFlag,prime,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryFlag,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag])
      (by norm_num [R.primaryFlag,R.jointHelperFlag,prime,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryFlag,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag])
  rw [hnodes] at hh
  exact hh

def armBReducedCut (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  rtySurfaceMap (polynomialEmbedding K)
    (reducedAgreementNumerator2 F 27 w
      (fun j => (j.factorial : K)⁻¹) x u)

theorem armBReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F w x u-armBReducedCut F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F 27 w
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,armBReducedCut,map_sub,
    rtySurfaceMapHom_apply] using h

theorem armBReducedCut_in_flag (F : MvPolynomial (Fin 4) K)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤54)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤212)
    (x u : K) : PolynomialInFlag R.armBAgreement (armBReducedCut F x u) := by
  have hTdegree : F.degreeOf 3≤27 := by
    rw [← T_weight_eq_degreeOf]
    exact hT
  apply (support_subset_flagSupport_iff _ _).mp
  exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F
    w 212 54 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hTdegree hRT hJ (fun j => (j.factorial : K)⁻¹) x u

/-- Old two-incidence count specialized to the second L-terminal arm. -/
theorem individual_armB_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤54)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤212)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hn : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v small) :
    Gamma.card*(R.a-R.v)^2≤(R.n-R.v)^2*
      flagMixed (exactFlag (rtySource F)) R.armBAgreement R.armBAgreement := by
  have hsource : PolynomialInFlag R.armBFlag (rtySource F) :=
    WeightedFactorFlagBudgetW1332246900.rtySource_in_flag_of_weights F
      R.armBFlag hT hRT hJ
  have hsmallCurve : small*(R.a-R.v)≤
      (nodeSet.card-R.v)*R.armBAgreement.all := by
    rw [hn]
    norm_num [small,R.a,R.v,R.n,R.armBAgreement,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBAgreement]
  have hsmallSurface : small*(R.a-R.v)^2≤
      (nodeSet.card-R.v)^2*R.armBAgreement.all^2 := by
    rw [hn]
    norm_num [small,R.a,R.v,R.n,R.armBAgreement,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBAgreement]
  have hgate : (R.armBAgreement.yz+R.armBAgreement.all)*R.armBFlag.all+
      (R.armBFlag.yz+R.armBFlag.all)*R.armBAgreement.all<prime := by
    norm_num [R.armBAgreement,R.armBFlag,prime,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBAgreement,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBFlag]
  have h := original_regular_of_congruent_active_flags F hF Gamma nodeSet x u
    hinj prime w R.a R.v small (by norm_num [w]) (by norm_num [w,prime])
    (by norm_num [prime])
    (by norm_num [w,R.a,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a])
    (by norm_num [R.v,R.a,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a])
    (by rw [hn]; norm_num [R.n,R.a,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a])
    hdegree hsolution hregular hagreement hcommon
    (fun i => armBReducedCut F (x i) (u i))
    (fun i _ => armBReducedCut_congruent F (x i) (u i))
    (exactFlag (rtySource F)) R.armBFlag R.armBAgreement
    (polynomialIn_exactFlag _) hsource
    (fun i _ => armBReducedCut_in_flag F hT hRT hJ (x i) (u i))
    hsmallCurve hsmallSurface
    (by norm_num [R.armBFlag,prime,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armBFlag]) hgate
  rw [hn] at h
  exact h

/-- Full active-factor hard-branch bound.  Every consumer, partition and
coupled degree charge is internal; the sole remaining premise is the exact
three-way source/helper producer. -/
theorem hard_lshape_active_scaled_of_joint_step [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hnodes : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v small)
    (hstep : ∀ T, T⊆positiveTFactors Q → T.Nonempty → LHeavy id T →
      ∃ F∈T,∃ H,JointRegularHelper nodeSet x u F H) :
    (∑ F∈positiveTFactors Q,(regularFamily F Gamma).card)*(R.a-R.v)^2≤
      R.jointCommonNumerator R.armAFlag R.armAExitFlag R.armAAgreement := by
  apply lterminal_partition_counts_scaled Q hQ hQT hQRT hQJ
    (positiveTFactors Q) le_rfl
    (fun F => ∃ H,JointRegularHelper nodeSet x u F H)
    hstep (fun F => (regularFamily F Gamma).card)
  · intro F hF hcert
    obtain ⟨H,hH⟩ := hcert
    obtain ⟨hFirred,hFdiv,hFpos⟩ := positiveTFactors_spec Q F hF
    have hdvd (weights : Fin 4→Nat) :
        MvPolynomial.weightedTotalDegree weights F≤
          MvPolynomial.weightedTotalDegree weights Q :=
      weightedTotalDegree_le_of_dvd weights F Q hFdiv hQ
    exact joint_regularHelper_factor_scaled_le nodeSet x u hnodes F H hFpos
      ((hdvd ![0,0,0,1]).trans hQT) ((hdvd ![0,0,1,1]).trans hQRT)
      ((hdvd ![0,1,1,1]).trans hQJ) hH Gamma hdegree hagrees hcommon
  · intro T hT hTJ hTD F
    let P : MvPolynomial (Fin 4) K := ∏ G∈T,G
    have hirr : ∀ G∈T,Irreducible G := fun G hG =>
      (positiveTFactors_spec Q G (hT hG)).1
    have hP : P≠0 := product_ne_zero T id hirr
    have hdiv : F.1∣P := Finset.dvd_prod_of_mem id F.2
    have hnested := derivative_nested_bounds P
    have hhalf : derivativeDegree P/2≤55/2 := Nat.div_le_div_right hTD
    have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
      hnested.1.trans (by norm_num at hhalf ⊢; exact hhalf)
    have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤55 :=
      hnested.2.trans hTD
    have hFT := (weightedTotalDegree_le_of_dvd ![0,0,0,1]
      F.1 P hdiv hP).trans hPT
    have hFRT := (weightedTotalDegree_le_of_dvd ![0,0,1,1]
      F.1 P hdiv hP).trans hPRT
    have hFJ := (weightedTotalDegree_le_of_dvd ![0,1,1,1]
      F.1 P hdiv hP).trans hTJ
    have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
    exact WeightedIdentityLShapeCornerW1332256900.individual_old_scaled
      F.1 (hirr F.1 F.2).ne_zero hFT hFRT hFJ
      (regularFamily F.1 Gamma) nodeSet x u hinj hnodes
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2.1)
      (fun P hP => (Finset.mem_filter.mp hP).2.2)
      (fun P hP => hagrees P (hsub hP))
      (hereditaryCommonCap_mono hcommon hsub)
  · intro T hT hTJ hTD F
    let P : MvPolynomial (Fin 4) K := ∏ G∈T,G
    have hirr : ∀ G∈T,Irreducible G := fun G hG =>
      (positiveTFactors_spec Q G (hT hG)).1
    have hP : P≠0 := product_ne_zero T id hirr
    have hdiv : F.1∣P := Finset.dvd_prod_of_mem id F.2
    have hnested := derivative_nested_bounds P
    have hhalf : derivativeDegree P/2≤54/2 := Nat.div_le_div_right hTD
    have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
      hnested.1.trans (by norm_num at hhalf ⊢; exact hhalf)
    have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤54 :=
      hnested.2.trans hTD
    have hFT := (weightedTotalDegree_le_of_dvd ![0,0,0,1]
      F.1 P hdiv hP).trans hPT
    have hFRT := (weightedTotalDegree_le_of_dvd ![0,0,1,1]
      F.1 P hdiv hP).trans hPRT
    have hFJ := (weightedTotalDegree_le_of_dvd ![0,1,1,1]
      F.1 P hdiv hP).trans hTJ
    have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
    exact individual_armB_scaled F.1 (hirr F.1 F.2).ne_zero hFT hFRT hFJ
      (regularFamily F.1 Gamma) nodeSet x u hinj hnodes
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2.1)
      (fun P hP => (Finset.mem_filter.mp hP).2.2)
      (fun P hP => hagrees P (hsub hP))
      (hereditaryCommonCap_mono hcommon hsub)

end
end ProximityPrize.SubmissionLower.WeightedIdentityHardLShapeIntegrationW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedIdentityHardLShapeIntegrationW1332256900.joint_regularHelper_factor_scaled_le
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityHardLShapeIntegrationW1332256900.jointRegularHelper_of_deflated_source
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityHardLShapeIntegrationW1332256900.individual_armB_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityHardLShapeIntegrationW1332256900.hard_lshape_active_scaled_of_joint_step
