import WeightedIdentityExtendedLShapeAggregationW1332266900
import WeightedHeavyBatchPartitionW1332246900
import WeightedProperHelperCountW1332246900
import Order2HereditaryActiveSurface6900

/-!
# Semantic extended-L terminal consumer at W=133226

This module closes the consumer side of the full-node `W=133226` branch.  A
generic strict descent stops at one of four terminals: the two old L-shape
arms, derivative degree at most three, or jet degree at most 32.  The old arms
share their flag budget with all helper exits; the skinny arms use independent
aggregate caps.  The only deliberately abstract input left to the source side
is a per-step `JointRegularHelper` certificate.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityExtendedLShapeIntegrationW1332266900

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
open WeightedHeavyBatchPartitionW1332246900
open WeightedIdentityExtendedLShapeArithmeticW1332266900
open WeightedIdentityExtendedLShapeAggregationW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

namespace R
abbrev n := WeightedIdentityExtendedLShapeArithmeticW1332266900.n
abbrev a := WeightedIdentityExtendedLShapeArithmeticW1332266900.a
abbrev v := WeightedIdentityExtendedLShapeArithmeticW1332266900.v
abbrev w := WeightedIdentityExtendedLShapeArithmeticW1332266900.w
abbrev small := WeightedIdentityExtendedLShapeArithmeticW1332266900.small
abbrev prime := WeightedIdentityExtendedLShapeArithmeticW1332266900.prime
abbrev primaryFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag
abbrev helperFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag
abbrev primaryAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement
abbrev armAFlag := WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag
abbrev armBFlag := WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag
abbrev armAExitFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armAExitFlag
abbrev armBExitFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armBExitFlag
abbrev armAAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armAAgreement
abbrev armBAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armBAgreement
abbrev derivativeSkinnyFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyFlag
abbrev derivativeSkinnyAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyAgreement
abbrev jetSkinnyFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyFlag
abbrev jetSkinnyAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyAgreement
abbrev commonNumerator :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.commonNumerator
end R

def factorFlag (F : MvPolynomial (Fin 4) K) : FlagDegree :=
  exactFlag (rtySource F)

section Terminal

variable {ι : Type*} [DecidableEq ι]

def ExtendedTerminal (factor : ι→MvPolynomial (Fin 4) K)
    (T : Finset ι) : Prop :=
  let P := ∏ i∈T,factor i
  (jetDegree P≤211 ∧ derivativeDegree P≤55) ∨
    (jetDegree P≤212 ∧ derivativeDegree P≤54) ∨
    derivativeDegree P≤3 ∨ jetDegree P≤32

def ExtendedHeavy (factor : ι→MvPolynomial (Fin 4) K)
    (T : Finset ι) : Prop :=
  let P := ∏ i∈T,factor i
  (213≤jetDegree P ∧ 4≤derivativeDegree P) ∨
    (33≤jetDegree P ∧ 56≤derivativeDegree P) ∨
    (212≤jetDegree P ∧ 55≤derivativeDegree P)

theorem extendedHeavy_iff_not_terminal
    (factor : ι→MvPolynomial (Fin 4) K) (T : Finset ι) :
    ExtendedHeavy factor T ↔ ¬ExtendedTerminal factor T := by
  simp only [ExtendedHeavy,ExtendedTerminal]
  omega

theorem extendedHeavy_nonempty
    (factor : ι→MvPolynomial (Fin 4) K) (T : Finset ι)
    (h : ExtendedHeavy factor T) : T.Nonempty := by
  by_contra hn
  have hT : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hnot := (extendedHeavy_iff_not_terminal factor T).mp h
  rw [hT] at hnot
  apply hnot
  right
  right
  right
  simp [jetDegree,MvPolynomial.weightedTotalDegree]

/-- Generic strict removal.  In particular, neither the isolated corner nor
either high/high region may remain in the terminal product. -/
theorem extended_terminal_partition
    (factor : ι→MvPolynomial (Fin 4) K) (ambient : Finset ι)
    (certificate : ι→Prop)
    (hstep : ∀ T, T⊆ambient → T.Nonempty → ExtendedHeavy factor T →
      ∃ i∈T,certificate i) :
    ∃ exited rest : Finset ι,
      rest⊆ambient ∧ exited=ambient\rest ∧ Disjoint exited rest ∧
      exited∪rest=ambient ∧ ExtendedTerminal factor rest ∧
      ∀ i∈exited,certificate i := by
  obtain ⟨rest,hrest,hterminal,hcert⟩ :=
    exists_certified_terminal_subset ambient (ExtendedTerminal factor)
      certificate (fun T hT hnot =>
        hstep T hT
          (extendedHeavy_nonempty factor T
            ((extendedHeavy_iff_not_terminal factor T).mpr hnot))
          ((extendedHeavy_iff_not_terminal factor T).mpr hnot))
  refine ⟨ambient\rest,rest,hrest,rfl,?_,?_,hterminal,hcert⟩
  · exact Finset.disjoint_left.mpr
      (fun i hi hr => (Finset.mem_sdiff.mp hi).2 hr)
  · rw [Finset.union_comm]
    exact Finset.union_sdiff_of_subset hrest

end Terminal

theorem sum_sdiff_subtype_add_rest {α : Type*} [DecidableEq α]
    (ambient rest : Finset α) (hrest : rest⊆ambient) (f : α→Nat) :
    (∑ i : ↥(ambient\rest),f i.1)+(∑ i : ↥rest,f i.1)=
      ∑ i : ↥ambient,f i.1 := by
  rw [Finset.sum_coe_sort,Finset.sum_coe_sort,Finset.sum_coe_sort]
  exact sum_exited_add_rest ambient rest hrest f

/-- The ambient product gives one shared primary cumulative budget. -/
theorem primary_partition_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient) :
    ((∑ F : ↥(ambient\rest),
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤744) ∧
    ((∑ F : ↥(ambient\rest),((factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤244) ∧
    ((∑ F : ↥(ambient\rest),(factorFlag F.1).all)+
      (∑ F : ↥rest,(factorFlag F.1).all)≤122) := by
  have hbudget := exactFlag_cumulative_of_weight_bounds ambient Q hQ
    (positiveT_subset_product_dvd ambient Q hQ hambient) R.primaryFlag
    hQT hQRT hQJ
  have splitS := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).all)
  have splitM := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).yz+(factorFlag F).all)
  have splitJ := sum_sdiff_subtype_add_rest ambient rest hrest
    (fun F => (factorFlag F).zOnly+(factorFlag F).yz+(factorFlag F).all)
  exact ⟨splitJ.le.trans hbudget.2.2,splitM.le.trans hbudget.2.1,
    splitS.le.trans hbudget.1⟩

/-- Exact cumulative budget of the terminal product itself. -/
theorem rest_product_budgets
    (Q : MvPolynomial (Fin 4) K)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (p : FlagDegree)
    (hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1]
      (∏ F∈rest,F)≤p.all)
    (hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1]
      (∏ F∈rest,F)≤p.yz+p.all)
    (hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1]
      (∏ F∈rest,F)≤p.zOnly+p.yz+p.all) :
    (∑ F : ↥rest,(factorFlag F.1).all)≤p.all ∧
    (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤
      p.yz+p.all ∧
    (∑ F : ↥rest,((factorFlag F.1).zOnly+
      (factorFlag F.1).yz+(factorFlag F.1).all))≤p.zOnly+p.yz+p.all := by
  let P : MvPolynomial (Fin 4) K := ∏ F∈rest,F
  have hirr : ∀ F∈rest,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hambient (hrest hF))).1
  have hP : P≠0 := product_ne_zero rest id hirr
  exact exactFlag_cumulative_of_weight_bounds rest P hP dvd_rfl p
    hPT hPRT hPJ

def profileFlag (M S T : Nat) : FlagDegree := ⟨M-S,S-T,T⟩

def profileAgreement (M S T : Nat) : FlagDegree :=
  honestReducedAgreementFlag R.w M S T

def profileReducedCut (T : Nat) (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  rtySurfaceMap (polynomialEmbedding K)
    (reducedAgreementNumerator2 F T R.w
      (fun j => (j.factorial : K)⁻¹) x u)

theorem profileReducedCut_congruent (T : Nat)
    (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F R.w x u-profileReducedCut T F x u := by
  have h := map_dvd (rtySurfaceMapHom (polynomialEmbedding K))
    (agreementNumerator2_sub_reducedT_dvd F T R.w
      (fun j => (j.factorial : K)⁻¹) x u)
  simpa only [rtySource,rtyAgreement,profileReducedCut,map_sub,
    rtySurfaceMapHom_apply] using h

theorem profileReducedCut_in_flag
    (M S T : Nat) (hTpos : 1≤T) (hTS : T≤S) (hSM : S<M) (hS2 : 2≤S)
    (F : MvPolynomial (Fin 4) K)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤T)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤S)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤M)
    (x u : K) :
    PolynomialInFlag (profileAgreement M S T)
      (profileReducedCut T F x u) := by
  have hTdegree : F.degreeOf 3≤T := by
    rw [← T_weight_eq_degreeOf]
    exact hT
  apply (support_subset_flagSupport_iff _ _).mp
  exact honest_reduced_rty_agreement_support (polynomialEmbedding K) F
    R.w M S T hTpos hTS hSM hS2 hTdegree hRT hJ
    (fun j => (j.factorial : K)⁻¹) x u

def regularFamily (F : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) : Finset (Polynomial K) :=
  Gamma.filter fun P => jetSpecialization2 P F=0 ∧
    jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0

/-- One generic two-incidence consumer; all four terminal-specific consumers
below are exact instantiations. -/
theorem individual_profile_scaled [CharP K 2130706433]
    (M S T : Nat) (hTpos : 1≤T) (hTS : T≤S) (hSM : S<M) (hS2 : 2≤S)
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤T)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤S)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤M)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hn : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small)
    (hsmallCurve : R.small*(R.a-R.v)≤
      (R.n-R.v)*(profileAgreement M S T).all)
    (hsmallSurface : R.small*(R.a-R.v)^2≤
      (R.n-R.v)^2*(profileAgreement M S T).all^2)
    (hMprime : M<R.prime)
    (hgate : ((profileAgreement M S T).yz+
        (profileAgreement M S T).all)*(profileFlag M S T).all+
      ((profileFlag M S T).yz+(profileFlag M S T).all)*
        (profileAgreement M S T).all<R.prime) :
    Gamma.card*(R.a-R.v)^2≤(R.n-R.v)^2*
      flagMixed (exactFlag (rtySource F)) (profileAgreement M S T)
        (profileAgreement M S T) := by
  have hsource : PolynomialInFlag (profileFlag M S T) (rtySource F) := by
    apply WeightedFactorFlagBudgetW1332246900.rtySource_in_flag_of_weights
    · simpa [profileFlag] using hT
    · simpa [profileFlag, Nat.sub_add_cancel hTS] using hRT
    · simp only [profileFlag]
      have hSMle : S≤M := Nat.le_of_lt hSM
      omega
  have h := original_regular_of_congruent_active_flags F hF Gamma nodeSet x u
    hinj R.prime R.w R.a R.v R.small
    (by norm_num [R.w,WeightedIdentityExtendedLShapeArithmeticW1332266900.w])
    (by norm_num [R.w,R.prime,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
    (by norm_num [R.prime,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
    (by norm_num [R.w,R.a,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.a])
    (by norm_num [R.v,R.a,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.a])
    (by rw [hn]; norm_num [R.n,R.a,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.a])
    hdegree hsolution hregular hagreement hcommon
    (fun i => profileReducedCut T F (x i) (u i))
    (fun i _ => profileReducedCut_congruent T F (x i) (u i))
    (exactFlag (rtySource F)) (profileFlag M S T)
    (profileAgreement M S T) (polynomialIn_exactFlag _) hsource
    (fun i _ => profileReducedCut_in_flag M S T hTpos hTS hSM hS2 F
      hT hRT hJ (x i) (u i))
    (by simpa [hn] using hsmallCurve)
    (by simpa [hn] using hsmallSurface)
    (by
      simp only [profileFlag]
      omega) hgate
  rw [hn] at h
  exact h

theorem individual_armA_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤55)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤211)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hn : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small) :
    Gamma.card*(R.a-R.v)^2≤(R.n-R.v)^2*
      flagMixed (exactFlag (rtySource F)) R.armAAgreement
        R.armAAgreement := by
  simpa [profileAgreement,R.armAAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armAAgreement] using
    (individual_profile_scaled 211 55 27 (by omega) (by omega) (by omega)
      (by omega) F hF hT hRT hJ Gamma nodeSet x u hinj hn hdegree
      hsolution hregular hagreement hcommon
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [profileAgreement,profileFlag,R.w,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime,
        honestReducedAgreementFlag]))

theorem individual_armB_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤27)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤54)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤212)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hn : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small) :
    Gamma.card*(R.a-R.v)^2≤(R.n-R.v)^2*
      flagMixed (exactFlag (rtySource F)) R.armBAgreement
        R.armBAgreement := by
  simpa [profileAgreement,R.armBAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armBAgreement] using
    (individual_profile_scaled 212 54 27 (by omega) (by omega) (by omega)
      (by omega) F hF hT hRT hJ Gamma nodeSet x u hinj hn hdegree
      hsolution hregular hagreement hcommon
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [profileAgreement,profileFlag,R.w,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime,
        honestReducedAgreementFlag]))

/-- The first new skinny consumer.  The loose T=7 box is intentional: its
agreement `all` coordinate dominates `small`, so the absorption proof remains
valid even if this theorem is later generalized below the full node count. -/
theorem individual_derivative_skinny_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤7)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤7)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤744)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hn : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small) :
    Gamma.card*(R.a-R.v)^2≤(R.n-R.v)^2*
      flagMixed (exactFlag (rtySource F)) R.derivativeSkinnyAgreement
        R.derivativeSkinnyAgreement := by
  simpa [profileAgreement,R.derivativeSkinnyAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyAgreement]
    using
    (individual_profile_scaled 744 7 7 (by omega) (by omega) (by omega)
      (by omega) F hF hT hRT hJ Gamma nodeSet x u hinj hn hdegree
      hsolution hregular hagreement hcommon
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [profileAgreement,profileFlag,R.w,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime,
        honestReducedAgreementFlag]))

/-- The second new skinny consumer. -/
theorem individual_jet_skinny_scaled [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤32)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤32)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤33)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hn : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P F=0)
    (hregular : ∀ P∈Gamma,
      jetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0)
    (hagreement : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small) :
    Gamma.card*(R.a-R.v)^2≤(R.n-R.v)^2*
      flagMixed (exactFlag (rtySource F)) R.jetSkinnyAgreement
        R.jetSkinnyAgreement := by
  simpa [profileAgreement,R.jetSkinnyAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyAgreement]
    using
    (individual_profile_scaled 33 32 32 (by omega) (by omega) (by omega)
      (by omega) F hF hT hRT hJ Gamma nodeSet x u hinj hn hdegree
      hsolution hregular hagreement hcommon
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.small,R.a,R.v,R.n,profileAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [profileAgreement,profileFlag,R.w,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime,
        honestReducedAgreementFlag]))

/-- Exact semantic payload expected from the later source/band producer. -/
def JointRegularHelper (nodeSet : Finset I) (nodes values : I→K)
    (F H : MvPolynomial (Fin 4) K) : Prop :=
  Prime F ∧ H≠0 ∧ PolynomialInFlag R.helperFlag (rtySource H) ∧
  ¬F∣H ∧
  ∀ (P : Polynomial K), P.natDegree≤R.w →
    R.a≤(nodeSet.filter fun i => P.eval (nodes i)=values i).card →
    localJetSpecialization2 P F=0 →
    localJetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0 →
    localJetSpecialization2 P H=0

def primaryReducedCut (F : MvPolynomial (Fin 4) K) (x u : K) :
    MvPolynomial (Fin 3) (GenericField K) := profileReducedCut 122 F x u

theorem primaryReducedCut_congruent (F : MvPolynomial (Fin 4) K) (x u : K) :
    rtySource F∣rtyAgreement F R.w x u-primaryReducedCut F x u :=
  profileReducedCut_congruent 122 F x u

/-- One-incidence count for one helper-exited factor. -/
theorem joint_regularHelper_factor_scaled_le [CharP K 2130706433]
    (nodeSet : Finset I) (x u : I→K) (hnodes : nodeSet.card=R.n)
    (F H : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf (3 : Fin 4))
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤244)
    (hJet : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤744)
    (hHelper : JointRegularHelper nodeSet x u F H)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hagrees : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small) :
    (regularFamily F Gamma).card*(R.a-R.v)≤(R.n-R.v)*
      flagMixed (exactFlag (rtySource F)) R.helperFlag
        R.primaryAgreement := by
  obtain ⟨hF,_hH,hHflag,hproper,hvanish⟩ := hHelper
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
      R.w 744 244 122 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hTdegree hRT hJet (fun j => (j.factorial : K)⁻¹)
      (x i) (u i)
  have hHsolution : ∀ P∈regularFamily F Gamma,
      jetSpecialization2 P H=0 := by
    intro P hP
    obtain ⟨hPG,hPF,hPreg⟩ := Finset.mem_filter.mp hP
    exact hvanish P (hdegree P hPG) (hagrees P hPG) hPF hPreg
  have hh :=
    WeightedProperHelperCountW1332246900.fixed_second_hereditary_scaled
      F H hF.irreducible (by omega) hproper
      (regularFamily F Gamma) nodeSet x u R.prime R.w R.a R.v R.small
      (by norm_num [R.w,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [R.v,R.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a])
      (by rw [hnodes]; norm_num [R.n,R.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a])
      (fun P hP => hdegree P (hsub hP))
      (fun P hP => (Finset.mem_filter.mp hP).2.1)
      (fun P hP => (Finset.mem_filter.mp hP).2.2) hHsolution
      (fun P hP => hagrees P (hsub hP))
      (hereditaryCommonCap_mono hcommon hsub)
      (fun i => primaryReducedCut F (x i) (u i))
      (fun i hi => primaryReducedCut_congruent F (x i) (u i))
      (exactFlag (rtySource F)) R.primaryFlag R.helperFlag
      R.primaryAgreement (polynomialIn_exactFlag _) hSource hHflag hCut
      (by rw [hnodes]; norm_num [R.small,R.a,R.v,R.n,R.primaryAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.small,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag])
      (by norm_num [R.primaryFlag,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [R.primaryFlag,R.helperFlag,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
      (by norm_num [R.primaryFlag,R.helperFlag,R.prime,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.prime])
  rw [hnodes] at hh
  exact hh

theorem armA_partition_six_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤211)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤55) :
    ((∑ F : ↥(ambient\rest),
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤744) ∧
    ((∑ F : ↥(ambient\rest),((factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤244) ∧
    ((∑ F : ↥(ambient\rest),(factorFlag F.1).all)+
      (∑ F : ↥rest,(factorFlag F.1).all)≤122) ∧
    (∑ F : ↥rest,((factorFlag F.1).zOnly+
      (factorFlag F.1).yz+(factorFlag F.1).all))≤211 ∧
    (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤55 ∧
    (∑ F : ↥rest,(factorFlag F.1).all)≤27 := by
  obtain ⟨hJ,hM,hS⟩ := primary_partition_budgets Q hQ hQT hQRT hQJ
    ambient rest hambient hrest
  let P : MvPolynomial (Fin 4) K := ∏ F∈rest,F
  have hnested := derivative_nested_bounds P
  have hhalf : derivativeDegree P/2≤55/2 := Nat.div_le_div_right hrestD
  have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
    hnested.1.trans (by norm_num at hhalf ⊢; exact hhalf)
  have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤55 :=
    hnested.2.trans hrestD
  have hr := rest_product_budgets Q ambient rest hambient hrest R.armAFlag
    (by simpa [R.armAFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag] using hPT)
    (by simpa [R.armAFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag] using hPRT)
    (by simpa [R.armAFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag,
      jetDegree,jetWeights] using hrestJ)
  exact ⟨hJ,hM,hS,by simpa [R.armAFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag] using hr.2.2,
    by simpa [R.armAFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag] using hr.2.1,
    by simpa [R.armAFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag] using hr.1⟩

theorem armB_partition_six_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤212)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤54) :
    ((∑ F : ↥(ambient\rest),
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,
        ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤744) ∧
    ((∑ F : ↥(ambient\rest),((factorFlag F.1).yz+(factorFlag F.1).all))+
      (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤244) ∧
    ((∑ F : ↥(ambient\rest),(factorFlag F.1).all)+
      (∑ F : ↥rest,(factorFlag F.1).all)≤122) ∧
    (∑ F : ↥rest,((factorFlag F.1).zOnly+
      (factorFlag F.1).yz+(factorFlag F.1).all))≤212 ∧
    (∑ F : ↥rest,((factorFlag F.1).yz+(factorFlag F.1).all))≤54 ∧
    (∑ F : ↥rest,(factorFlag F.1).all)≤27 := by
  obtain ⟨hJ,hM,hS⟩ := primary_partition_budgets Q hQ hQT hQRT hQJ
    ambient rest hambient hrest
  let P : MvPolynomial (Fin 4) K := ∏ F∈rest,F
  have hnested := derivative_nested_bounds P
  have hhalf : derivativeDegree P/2≤54/2 := Nat.div_le_div_right hrestD
  have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
    hnested.1.trans (by norm_num at hhalf ⊢; exact hhalf)
  have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤54 :=
    hnested.2.trans hrestD
  have hr := rest_product_budgets Q ambient rest hambient hrest R.armBFlag
    (by simpa [R.armBFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag] using hPT)
    (by simpa [R.armBFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag] using hPRT)
    (by simpa [R.armBFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag,
      jetDegree,jetWeights] using hrestJ)
  exact ⟨hJ,hM,hS,by simpa [R.armBFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag] using hr.2.2,
    by simpa [R.armBFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag] using hr.2.1,
    by simpa [R.armBFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag] using hr.1⟩

theorem armA_partition_counts_scaled
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤211)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤55)
    (count : MvPolynomial (Fin 4) K→Nat)
    (hexit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.helperFlag R.primaryAgreement)
    (hcheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
      (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armAAgreement
        R.armAAgreement) :
    ((∑ F∈ambient\rest,count F)+(∑ F∈rest,count F))*(R.a-R.v)^2≤
      R.commonNumerator R.armAFlag R.armAExitFlag R.armAAgreement := by
  obtain ⟨hJ,hM,hS,hrJ,hrM,hrS⟩ :=
    armA_partition_six_budgets Q hQ hQT hQRT hQJ ambient rest hambient
      hrest hrestJ hrestD
  have h := coupled_armA_counts_scaled
    (fun F : ↥(ambient\rest) => count F.1)
    (fun F : ↥rest => count F.1)
    (fun F : ↥(ambient\rest) => factorFlag F.1)
    (fun F : ↥rest => factorFlag F.1)
    hexit hcheap hJ hM hS hrJ hrM hrS
  simpa only [Finset.sum_coe_sort] using h

theorem armB_partition_counts_scaled
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hrestJ : jetDegree (∏ F∈rest,F)≤212)
    (hrestD : derivativeDegree (∏ F∈rest,F)≤54)
    (count : MvPolynomial (Fin 4) K→Nat)
    (hexit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.helperFlag R.primaryAgreement)
    (hcheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
      (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armBAgreement
        R.armBAgreement) :
    ((∑ F∈ambient\rest,count F)+(∑ F∈rest,count F))*(R.a-R.v)^2≤
      R.commonNumerator R.armBFlag R.armBExitFlag R.armBAgreement := by
  obtain ⟨hJ,hM,hS,hrJ,hrM,hrS⟩ :=
    armB_partition_six_budgets Q hQ hQT hQRT hQJ ambient rest hambient
      hrest hrestJ hrestD
  have h := coupled_armB_counts_scaled
    (fun F : ↥(ambient\rest) => count F.1)
    (fun F : ↥rest => count F.1)
    (fun F : ↥(ambient\rest) => factorFlag F.1)
    (fun F : ↥rest => factorFlag F.1)
    hexit hcheap hJ hM hS hrJ hrM hrS
  simpa only [Finset.sum_coe_sort] using h

/-- Independent aggregate count for a skinny terminal.  Exits still share the
ambient primary flag, and rest factors share the terminal-product flag; only
the two groups are charged independently. -/
theorem skinny_partition_counts_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (restFlag restAgreement : FlagDegree)
    (hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1]
      (∏ F∈rest,F)≤restFlag.all)
    (hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1]
      (∏ F∈rest,F)≤restFlag.yz+restFlag.all)
    (hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1]
      (∏ F∈rest,F)≤restFlag.zOnly+restFlag.yz+restFlag.all)
    (count : MvPolynomial (Fin 4) K→Nat)
    (hexit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.helperFlag R.primaryAgreement)
    (hcheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
      (R.n-R.v)^2*flagMixed (factorFlag F.1) restAgreement restAgreement)
    (exitCap restCap : Nat)
    (hexitCap : (R.n-R.v)*flagMixed R.primaryFlag R.helperFlag
      R.primaryAgreement≤exitCap*(R.a-R.v))
    (hrestCap : (R.n-R.v)^2*flagMixed restFlag restAgreement restAgreement≤
      restCap*(R.a-R.v)^2) :
    (∑ F : ↥(ambient\rest),count F.1)+(∑ F : ↥rest,count F.1)≤
      exitCap+restCap := by
  obtain ⟨hJ,hM,hS⟩ := primary_partition_budgets Q hQ hQT hQRT hQJ
    ambient rest hambient hrest
  obtain ⟨hrS,hrM,hrJ⟩ := rest_product_budgets Q ambient rest
    hambient hrest restFlag hPT hPRT hPJ
  have heS : (∑ F : ↥(ambient\rest),(factorFlag F.1).all)≤
      R.primaryFlag.all := by
    norm_num [R.primaryFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag] at hS ⊢
    omega
  have heM : (∑ F : ↥(ambient\rest),
      ((factorFlag F.1).yz+(factorFlag F.1).all))≤
      R.primaryFlag.yz+R.primaryFlag.all := by
    norm_num [R.primaryFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag] at hM ⊢
    omega
  have heJ : (∑ F : ↥(ambient\rest),
      ((factorFlag F.1).zOnly+(factorFlag F.1).yz+(factorFlag F.1).all))≤
      R.primaryFlag.zOnly+R.primaryFlag.yz+R.primaryFlag.all := by
    norm_num [R.primaryFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag] at hJ ⊢
    omega
  have heScaled :=
    WeightedRepresentativeCountLedgerW1332246900.aggregate_scaled_flags
      (fun F : ↥(ambient\rest) => count F.1)
      (fun F : ↥(ambient\rest) => factorFlag F.1)
      R.primaryFlag R.helperFlag R.primaryAgreement (R.a-R.v) (R.n-R.v)
      hexit heS heM heJ
  have hrScaled :=
    WeightedRepresentativeCountLedgerW1332246900.aggregate_scaled_flags
      (fun F : ↥rest => count F.1) (fun F : ↥rest => factorFlag F.1)
      restFlag restAgreement restAgreement ((R.a-R.v)^2) ((R.n-R.v)^2)
      hcheap hrS hrM hrJ
  have heCard :=
    WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
      (∑ F : ↥(ambient\rest),count F.1) (R.a-R.v)
      ((R.n-R.v)*flagMixed R.primaryFlag R.helperFlag R.primaryAgreement)
      exitCap (by norm_num [R.a,R.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v])
      heScaled hexitCap
  have hrCard :=
    WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
      (∑ F : ↥rest,count F.1) ((R.a-R.v)^2)
      ((R.n-R.v)^2*flagMixed restFlag restAgreement restAgreement)
      restCap (by norm_num [R.a,R.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v])
      hrScaled hrestCap
  exact Nat.add_le_add heCard hrCard

theorem member_weight_bounds_of_rest
    {T S M : Nat}
    (Q : MvPolynomial (Fin 4) K)
    (ambient rest : Finset (MvPolynomial (Fin 4) K))
    (hambient : ambient⊆positiveTFactors Q) (hrest : rest⊆ambient)
    (hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1]
      (∏ G∈rest,G)≤T)
    (hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1]
      (∏ G∈rest,G)≤S)
    (hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1]
      (∏ G∈rest,G)≤M)
    (F : ↥rest) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] F.1≤T ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] F.1≤S ∧
    MvPolynomial.weightedTotalDegree ![0,1,1,1] F.1≤M := by
  let P : MvPolynomial (Fin 4) K := ∏ G∈rest,G
  have hirr : ∀ G∈rest,Irreducible G := fun G hG =>
    (positiveTFactors_spec Q G (hambient (hrest hG))).1
  have hP : P≠0 := product_ne_zero rest id hirr
  have hdiv : F.1∣P := Finset.dvd_prod_of_mem id F.2
  exact ⟨(weightedTotalDegree_le_of_dvd ![0,0,0,1] F.1 P hdiv hP).trans hPT,
    (weightedTotalDegree_le_of_dvd ![0,0,1,1] F.1 P hdiv hP).trans hPRT,
    (weightedTotalDegree_le_of_dvd ![0,1,1,1] F.1 P hdiv hP).trans hPJ⟩

/-- Full semantic terminal closure for the `N=262144`, `W=133226` active
family.  The only unclosed input is the exact three-way helper-producing
step.  All four terminal counts and both shared-budget arms are internal. -/
theorem extended_lshape_active_card_le_of_joint_step
    [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hQT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hQRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hQJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744)
    (Gamma : Finset (Polynomial K)) (nodeSet : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodeSet) (hnodes : nodeSet.card=R.n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤R.w)
    (hagrees : ∀ P∈Gamma,
      R.a≤(nodeSet.filter fun i => P.eval (x i)=u i).card)
    (hcommon : HereditaryCommonCap Gamma nodeSet x u R.v R.small)
    (hstep : ∀ T, T⊆positiveTFactors Q → T.Nonempty →
      ExtendedHeavy id T →
      ∃ F∈T,∃ H,JointRegularHelper nodeSet x u F H) :
    (∑ F∈positiveTFactors Q,(regularFamily F Gamma).card)≤
      247945303343219481 := by
  let ambient := positiveTFactors Q
  let count : MvPolynomial (Fin 4) K→Nat :=
    fun F => (regularFamily F Gamma).card
  obtain ⟨exited,rest,hrest,hEx,hdisjoint,hunion,hterminal,hcert⟩ :=
    extended_terminal_partition id ambient
      (fun F => ∃ H,JointRegularHelper nodeSet x u F H) hstep
  subst exited
  have hambient : ambient⊆positiveTFactors Q := by simp [ambient]
  have hExit : ∀ F : ↥(ambient\rest),count F.1*(R.a-R.v)≤
      (R.n-R.v)*flagMixed (factorFlag F.1) R.helperFlag
        R.primaryAgreement := by
    intro F
    obtain ⟨H,hH⟩ := hcert F.1 F.2
    have hmem : F.1∈positiveTFactors Q := hambient (Finset.mem_sdiff.mp F.2).1
    obtain ⟨hFirred,hFdiv,hFpos⟩ := positiveTFactors_spec Q F.1 hmem
    have hdvd (weights : Fin 4→Nat) :
        MvPolynomial.weightedTotalDegree weights F.1≤
          MvPolynomial.weightedTotalDegree weights Q :=
      weightedTotalDegree_le_of_dvd weights F.1 Q hFdiv hQ
    exact joint_regularHelper_factor_scaled_le nodeSet x u hnodes F.1 H
      hFpos ((hdvd ![0,0,0,1]).trans hQT)
      ((hdvd ![0,0,1,1]).trans hQRT)
      ((hdvd ![0,1,1,1]).trans hQJ) hH Gamma hdegree hagrees hcommon
  have hsplit : (∑ F∈positiveTFactors Q,count F)=
      (∑ F∈ambient\rest,count F)+(∑ F∈rest,count F) := by
    simpa [ambient] using (sum_exited_add_rest ambient rest hrest count).symm
  rw [hsplit]
  rcases hterminal with hA | hB | hDerivative | hJet
  · have hCheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
        (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armAAgreement
          R.armAAgreement := by
      intro F
      let P : MvPolynomial (Fin 4) K := ∏ G∈rest,G
      have hnested := derivative_nested_bounds P
      have hhalf : derivativeDegree P/2≤55/2 := Nat.div_le_div_right hA.2
      have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
        hnested.1.trans (by norm_num at hhalf ⊢; exact hhalf)
      have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤55 :=
        hnested.2.trans hA.2
      have hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤211 := by
        simpa [P,jetDegree,jetWeights] using hA.1
      obtain ⟨hFT,hFRT,hFJ⟩ := member_weight_bounds_of_rest Q ambient
        rest hambient hrest hPT hPRT hPJ F
      have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
      have hFirred := (positiveTFactors_spec Q F.1 (hambient (hrest F.2))).1
      exact individual_armA_scaled F.1 hFirred.ne_zero hFT hFRT hFJ
        (regularFamily F.1 Gamma) nodeSet x u hinj hnodes
        (fun P hP => hdegree P (hsub hP))
        (fun P hP => (Finset.mem_filter.mp hP).2.1)
        (fun P hP => (Finset.mem_filter.mp hP).2.2)
        (fun P hP => hagrees P (hsub hP))
        (hereditaryCommonCap_mono hcommon hsub)
    have hs := armA_partition_counts_scaled Q hQ hQT hQRT hQJ ambient
      rest hambient hrest hA.1 hA.2 count hExit hCheap
    apply WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
      _ ((R.a-R.v)^2)
      (R.commonNumerator R.armAFlag R.armAExitFlag R.armAAgreement)
      247945303343219481
      (by norm_num [R.a,R.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v]) hs
    norm_num [R.commonNumerator,R.armAFlag,R.armAExitFlag,R.armAAgreement,
      R.helperFlag,R.primaryAgreement,R.n,R.a,R.v,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.commonNumerator,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAExitFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armAAgreement,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
      honestReducedAgreementFlag,flagMixed]
  · have hCheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
        (R.n-R.v)^2*flagMixed (factorFlag F.1) R.armBAgreement
          R.armBAgreement := by
      intro F
      let P : MvPolynomial (Fin 4) K := ∏ G∈rest,G
      have hnested := derivative_nested_bounds P
      have hhalf : derivativeDegree P/2≤54/2 := Nat.div_le_div_right hB.2
      have hPT : MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 :=
        hnested.1.trans (by norm_num at hhalf ⊢; exact hhalf)
      have hPRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤54 :=
        hnested.2.trans hB.2
      have hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤212 := by
        simpa [P,jetDegree,jetWeights] using hB.1
      obtain ⟨hFT,hFRT,hFJ⟩ := member_weight_bounds_of_rest Q ambient
        rest hambient hrest hPT hPRT hPJ F
      have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
      have hFirred := (positiveTFactors_spec Q F.1 (hambient (hrest F.2))).1
      exact individual_armB_scaled F.1 hFirred.ne_zero hFT hFRT hFJ
        (regularFamily F.1 Gamma) nodeSet x u hinj hnodes
        (fun P hP => hdegree P (hsub hP))
        (fun P hP => (Finset.mem_filter.mp hP).2.1)
        (fun P hP => (Finset.mem_filter.mp hP).2.2)
        (fun P hP => hagrees P (hsub hP))
        (hereditaryCommonCap_mono hcommon hsub)
    have hs := armB_partition_counts_scaled Q hQ hQT hQRT hQJ ambient
      rest hambient hrest hB.1 hB.2 count hExit hCheap
    apply WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
      _ ((R.a-R.v)^2)
      (R.commonNumerator R.armBFlag R.armBExitFlag R.armBAgreement)
      247945303343219481
      (by norm_num [R.a,R.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v]) hs
    norm_num [R.commonNumerator,R.armBFlag,R.armBExitFlag,R.armBAgreement,
      R.helperFlag,R.primaryAgreement,R.n,R.a,R.v,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.commonNumerator,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBExitFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.armBAgreement,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
      WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
      honestReducedAgreementFlag,flagMixed]
  · let P : MvPolynomial (Fin 4) K := ∏ G∈rest,G
    have hirr : ∀ G∈rest,Irreducible G := fun G hG =>
      (positiveTFactors_spec Q G (hambient (hrest hG))).1
    have hP : P≠0 := product_ne_zero rest id hirr
    have hPdiv : P∣Q := positiveT_subset_product_dvd rest Q hQ
      (fun G hG => hambient (hrest hG))
    have hPJ0 : MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤744 :=
      (weightedTotalDegree_le_of_dvd ![0,1,1,1] P Q hPdiv hQ).trans hQJ
    have hPJjet : jetDegree P≤744 := by
      simpa [jetDegree,jetWeights] using hPJ0
    obtain ⟨hPT,hPRT,hPJjet'⟩ := derivative_skinny_nested_bounds P
      hPJjet hDerivative
    have hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤744 := by
      simpa [jetDegree,jetWeights] using hPJjet'
    have hCheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
        (R.n-R.v)^2*flagMixed (factorFlag F.1)
          R.derivativeSkinnyAgreement R.derivativeSkinnyAgreement := by
      intro F
      obtain ⟨hFT,hFRT,hFJ⟩ := member_weight_bounds_of_rest Q ambient
        rest hambient hrest hPT hPRT hPJ F
      have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
      exact individual_derivative_skinny_scaled F.1 (hirr F.1 F.2).ne_zero
        hFT hFRT hFJ (regularFamily F.1 Gamma) nodeSet x u hinj hnodes
        (fun P hP => hdegree P (hsub hP))
        (fun P hP => (Finset.mem_filter.mp hP).2.1)
        (fun P hP => (Finset.mem_filter.mp hP).2.2)
        (fun P hP => hagrees P (hsub hP))
        (hereditaryCommonCap_mono hcommon hsub)
    have hc := skinny_partition_counts_le Q hQ hQT hQRT hQJ ambient rest
      hambient hrest R.derivativeSkinnyFlag R.derivativeSkinnyAgreement
      (by simpa [R.derivativeSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyFlag]
        using hPT)
      (by simpa [R.derivativeSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyFlag]
        using hPRT)
      (by simpa [R.derivativeSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyFlag]
        using hPJ)
      count hExit hCheap 788423032100813 20931209660456200
      (by norm_num [R.n,R.a,R.v,R.primaryFlag,R.helperFlag,R.primaryAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag,flagMixed])
      (by norm_num [R.n,R.a,R.v,R.derivativeSkinnyFlag,
        R.derivativeSkinnyAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.derivativeSkinnyAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag,flagMixed])
    have hc' : (∑ F∈ambient\rest,count F)+(∑ F∈rest,count F)≤
        788423032100813+20931209660456200 := by
      simpa only [Finset.sum_coe_sort] using hc
    exact hc'.trans (by norm_num)
  · let P : MvPolynomial (Fin 4) K := ∏ G∈rest,G
    have hirr : ∀ G∈rest,Irreducible G := fun G hG =>
      (positiveTFactors_spec Q G (hambient (hrest hG))).1
    have hP : P≠0 := product_ne_zero rest id hirr
    obtain ⟨hPT,hPRT,hPJjet⟩ := jet_skinny_nested_bounds P hJet
    have hPJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤33 := by
      simpa [jetDegree,jetWeights] using hPJjet
    have hCheap : ∀ F : ↥rest,count F.1*(R.a-R.v)^2≤
        (R.n-R.v)^2*flagMixed (factorFlag F.1)
          R.jetSkinnyAgreement R.jetSkinnyAgreement := by
      intro F
      obtain ⟨hFT,hFRT,hFJ⟩ := member_weight_bounds_of_rest Q ambient
        rest hambient hrest hPT hPRT hPJ F
      have hsub : regularFamily F.1 Gamma⊆Gamma := Finset.filter_subset _ _
      exact individual_jet_skinny_scaled F.1 (hirr F.1 F.2).ne_zero
        hFT hFRT hFJ (regularFamily F.1 Gamma) nodeSet x u hinj hnodes
        (fun P hP => hdegree P (hsub hP))
        (fun P hP => (Finset.mem_filter.mp hP).2.1)
        (fun P hP => (Finset.mem_filter.mp hP).2.2)
        (fun P hP => hagrees P (hsub hP))
        (hereditaryCommonCap_mono hcommon hsub)
    have hc := skinny_partition_counts_le Q hQ hQT hQRT hQJ ambient rest
      hambient hrest R.jetSkinnyFlag R.jetSkinnyAgreement
      (by simpa [R.jetSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyFlag]
        using hPT)
      (by simpa [R.jetSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyFlag]
        using hPRT)
      (by simpa [R.jetSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyFlag]
        using hPJ)
      count hExit hCheap 788423032100813 7188982987108962
      (by norm_num [R.n,R.a,R.v,R.primaryFlag,R.helperFlag,R.primaryAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag,flagMixed])
      (by norm_num [R.n,R.a,R.v,R.jetSkinnyFlag,R.jetSkinnyAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyFlag,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.jetSkinnyAgreement,
        WeightedIdentityExtendedLShapeArithmeticW1332266900.w,
        honestReducedAgreementFlag,flagMixed])
    have hc' : (∑ F∈ambient\rest,count F)+(∑ F∈rest,count F)≤
        788423032100813+7188982987108962 := by
      simpa only [Finset.sum_coe_sort] using hc
    exact hc'.trans (by norm_num)

#print axioms extended_terminal_partition
#print axioms individual_derivative_skinny_scaled
#print axioms individual_jet_skinny_scaled
#print axioms joint_regularHelper_factor_scaled_le
#print axioms armA_partition_counts_scaled
#print axioms skinny_partition_counts_le
#print axioms extended_lshape_active_card_le_of_joint_step

end
end ProximityPrize.SubmissionLower.WeightedIdentityExtendedLShapeIntegrationW1332266900
