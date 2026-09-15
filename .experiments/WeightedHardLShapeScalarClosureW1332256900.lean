import WeightedHardLShapeClosedW1332256900
import Order2SeedlessCleanupAggregate6900
import ScalarShortenedJohnsonCommonCap6900
import WeightedIdentityOneExceptionLedgerW1332256900

/-!
# Scalar closure of the W=133225 hard identity branch

This module starts immediately above the closed hard-L active-factor bound.
It ports the accepted W133224 nonactive decomposition to the exact
`(n,w,a;M,D,T)=(262143,133225,180413;740,244,122)` profile, derives the
hereditary common-node premise from shortened Johnson, and performs the final
scalar arithmetic.  Construction of the primary polynomial is intentionally
outside this theorem.
-/
namespace ProximityPrize.SubmissionLower.WeightedHardLShapeScalarClosureW1332256900

open scoped BigOperators
open RCN081 RCN135 RCN290 RCN293
open Order2SourceBasisScaffold Order2SourceSpecializationScaffold
open Order2ValueYCapAllFactorScaffold
open Order2SeedlessCleanupAggregate6900
open Order2HereditaryCommonNodeFlagCount6900
open ScalarShortenedJohnsonCommonCap6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section

variable {K : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

def n : Nat := 262143
def w : Nat := 133225
def a : Nat := 180413
def v : Nat := 68763
def small : Nat := 1453806
def prime : Nat := 2130706433

def firstOrderMixedCost (yCap rCap : Nat) : Nat :=
  (1+2*w*yCap)*rCap+w*(2*rCap-1)*yCap

def firstOrderRegularNumerator (yCap rCap : Nat) : Nat :=
  (n-w)*firstOrderMixedCost yCap rCap

def positiveAuxY : Nat := (2*122-1)*740
def positiveAuxR : Nat := (2*122-1)*244
def positiveRegularCap : Nat := 15522439326103910
def positiveSingularCap : Nat := 21323595060
def tFreeRegularCap : Nat := 262605642924
def tFreeSingularCap : Nat := 360380

def cleanupCap : Nat :=
  WeightedIdentityOneExceptionLedgerW1332256900.minimumPrimaryCleanupCap

theorem cleanup_cap_exact : cleanupCap=15522723255702274 := by
  exact WeightedIdentityOneExceptionLedgerW1332256900.joint_cap_boundary_ledger_exact.1

theorem cleanup_component_arithmetic :
    positiveAuxY=179820 ∧ positiveAuxR=59292 ∧
    firstOrderRegularNumerator positiveAuxY positiveAuxR≤
      positiveRegularCap*(a-w) ∧
    firstOrderRegularNumerator 740 244≤tFreeRegularCap*(a-w) ∧
    positiveRegularCap+positiveSingularCap+
      tFreeRegularCap+tFreeSingularCap=cleanupCap := by
  rw [cleanup_cap_exact]
  norm_num [positiveAuxY,positiveAuxR,firstOrderRegularNumerator,
    firstOrderMixedCost,positiveRegularCap,positiveSingularCap,
    tFreeRegularCap,tFreeSingularCap,n,w,a]

/-- Fixed-cardinality version of the generic seedless cleanup row. -/
theorem seedless_row_card_le {I : Type} [Fintype I]
    [CharP K 2130706433]
    (J : MvPolynomial (Fin 4) K) (hJ : J≠0) (yCap R cap : Nat)
    (hYchar : yCap<prime) (hRchar : R<prime) (hRp : 1≤R)
    (hY : J.degreeOf 1≤yCap) (hR : J.degreeOf 2≤R)
    (hT : J.degreeOf 3=0)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P J=0)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcap : firstOrderRegularNumerator yCap R≤cap*(a-w)) :
    Gamma.card≤cap+(2*R-1)*yCap := by
  apply all_card_le J hJ w a prime yCap R cap
    (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,a])
    hYchar hRchar hRp hY hR hT Gamma nodes x u hinj
    (by rw [hn]; norm_num [n,a]) hdegree hsolution hagreement
  simpa only [hn,firstOrderRegularNumerator,firstOrderMixedCost,n,w,a] using
    hcap

def tFreeSolutions (Q : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) : Finset (Polynomial K) :=
  Gamma.filter fun P => jetSpecialization2 P (tFreeProduct Q)=0

/-- Exact W133225 semantic cleanup.  The T-free family already includes its
Y-only subcase, so the output is the ledger's minimum cleanup cap with no
extra additive charge. -/
theorem actual_nonactive_bound {I : Type} [Fintype I]
    [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hY : Q.degreeOf 1≤740) (hR : Q.degreeOf 2≤244)
    (hT : Q.degreeOf 3≤122)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    Gamma.card≤(activeTRegularPolynomials Q Gamma).card+cleanupCap := by
  classical
  let S := positiveTSingularAuxiliary Q
  have hSne : S≠0 := positiveTSingularAuxiliary_nonzero Q hQ 2130706433
    (hT.trans_lt (by norm_num [prime]))
  have hST : S.degreeOf (3 : Fin 4)=0 :=
    positiveTSingularAuxiliary_T_degree Q
  have hSY : S.degreeOf (1 : Fin 4)≤positiveAuxY := by
    have h := positiveTSingularAuxiliary_weight_le Q hQ
      (Pi.single (1 : Fin 4) 1) 122 (by norm_num) hT
    simpa only [MvPolynomial.weightedTotalDegree_piSingle,positiveAuxY] using
      h.trans (Nat.mul_le_mul_left (2*122-1) (by
        simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hY))
  have hSR : S.degreeOf (2 : Fin 4)≤positiveAuxR := by
    have h := positiveTSingularAuxiliary_weight_le Q hQ
      (Pi.single (2 : Fin 4) 1) 122 (by norm_num) hT
    simpa only [MvPolynomial.weightedTotalDegree_piSingle,positiveAuxR] using
      h.trans (Nat.mul_le_mul_left (2*122-1) (by
        simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hR))
  have hpositive :
      (positiveTSingularPolynomials Q Gamma).card≤
        positiveRegularCap+positiveSingularCap := by
    apply seedless_row_card_le S hSne positiveAuxY positiveAuxR
      positiveRegularCap
      (by norm_num [positiveAuxY,prime])
      (by norm_num [positiveAuxR,prime])
      (by norm_num [positiveAuxR]) hSY hSR hST
      (positiveTSingularPolynomials Q Gamma) nodes x u hinj hn
      (fun P hP => hdegree P (Finset.mem_filter.mp hP).1)
      (fun P hP => (Finset.mem_filter.mp hP).2)
      (fun P hP => hagreement P (Finset.mem_filter.mp hP).1)
    exact cleanup_component_arithmetic.2.2.1
  have hJY : (tFreeProduct Q).degreeOf (1 : Fin 4)≤740 :=
    (degreeOf_le_of_dvd 1 (tFreeProduct Q) Q (tFreeProduct_dvd Q hQ) hQ).trans hY
  have hJR : (tFreeProduct Q).degreeOf (2 : Fin 4)≤244 :=
    (degreeOf_le_of_dvd 2 (tFreeProduct Q) Q (tFreeProduct_dvd Q hQ) hQ).trans hR
  have htfree : (tFreeSolutions Q Gamma).card≤
      tFreeRegularCap+tFreeSingularCap := by
    apply seedless_row_card_le (tFreeProduct Q) (tFreeProduct_nonzero Q)
      740 244 tFreeRegularCap
      (by norm_num [prime]) (by norm_num [prime]) (by norm_num)
      hJY hJR (tFreeProduct_T_degree Q)
      (tFreeSolutions Q Gamma) nodes x u hinj hn
      (fun P hP => hdegree P (Finset.mem_filter.mp hP).1)
      (fun P hP => (Finset.mem_filter.mp hP).2)
      (fun P hP => hagreement P (Finset.mem_filter.mp hP).1)
    exact cleanup_component_arithmetic.2.2.2.1
  have hcover : Gamma⊆activeTRegularPolynomials Q Gamma ∪
      (positiveTSingularPolynomials Q Gamma ∪ tFreeSolutions Q Gamma) := by
    intro P hP
    obtain hreg | hsing | hfree :=
      jet_zero_regular_or_positiveT_singular_or_tFree Q hQ P (hsolution P hP)
    · obtain ⟨F,hF,_,_,_,hz,hr⟩ := hreg
      exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hP,F,hF,hz,hr⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hP,hsing⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hP,hfree⟩))
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le (activeTRegularPolynomials Q Gamma)
    (positiveTSingularPolynomials Q Gamma ∪ tFreeSolutions Q Gamma)
  have h2 := Finset.card_union_le (positiveTSingularPolynomials Q Gamma)
    (tFreeSolutions Q Gamma)
  have hnumbers : positiveRegularCap+positiveSingularCap+
      tFreeRegularCap+tFreeSingularCap≤cleanupCap := by
    exact cleanup_component_arithmetic.2.2.2.2.le
  omega

/-- Nested weighted caps imply the coordinate caps used by cleanup. -/
theorem primary_coordinate_caps (Q : MvPolynomial (Fin 4) K)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740) :
    Q.degreeOf 1≤740 ∧ Q.degreeOf 2≤244 ∧ Q.degreeOf 3≤122 := by
  refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
    MvPolynomial.degreeOf_le_iff.mpr ?_,MvPolynomial.degreeOf_le_iff.mpr ?_⟩
  · intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree
      (![0,1,1,1] : Fin 4→Nat) he).trans hJ
    rw [weight_fin4] at hw
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at hw
    omega
  · intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree
      (![0,0,1,1] : Fin 4→Nat) he).trans hRT
    rw [weight_fin4] at hw
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at hw
    omega
  · intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree
      (![0,0,0,1] : Fin 4→Nat) he).trans hT
    rw [weight_fin4] at hw
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at hw
    omega

/-- The common-node hypothesis of the active theorem is automatic at the
exact hard-branch cardinality. -/
theorem hard_hereditary_common_cap {I : Type}
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    HereditaryCommonCap Gamma nodes x u v small := by
  intro S hS hlarge
  apply scalar_hereditary_common_nodes_card_le Gamma nodes x u hinj
    w a small v
  · norm_num [w,a]
  · rw [hn]; norm_num [n,a]
  · norm_num [v,w]
  · rw [hn]
    simpa only [n,w,a,v,small,
      WeightedIdentityOneExceptionLedgerW1332256900.n,
      WeightedIdentityOneExceptionLedgerW1332256900.w,
      WeightedIdentityOneExceptionLedgerW1332256900.a,
      WeightedIdentityOneExceptionLedgerW1332256900.v,
      WeightedIdentityOneExceptionLedgerW1332256900.small] using
      WeightedIdentityOneExceptionLedgerW1332256900.one_exception_Johnson_gate
  · exact hdegree
  · exact hagreement
  · exact hS
  · exact hlarge

/-- Closed hard-active count converted from its scaled form to an integer
cardinality cap. -/
theorem activeTRegular_card_le_joint {I : Type}
    [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    (activeTRegularPolynomials Q Gamma).card≤247924633751427236 := by
  have hcommon := hard_hereditary_common_cap Gamma nodes x u hinj hn
    hdegree hagreement
  have hactive :=
    WeightedHardLShapeClosedW1332256900.hard_lshape_active_scaled
      Q hQ hT hRT hJ Gamma nodes x u hinj
      (by simpa only [n,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n] using hn)
      hdegree hagreement hcommon
  have hcover : activeTRegularPolynomials Q Gamma⊆
      (positiveTFactors Q).biUnion
        (fun F =>
          WeightedIdentityHardLShapeIntegrationW1332256900.regularFamily
            F Gamma) := by
    intro P hP
    obtain ⟨hPG,F,hF,hzero,hreg⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_biUnion.mpr
      ⟨F,hF,Finset.mem_filter.mpr ⟨hPG,hzero,hreg⟩⟩
  have hcard : (activeTRegularPolynomials Q Gamma).card≤
      ∑ F∈positiveTFactors Q,
        (WeightedIdentityHardLShapeIntegrationW1332256900.regularFamily
          F Gamma).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hscaled := (Nat.mul_le_mul_right ((a-v)^2) hcard).trans hactive
  apply WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
    (activeTRegularPolynomials Q Gamma).card ((a-v)^2)
    (RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement)
    247924633751427236
  · norm_num [a,v]
  · exact hscaled
  · norm_num [a,v,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement,
      RCN095.flagMixed]

/-- Exact full-family bound in the hard W133225 branch. -/
theorem hard_scalar_card_le {I : Type} [Fintype I]
    [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    Gamma.card≤263447357007129510 := by
  obtain ⟨hY,hR,hTcoord⟩ := primary_coordinate_caps Q hT hRT hJ
  have hcleanup := actual_nonactive_bound Q hQ hY hR hTcoord Gamma
    nodes x u hinj hn hdegree hsolution hagreement
  have hactive := activeTRegular_card_le_joint Q hQ hT hRT hJ Gamma
    nodes x u hinj hn hdegree hagreement
  have hce := cleanup_cap_exact
  omega

theorem hard_scalar_card_lt_coreFloor {I : Type} [Fintype I]
    [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    Gamma.card<
      RootWeightedIdentityCoupledBudgetArithmeticW1332256900.coreFloor := by
  exact (hard_scalar_card_le Q hQ hT hRT hJ Gamma nodes x u hinj hn
    hdegree hsolution hagreement).trans_lt (by
      norm_num [RootWeightedIdentityCoupledBudgetArithmeticW1332256900.coreFloor])

/-- Contradiction-shaped wrapper for the surrounding hard-branch split. -/
theorem hard_scalar_coreFloor_contradiction {I : Type} [Fintype I]
    [CharP K 2130706433]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤740)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I→K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0)
    (hagreement : ∀ P∈Gamma,
      a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hlarge : RootWeightedIdentityCoupledBudgetArithmeticW1332256900.coreFloor≤
      Gamma.card) : False := by
  have hsmall := hard_scalar_card_lt_coreFloor Q hQ hT hRT hJ Gamma
    nodes x u hinj hn hdegree hsolution hagreement
  omega

#print axioms actual_nonactive_bound
#print axioms hard_hereditary_common_cap
#print axioms activeTRegular_card_le_joint
#print axioms hard_scalar_card_le
#print axioms hard_scalar_card_lt_coreFloor
#print axioms hard_scalar_coreFloor_contradiction

end
end ProximityPrize.SubmissionLower.WeightedHardLShapeScalarClosureW1332256900
