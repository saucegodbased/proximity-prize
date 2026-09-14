import WeightedPrimaryUniversalW1332216900
import Order2WeightedNonactiveCleanupW1332216900

/-! The actual primary source and semantic nonactive cleanup, for any received
word. The remaining active count is explicit; no final scalar bound is claimed
by this reduction. -/
namespace ProximityPrize.SubmissionLower.WeightedPrimaryAllFactorReductionW1332216900
open Order2SourceBasisScaffold WeightedSourceIndex6900
open Order2ValueYCapAllFactorScaffold WeightedRepresentativeCountLedgerW1332216900
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section
abbrev Poly4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem primary_source_coordinate_caps {K : Type*} [Field K] (Q : Poly4 K)
    (hbox : Q∈globalOrder2CoefficientBox K 96160129 133221 721 236 118) :
    Q.degreeOf 1≤721 ∧ Q.degreeOf 2≤236 ∧ Q.degreeOf 3≤118 := by
  have hsupport : ∀ d∈Q.support,
      d 1+d 2+d 3≤721 ∧ d 2+d 3≤236 ∧ d 3≤118 ∧
      d 0+133221*d 1+133220*d 2+133219*d 3<96160129 := hbox
  refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
    MvPolynomial.degreeOf_le_iff.mpr ?_, MvPolynomial.degreeOf_le_iff.mpr ?_⟩
  · intro d hd
    have h := hsupport d hd
    omega
  · intro d hd
    have h := hsupport d hd
    omega
  · intro d hd
    exact (hsupport d hd).2.2.1

theorem primary_source_weighted_caps {K : Type*} [Field K] (Q : Poly4 K)
    (hbox : Q∈globalOrder2CoefficientBox K 96160129 133221 721 236 118) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤118 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤236 ∧
    MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤721 := by
  have hsupport : ∀ d∈Q.support,
      d 1+d 2+d 3≤721 ∧ d 2+d 3≤236 ∧ d 3≤118 ∧
      d 0+133221*d 1+133220*d 2+133219*d 3<96160129 := hbox
  refine ⟨?_,?_,?_⟩
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 118).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).2.2.1
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 236).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).2.1
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 721).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).1

theorem exists_primary_source_and_nonactive_bound
    {K I : Type} [Field K] [Fintype I] [CharP K prime]
    (nodes received : I → K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144) (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagreement : ∀ P∈Gamma,180413≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card) :
    ∃ Q : Poly4 K, Q≠0 ∧
      Q∈weightedCoefficientBox K 96160129 133221 236 ∧
      Q∈globalOrder2CoefficientBox K 96160129 133221 721 236 118 ∧
      (∀ P∈Gamma,jetSpecialization2 P Q=0) ∧
      Gamma.card≤(activeTRegularPolynomials Q Gamma).card+13679939831507851 := by
  have h2 : (2 : K)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num [prime])
  obtain ⟨Q,hQ,hweighted,hbox,hvanish⟩ :=
    WeightedPrimaryUniversalW1332216900.primary_universal_vanishing
      nodes received hinj (by omega) h2
  have hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0 := by
    intro P hP
    apply hvanish P
      (Finset.univ.filter fun i => P.eval (nodes i)=received i)
      (hdegree P hP) (hagreement P hP)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨hY,hR,hT⟩ := primary_source_coordinate_caps Q hbox
  refine ⟨Q,hQ,hweighted,hbox,hsolution,?_⟩
  exact Order2WeightedNonactiveCleanupW1332216900.actual_nonactive_bound Q hQ
    hY hR hT Gamma Finset.univ nodes received hinj.injOn
    (by simpa only [Finset.card_univ,hI,n])
    hdegree hsolution hagreement

#print axioms primary_source_coordinate_caps
#print axioms primary_source_weighted_caps
#print axioms exists_primary_source_and_nonactive_bound
end
end ProximityPrize.SubmissionLower.WeightedPrimaryAllFactorReductionW1332216900
