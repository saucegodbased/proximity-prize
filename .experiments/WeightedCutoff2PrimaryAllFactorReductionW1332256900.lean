import WeightedCutoff2PrimaryUniversalW1332256900
import WeightedCutoff2NonactiveCleanupW1332256900

/-! Primary source plus semantic nonactive cleanup for the cutoff-two profile. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2PrimaryAllFactorReductionW1332256900

open Order2SourceBasisScaffold WeightedSourceIndex6900
open Order2ValueYCapAllFactorScaffold
open WeightedCutoff2RepresentativeLedgerW1332256900
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section
abbrev Poly4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem primary_source_coordinate_caps {K : Type*} [Field K] (Q : Poly4 K)
    (hbox : Q∈globalOrder2CoefficientBox K 98505498 133225 739 244 122) :
    Q.degreeOf 1≤739 ∧ Q.degreeOf 2≤244 ∧ Q.degreeOf 3≤122 := by
  have hsupport : ∀ d∈Q.support,
      d 1+d 2+d 3≤739 ∧ d 2+d 3≤244 ∧ d 3≤122 ∧
      d 0+133225*d 1+133224*d 2+133223*d 3<98505498 := hbox
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
    (hbox : Q∈globalOrder2CoefficientBox K 98505498 133225 739 244 122) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244 ∧
    MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤739 := by
  have hsupport : ∀ d∈Q.support,
      d 1+d 2+d 3≤739 ∧ d 2+d 3≤244 ∧ d 3≤122 ∧
      d 0+133225*d 1+133224*d 2+133223*d 3<98505498 := hbox
  refine ⟨?_,?_,?_⟩
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 122).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).2.2.1
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 244).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).2.1
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 739).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).1

theorem exists_primary_source_and_nonactive_bound
    {K I : Type} [Field K] [Fintype I] [CharP K prime]
    (nodes received : I → K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I≤n) (hAn : a≤Fintype.card I)
    (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagreement : ∀ P∈Gamma,a≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card) :
    ∃ Q : Poly4 K, Q≠0 ∧
      Q∈weightedCoefficientBox K 98505498 133225 244 ∧
      Q∈globalOrder2CoefficientBox K 98505498 133225 739 244 122 ∧
      (∀ P∈Gamma,jetSpecialization2 P Q=0) ∧
      Gamma.card≤(activeTRegularPolynomials Q Gamma).card+15501626357806302 := by
  have h2 : (2 : K)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num [prime])
  obtain ⟨Q,hQ,hweighted,hbox,hvanish⟩ :=
    WeightedCutoff2PrimaryUniversalW1332256900.primary_universal_vanishing
      nodes received hinj hI h2
  have hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0 := by
    intro P hP
    apply hvanish P
      (Finset.univ.filter fun i => P.eval (nodes i)=received i)
      (hdegree P hP) (hagreement P hP)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨hY,hR,hT⟩ := primary_source_coordinate_caps Q hbox
  refine ⟨Q,hQ,hweighted,hbox,hsolution,?_⟩
  exact WeightedCutoff2NonactiveCleanupW1332256900.actual_nonactive_bound Q hQ
    hY hR hT Gamma Finset.univ nodes received hinj.injOn
    (by simpa only [Finset.card_univ] using hI)
    (by simpa only [Finset.card_univ] using hAn)
    hdegree hsolution hagreement

end
end ProximityPrize.SubmissionLower.WeightedCutoff2PrimaryAllFactorReductionW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2PrimaryAllFactorReductionW1332256900.exists_primary_source_and_nonactive_bound
