import WeightedPrimary550UniversalW1332266900
import WeightedExtendedLShapeScalarClosureW1332266900

/-! End-to-end hard endpoint: construct the primary source and feed it into
the closed W=133226 scalar contradiction. -/
namespace ProximityPrize.SubmissionLower.WeightedExtendedEndpointClosedW1332266900

open Order2SourceBasisScaffold
open Order2ValueYCapAllFactorScaffold (jetSpecialization2)
open WeightedSourceIndex6900
open WeightedExtendedLShapeScalarClosureW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The nested global coefficient box gives the three weighted caps consumed
by the hard L-shaped factor theorem. -/
theorem primary_source_weighted_caps {K : Type*} [Field K]
    (Q : MvPolynomial (Fin 4) K)
    (hbox : Q∈globalOrder2CoefficientBox K 99227150 133226 744 244 122) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤122 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤244 ∧
    MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤744 := by
  have hsupport : ∀ d∈Q.support,
      d 1+d 2+d 3≤744 ∧ d 2+d 3≤244 ∧ d 3≤122 ∧
      d 0+133226*d 1+133225*d 2+133224*d 3<99227150 := hbox
  refine ⟨?_,?_,?_⟩
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 122).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).2.2.1
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 244).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).2.1
  · apply (RCN081.weightedTotalDegree_le_iff _ Q 744).mpr
    intro d hd
    rw [RCN081.weight_fin4]
    simpa using (hsupport d hd).1

/-- Fully semantic hard-branch contradiction at the exact 133226 endpoint.
The primary polynomial is constructed internally from the received word. -/
theorem hard_endpoint_coreFloor_contradiction
    {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
    (nodes received : I → K) (hinj : Function.Injective nodes)
    (hI : Fintype.card I=262144) (Gamma : Finset (Polynomial K))
    (hdegree : ∀ P∈Gamma,P.natDegree≤133226)
    (hagreement : ∀ P∈Gamma,180413≤
      (Finset.univ.filter fun i => P.eval (nodes i)=received i).card)
    (hlarge :
      WeightedIdentityExtendedLShapeArithmeticW1332266900.coreFloor≤
        Gamma.card) : False := by
  have h2 : (2 : K)≠0 :=
    CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (by norm_num)
  obtain ⟨Q,hQ,hweighted,hbox,hvanish⟩ :=
    WeightedPrimary550UniversalW1332266900.primary_universal_vanishing
      nodes received hinj (by omega) h2
  have hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0 := by
    intro P hP
    apply hvanish P
      (Finset.univ.filter fun i => P.eval (nodes i)=received i)
      (hdegree P hP) (hagreement P hP)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨hT,hRT,hJ⟩ := primary_source_weighted_caps Q hbox
  apply hard_scalar_coreFloor_contradiction Q hQ hT hRT hJ Gamma
    Finset.univ nodes received hinj.injOn
  · simpa only [Finset.card_univ,hI,n]
  · intro P hP
    simpa only [w] using hdegree P hP
  · exact hsolution
  · intro P hP
    simpa only [a] using hagreement P hP
  · exact hlarge

#print axioms primary_source_weighted_caps
#print axioms hard_endpoint_coreFloor_contradiction

end
end ProximityPrize.SubmissionLower.WeightedExtendedEndpointClosedW1332266900
