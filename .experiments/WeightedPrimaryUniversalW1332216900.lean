import WeightedFinitePrefixPrimarySourceW1332216900
import Order2SourceSpecializationScaffold

/-! The primary weighted source already vanishes on every polynomial with
the required number of agreements, not only in a formal contact target. -/
namespace ProximityPrize.SubmissionLower.WeightedPrimaryUniversalW1332216900
open Order2SourceBasisScaffold
open Order2SourceSpecializationScaffold (localJetSpecialization2
  localJetSpecialization2_eq_zero_of_contact_and_degree
  localJetSpecialization2_natDegree_lt)
open WeightedSourceIndex6900
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

theorem primary_universal_vanishing {K I : Type*} [Field K] [Fintype I]
    (nodes values : I → K) (hinj : Function.Injective nodes)
    (hn : Fintype.card I≤262144) (h2 : (2 : K)≠0) :
    ∃ Q : Poly4 K, Q≠0 ∧ Q∈weightedCoefficientBox K 96160129 133221 236 ∧
      Q∈globalOrder2CoefficientBox K 96160129 133221 721 236 118 ∧
      ∀ (P : Polynomial K) (support : Finset I), P.natDegree≤133221 →
        180413≤support.card → (∀ i∈support,P.eval (nodes i)=values i) →
          localJetSpecialization2 P Q=0 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq I := Classical.decEq I
  obtain ⟨Q,hQ,hweighted,hcaps,hcontact⟩ :=
    WeightedFinitePrefixPrimarySourceW1332216900.primary_source_exists K I h2 nodes values hn
  refine ⟨Q,hQ,hweighted,hcaps,?_⟩
  intro P support hP hcard hvalues
  apply localJetSpecialization2_eq_zero_of_contact_and_degree
    Q P nodes values support 533 hinj.injOn h2
  · intro i hi
    exact hcontact i
  · exact hvalues
  · have hdegree := localJetSpecialization2_natDegree_lt
      96160129 133221 721 236 118 Q P (by norm_num) hcaps hP
    have hmany : 96160129≤533*support.card := by omega
    exact hdegree.trans_le hmany

#print axioms primary_universal_vanishing
end
end ProximityPrize.SubmissionLower.WeightedPrimaryUniversalW1332216900
