import WeightedCutoff2SourcesW1332256900
import Order2SourceSpecializationScaffold

/-! The cutoff-two primary source vanishes on every `180413`-agreement polynomial. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2PrimaryUniversalW1332256900

open Order2SourceBasisScaffold
open Order2SourceSpecializationScaffold (localJetSpecialization2
  localJetSpecialization2_eq_zero_of_contact_and_degree
  localJetSpecialization2_natDegree_lt)
open WeightedSourceIndex6900 WeightedCutoff2SourcesW1332256900
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

theorem primary_universal_vanishing {K I : Type} [Field K] [Fintype I]
    (nodes values : I → K) (hinj : Function.Injective nodes)
    (hn : Fintype.card I≤262142) (h2 : (2 : K)≠0) :
    ∃ Q : Poly4 K, Q≠0 ∧ Q∈weightedCoefficientBox K 98505498 133225 244 ∧
      Q∈globalOrder2CoefficientBox K 98505498 133225 739 244 122 ∧
      ∀ (P : Polynomial K) (support : Finset I), P.natDegree≤133225 →
        180413≤support.card → (∀ i∈support,P.eval (nodes i)=values i) →
          localJetSpecialization2 P Q=0 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq I := Classical.decEq I
  obtain ⟨Q,hQ,hweighted,hcaps,hcontact⟩ :=
    primary_source_exists K I h2 nodes values hn
  refine ⟨Q,hQ,hweighted,hcaps,?_⟩
  intro P support hP hcard hvalues
  apply localJetSpecialization2_eq_zero_of_contact_and_degree
    Q P nodes values support 546 hinj.injOn h2
  · intro i hi
    exact hcontact i
  · exact hvalues
  · have hdegree := localJetSpecialization2_natDegree_lt
      98505498 133225 739 244 122 Q P (by norm_num) hcaps hP
    have hmany : 98505498≤546*support.card := by omega
    exact hdegree.trans_le hmany

end
end ProximityPrize.SubmissionLower.WeightedCutoff2PrimaryUniversalW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2PrimaryUniversalW1332256900.primary_universal_vanishing
