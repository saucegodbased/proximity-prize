import ScalarShortenedJohnsonCommonCap6900
import WeightedRepresentativeCountLedgerW1332216900

/-! Consumer-facing shortened-Johnson specialization for the W=133221
profile.  The threshold is the literal `q=2458014` used by the representative
ledger, and the hereditary common-node cap is `v=68740`. -/
namespace ProximityPrize.SubmissionLower.WeightedShortenedJohnsonW1332216900

open Polynomial
open ScalarShortenedJohnsonCommonCap6900
open WeightedRepresentativeCountLedgerW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
noncomputable section

variable {K I : Type*} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Any subfamily strictly larger than `2458014` has at most `68740` common
agreement nodes.  This is a direct specialization of the generic hereditary
shortened-Johnson theorem, with no quotient or surrogate family. -/
theorem scalar_hereditary_common_nodes_card_le_68757
    (Gamma : Finset K[X]) (nodes : Finset I) (node centre : I→K)
    (hinj : Set.InjOn node nodes) (hn : nodes.card=262144)
    (hdegree : ∀ P∈Gamma,P.natDegree≤133221)
    (hagrees : ∀ P∈Gamma,180413≤
      (nodes.filter (fun i => P.eval (node i)=centre i)).card)
    (S : Finset K[X]) (hS : S⊆Gamma) (hlarge : 2458014<S.card) :
    (nodes.filter (fun i => ∀ P∈S,P.eval (node i)=centre i)).card≤68740 := by
  apply scalar_hereditary_common_nodes_card_le Gamma nodes node centre hinj
    133221 180413 2458014 68740
  · exact shortened_Johnson_gate.2.2.1
  · rw [hn]
    exact shortened_Johnson_gate.2.2.2
  · exact shortened_Johnson_gate.2.1
  · rw [hn]
    exact shortened_Johnson_gate.1
  · exact hdegree
  · exact hagrees
  · exact hS
  · exact hlarge

/-- The three absorption inequalities expected by the existing active-count
consumers, with the same `q` and common-node cap. -/
theorem q1453806_absorption_gates :
    2458014*(180413-68740)≤(262144-68740)*cheapAgreement.all ∧
    2458014*(180413-68740)^2≤
      (262144-68740)^2*cheapAgreement.all^2 ∧
    2458014*(180413-68740)≤(262144-68740)*primaryAgreement.all := by
  simpa [n,v,small,a] using small_absorption_gates

end
end ProximityPrize.SubmissionLower.WeightedShortenedJohnsonW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedShortenedJohnsonW1332216900.scalar_hereditary_common_nodes_card_le_68757
#print axioms ProximityPrize.SubmissionLower.WeightedShortenedJohnsonW1332216900.q1453806_absorption_gates
