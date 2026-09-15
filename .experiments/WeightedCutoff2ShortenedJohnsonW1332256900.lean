import ScalarShortenedJohnsonCommonCap6900
import Order2HereditaryCommonNodeFlagCount6900
import WeightedCutoff2RepresentativeLedgerW1332256900

/-! Shortened-Johnson specialization, monotone for every node type of card at most `262142`. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2ShortenedJohnsonW1332256900

open Polynomial ScalarShortenedJohnsonCommonCap6900
open Order2HereditaryCommonNodeFlagCount6900
open WeightedCutoff2RepresentativeLedgerW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
noncomputable section

variable {K I : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem scalar_hereditary_common_nodes_card_le_68759
    (Gamma : Finset K[X]) (nodes : Finset I) (node centre : I→K)
    (hinj : Set.InjOn node nodes) (hn : nodes.card≤n) (hAn : a≤nodes.card)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hagrees : ∀ P∈Gamma,a≤
      (nodes.filter (fun i => P.eval (node i)=centre i)).card) :
    HereditaryCommonCap Gamma nodes node centre v small := by
  intro S hS hlarge
  apply scalar_hereditary_common_nodes_card_le Gamma nodes node centre hinj
    w a small v
  · exact shortened_Johnson_gate.2.2.1
  · exact hAn
  · exact shortened_Johnson_gate.2.1
  · have hnv : nodes.card-(v+1)≤n-(v+1) := Nat.sub_le_sub_right hn _
    have hnw : nodes.card-w≤n-w := Nat.sub_le_sub_right hn _
    have hleft : (nodes.card-(v+1))*(nodes.card-w)≤
        (n-(v+1))*(n-w) := Nat.mul_le_mul hnv hnw
    have hprod : (nodes.card-(v+1))*(w-(v+1))≤
        (n-(v+1))*(w-(v+1)) := Nat.mul_le_mul_right _ hnv
    have hright : (small+1)*((a-(v+1))^2-(n-(v+1))*(w-(v+1)))≤
        (small+1)*((a-(v+1))^2-(nodes.card-(v+1))*(w-(v+1))) :=
      Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hprod _)
    exact hleft.trans_lt (shortened_Johnson_gate.1.trans_le hright)
  · exact hdegree
  · exact hagrees
  · exact hS
  · exact hlarge

end
end ProximityPrize.SubmissionLower.WeightedCutoff2ShortenedJohnsonW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ShortenedJohnsonW1332256900.scalar_hereditary_common_nodes_card_le_68759
