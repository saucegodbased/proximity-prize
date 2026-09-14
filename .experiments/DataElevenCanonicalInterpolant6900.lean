import DataElevenHighEClosedFrontier6900

/-! A small import-graph adapter exposing the canonical all-node Lagrange
interpolant on the DataEleven branch. -/

namespace ProximityPrize.SubmissionLower.DataElevenCanonicalInterpolant6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

def canonicalReceivedInterpolant
    (u : Index → ExtensionField) : ExtensionField[X] :=
  Lagrange.interpolate Finset.univ IRSProfile.domain u

theorem canonicalReceivedInterpolant_eval
    (u : Index → ExtensionField) (i : Index) :
    (canonicalReceivedInterpolant u).eval (IRSProfile.domain i) = u i := by
  exact Lagrange.eval_interpolate_at_node u IRSProfile.domain.injective.injOn
    (Finset.mem_univ i)

#print axioms canonicalReceivedInterpolant_eval

end
end ProximityPrize.SubmissionLower.DataElevenCanonicalInterpolant6900
