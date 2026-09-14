import M69DataElevenNoLeafEndpointBridge6900
import Order2ProtocolBadFamily6900

/-!
# Full endpoint composition check for the m69 no-leaf interface

This deliberately adds no mathematics.  It checks in one Lean environment
that the exact universal no-leaf proposition isolated by the DataEleven route
feeds the existing score-6900 protocol wrapper without an unstated adapter.
-/

namespace ProximityPrize.SubmissionLower.M69DataElevenNoLeafProtocol6900

open ProximityPrize.Benchmark
open M69DataElevenNoLeafEndpointBridge6900
open Order2ProtocolBadFamily6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The complete checked handoff from the one remaining universal source-side
premise to the exact benchmark claim. -/
theorem protocolClaim6900_of_noDataElevenHighEClosedLeaf
    (hno : NoDataElevenHighEClosedLeaf6900) :
    ProtocolClaim 6900 10461695 33554432 := by
  apply protocolClaim6900_of_bad_family
  exact targetBadFamilyBound_of_noDataElevenHighEClosedLeaf hno

#print axioms protocolClaim6900_of_noDataElevenHighEClosedLeaf

end
end ProximityPrize.SubmissionLower.M69DataElevenNoLeafProtocol6900
