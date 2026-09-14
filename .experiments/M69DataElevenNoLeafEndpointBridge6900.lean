import DataElevenHighEClosedFrontier6900

/-!
# Exact endpoint bridge for the m69 DataEleven route

The active m69 source program is useful to the benchmark only if it rules out
the exact `DataElevenHighEClosedLeaf` produced by the universal bad-family
dichotomy.  This file exposes that single outgoing interface and connects it
to the already checked score-6900 endpoint.

It deliberately proves no source theorem: `NoDataElevenHighEClosedLeaf6900`
is the remaining premise.  Local prefix rank, individual residual membership,
or a fixed received word does not inhabit this universally quantified
predicate.
-/

namespace ProximityPrize.SubmissionLower.M69DataElevenNoLeafEndpointBridge6900

open ProximityPrize.Benchmark
open DataElevenHighEClosedFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- The exact source-facing proposition.  A proof may inspect every field of
the actual surviving leaf, but must work uniformly for every received pair,
selected family, and agreement-set family produced by the endpoint split. -/
def NoDataElevenHighEClosedLeaf6900 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
      (Gamma : Finset IRSProfile.Field)
      (agreement : IRSProfile.Field → Finset IRSProfile.Index)
      (selected : IRSProfile.Field → Polynomial IRSProfile.Field),
    DataElevenHighEClosedLeaf U Gamma agreement selected → False

/-- This is definitionally the numerical selected-family proposition consumed
by `Order2ProtocolBadFamily6900.protocolClaim6900_of_bad_family`.  It is
spelled locally because the legacy `V6` dependency of the DataEleven stack
currently collides with Mathlib's valuation module if both stacks are loaded
in one experimental environment. -/
abbrev TargetBadFamilyBoundViaDataEleven6900 : Prop :=
  AffineLineBadFamilyContract6900.SelectedBadGivenSetsBound
    IRSProfile.domain 131071 81731 254684620614660120

/-- Eliminating the exact DataEleven leaf closes the sole selected-family
bound consumed by the score-6900 protocol wrapper. -/
theorem targetBadFamilyBound_of_noDataElevenHighEClosedLeaf
    (hno : NoDataElevenHighEClosedLeaf6900) :
    TargetBadFamilyBoundViaDataEleven6900 := by
  intro U Gamma agreement selected hdegree hcard hagrees hbad
  have hI : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hcard' : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card := by
    intro gamma hgamma
    have h := hcard gamma hgamma
    rw [hI] at h
    norm_num at h
    exact h
  have hbad' : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code IRSProfile.domain 131072) (agreement gamma) := by
    simpa using hbad
  rcases target_bad_family_small_or_dataEleven_high_e_closed_leaf
      U Gamma agreement selected hdegree hcard' hagrees hbad' with
    hsmall | hleaf
  · exact Nat.le_of_lt hsmall
  · exact False.elim (hleaf.elim (hno U Gamma agreement selected))

#print axioms targetBadFamilyBound_of_noDataElevenHighEClosedLeaf

end
end ProximityPrize.SubmissionLower.M69DataElevenNoLeafEndpointBridge6900
