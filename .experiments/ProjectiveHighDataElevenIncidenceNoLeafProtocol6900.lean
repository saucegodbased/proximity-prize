import ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900
import Order2ProtocolBadFamily6900

/-!
# Exact score-6900 endpoint for the lossless projective-high leaf

This file deliberately isolates the one mathematical proposition now being
attacked.  It proves that excluding the exact, same-witness incidence leaf
closes the selected-bad-family bound and hence the benchmark claim.  It adds
no claim that the leaf has already been excluded.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighDataElevenIncidenceNoLeafProtocol6900

open ProximityPrize.Benchmark
open ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900
open Order2ProtocolBadFamily6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- The single exact research obligation.  Unlike the older no-leaf
interface, the input retains selected degree, agreement cardinality, exact
agreement, and badness on the same witness. -/
def NoProjectiveHighDataElevenHighEClosedIncidenceLeaf6900 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
      (Gamma : Finset IRSProfile.Field)
      (agreement : IRSProfile.Field → Finset IRSProfile.Index)
      (selected : IRSProfile.Field → Polynomial IRSProfile.Field),
    ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected → False

/-- Excluding the exact lossless leaf proves the precise selected-family
bound consumed by the score-6900 protocol. -/
theorem targetBadFamilyBound_of_noProjectiveHighDataElevenIncidenceLeaf
    (hno : NoProjectiveHighDataElevenHighEClosedIncidenceLeaf6900) :
    TargetBadFamilyBound6900 := by
  intro U Gamma agreement selected hdegree hcard hagrees hbad
  have hI : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hcard' : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card := by
    intro gamma hgamma
    have h := hcard gamma hgamma
    rw [hI] at h
    norm_num [Order2Protocol6900.errors] at h
    omega
  have hbad' : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code IRSProfile.domain 131072) (agreement gamma) := by
    simpa using hbad
  rcases
      target_bad_family_small_or_projective_high_dataEleven_incidence_leaf
        U Gamma agreement selected hdegree hcard' hagrees hbad' with
    hsmall | hleaf
  · exact Nat.le_of_lt hsmall
  · exact False.elim <| hleaf.elim (hno U Gamma agreement selected)

/-- Checked benchmark-facing composition.  The sole premise is exactly the
lossless no-leaf proposition above. -/
theorem protocolClaim6900_of_noProjectiveHighDataElevenIncidenceLeaf
    (hno : NoProjectiveHighDataElevenHighEClosedIncidenceLeaf6900) :
    ProtocolClaim 6900 Order2Protocol6900.radiusNumerator
      Order2Protocol6900.radiusDenominator := by
  apply protocolClaim6900_of_bad_family
  exact targetBadFamilyBound_of_noProjectiveHighDataElevenIncidenceLeaf hno

#print axioms targetBadFamilyBound_of_noProjectiveHighDataElevenIncidenceLeaf
#print axioms protocolClaim6900_of_noProjectiveHighDataElevenIncidenceLeaf

end
end ProximityPrize.SubmissionLower.ProjectiveHighDataElevenIncidenceNoLeafProtocol6900
