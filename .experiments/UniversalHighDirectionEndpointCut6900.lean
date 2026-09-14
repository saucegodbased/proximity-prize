import LowReceivedDirectionScalarSplit6900
import Order2ProtocolBadFamily6900

/-!
# Exact universal high-direction cut for the score-6900 endpoint

This file exposes the precise source theorem which remains after the compiled
low received-direction argument.  In particular, the high-direction premise
still quantifies over the original arbitrary received rows, selected seed
family, actual agreement sets, and bad-row witnesses.  A theorem about one
frozen NTT partition or one fixed received direction does not inhabit this
predicate.
-/

namespace ProximityPrize.SubmissionLower.UniversalHighDirectionEndpointCut6900

open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.AffineLineBadFamilyContract6900
open ProximityPrize.SubmissionLower.LowReceivedDirectionScalarSplit6900
open ProximityPrize.SubmissionLower.Order2ProtocolBadFamily6900
open ProximityPrize.SubmissionLower.Order2Protocol6900

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- The exact universal theorem still required from any Full187/high-degree
source construction.  Every hypothesis is inherited from the benchmark's
selected-bad-family contract; the only additional fact is that the canonical
interpolant of the second received row has degree at least `132103`. -/
def UniversalHighDirectionBadFamilyBound
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) : Prop :=
  ∀ (U : Fin 2 → I → K) (seeds : Finset K)
      (A : K → Finset I) (selected : K → Polynomial K),
    (∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071) →
    (∀ gamma ∈ seeds, 180413 ≤ (A gamma).card) →
    (∀ gamma ∈ seeds, ∀ i ∈ A gamma,
      (selected gamma).eval (nodes i) = U 0 i + gamma * U 1 i) →
    (∀ gamma ∈ seeds, ∃ j : Fin 2,
      LinearCode.projectedWord (U j) (A gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (A gamma)) →
    132103 ≤ (receivedDirectionInterpolant nodes (U 1)).natDegree →
    seeds.card ≤ 254684620614660120

/-- The low-degree scalar theorem and the exact universal high-direction cut
compose directly into the selected-family bound.  Keeping this theorem
generic prevents target-field implementation details from being embedded in
the proof term. -/
theorem selectedBadGivenSetsBound_of_universalHighDirection
    {I K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field K] [Fintype K] [DecidableEq K]
    [CharP K Order2ValueYCap132102Ledger.targetPrime]
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (hhigh : UniversalHighDirectionBadFamilyBound nodes) :
    SelectedBadGivenSetsBound nodes 131071 81731
      254684620614660120 := by
  intro U seeds A selected hdegree hcard hagreement hbad
  have hcard' : ∀ gamma ∈ seeds, 180413 ≤ (A gamma).card := by
    intro gamma hgamma
    have h := hcard gamma hgamma
    omega
  have hbad' : ∀ gamma ∈ seeds, ∃ j : Fin 2,
      LinearCode.projectedWord (![U 0, U 1] j) (A gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (A gamma) := by
    intro gamma hgamma
    obtain ⟨j, hj⟩ := hbad gamma hgamma
    refine ⟨j, ?_⟩
    fin_cases j <;> simpa using hj
  by_cases hVsmall :
      (receivedDirectionInterpolant nodes (U 1)).natDegree ≤ 132102
  · have hsmall : seeds.card < 254684620614660120 :=
      low_received_direction_bad_family_lt_mca
        (nodes := nodes) hI (U 0) (U 1)
        (receivedDirectionInterpolant nodes (U 1)) hVsmall
        (fun i ↦ receivedDirectionInterpolant_eval nodes (U 1) i)
        seeds A selected hdegree hcard' hagreement hbad'
    exact Nat.le_of_lt hsmall
  · have hV : 132103 ≤
        (receivedDirectionInterpolant nodes (U 1)).natDegree := by
      omega
    exact hhigh U seeds A selected hdegree hcard' hagreement hbad hV

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : CharP IRSProfile.Field
    Order2ValueYCap132102Ledger.targetPrime := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

abbrev UniversalHighDirectionBadFamilyBound6900 : Prop :=
  UniversalHighDirectionBadFamilyBound IRSProfile.domain

/-- Target specialization of the generic composition theorem. -/
theorem targetBadFamilyBound6900_of_universalHighDirection
    (hhigh : UniversalHighDirectionBadFamilyBound6900) :
    TargetBadFamilyBound6900 := by
  have hI : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have h := selectedBadGivenSetsBound_of_universalHighDirection
    IRSProfile.domain hI hhigh
  simpa [TargetBadFamilyBound6900, Order2Protocol6900.errors,
    Order2Protocol6900.mcaBudget] using h

/-- Consequently the same universal high-direction theorem is the sole
mathematical input needed by the already-compiled score-6900 protocol
wrapper. -/
theorem protocolClaim6900_of_universalHighDirection
    (hhigh : UniversalHighDirectionBadFamilyBound6900) :
    ProtocolClaim 6900 Order2Protocol6900.radiusNumerator
      Order2Protocol6900.radiusDenominator :=
  protocolClaim6900_of_bad_family
    (targetBadFamilyBound6900_of_universalHighDirection hhigh)

end
end ProximityPrize.SubmissionLower.UniversalHighDirectionEndpointCut6900

#print axioms ProximityPrize.SubmissionLower.UniversalHighDirectionEndpointCut6900.targetBadFamilyBound6900_of_universalHighDirection
#print axioms ProximityPrize.SubmissionLower.UniversalHighDirectionEndpointCut6900.protocolClaim6900_of_universalHighDirection
