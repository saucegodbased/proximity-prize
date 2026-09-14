import DataElevenHighEClosedFrontier6900

/-!
# Preserve the original incidence hypotheses past the DataEleven leaf

`DataElevenHighEClosedLeaf` stores the algebraic `DataEleven`/conic/cross
payload, but it does not store the four hypotheses about the selected family
which were supplied to its constructor: selected degree, agreement size,
agreement equality, and badness.  This file gives the lossless endpoint
record and a literal countergate showing why the omitted agreement-size field
cannot be reconstructed from the terminal fixed-scalar payload.
-/

namespace ProximityPrize.SubmissionLower.DataElevenHighEClosedIncidenceRepair6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open DataElevenHighEClosedFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Lossless version of the terminal leaf.  These four fields are exactly the
caller hypotheses which the old `DataElevenHighEClosedLeaf` did not retain. -/
structure DataElevenHighEClosedIncidenceLeaf
    (U : Fin 2 → Index → ExtensionField)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X]) where
  toDataElevenHighEClosedLeaf :
    DataElevenHighEClosedLeaf U Gamma agreement selected
  selected_degree :
    ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071
  agreement_card :
    ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card
  selected_agrees :
    ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (IRSProfile.domain i) =
        U 0 i + gamma * U 1 i
  selected_bad :
    ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code IRSProfile.domain 131072) (agreement gamma)

/-- The existing exact caller packages the lossless record without any new
mathematics or witness exchange. -/
theorem target_bad_family_small_or_dataEleven_high_e_closed_incidence_leaf
    (U : Fin 2 → Index → ExtensionField)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X])
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i)
    (hbad : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code IRSProfile.domain 131072) (agreement gamma)) :
    Gamma.card < 254684620614660120 ∨
      Nonempty (DataElevenHighEClosedIncidenceLeaf
        U Gamma agreement selected) := by
  rcases target_bad_family_small_or_dataEleven_high_e_closed_leaf
      U Gamma agreement selected hdegree hcard hagrees hbad with
    hsmall | hleaf
  · exact Or.inl hsmall
  · exact Or.inr <| hleaf.map fun leaf ↦
      ⟨leaf, hdegree, hcard, hagrees, hbad⟩

#print axioms DataElevenHighEClosedIncidenceLeaf
#print axioms target_bad_family_small_or_dataEleven_high_e_closed_incidence_leaf

end
end ProximityPrize.SubmissionLower.DataElevenHighEClosedIncidenceRepair6900
