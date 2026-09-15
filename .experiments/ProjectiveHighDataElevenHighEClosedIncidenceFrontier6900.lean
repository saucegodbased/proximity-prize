import ProjectiveHighDataElevenHighEClosedFrontier6900

/-!
# Lossless projective-high DataEleven endpoint

The previous projective-high endpoint retained the deep algebraic leaf and
the canonical high-tail invariant, but (like the older DataEleven endpoint)
dropped the four original benchmark-family hypotheses.  Those hypotheses are
exactly what an incidence or eliminant argument needs.  This record keeps all
of them on the same `U/Gamma/agreement/selected` witness.

This is packaging, not the missing no-leaf theorem.  Its purpose is to make
the next research gate honest: a proposed contradiction must consume this
exact record rather than silently changing families or assuming agreement
data which is no longer in scope.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ProjectiveHighDataElevenHighEClosedFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- The strongest currently reached same-witness leaf, with no loss of the
benchmark-facing incidence hypotheses. -/
structure ProjectiveHighDataElevenHighEClosedIncidenceLeaf
    (U : Fin 2 → Index → ExtensionField)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X]) where
  toProjectiveHighDataElevenHighEClosedLeaf :
    ProjectiveHighDataElevenHighEClosedLeaf U Gamma agreement selected
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

/-- The existing projective-high caller constructs the lossless record
without a witness exchange or any new mathematical assumption. -/
theorem target_bad_family_small_or_projective_high_dataEleven_incidence_leaf
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
      Nonempty (ProjectiveHighDataElevenHighEClosedIncidenceLeaf
        U Gamma agreement selected) := by
  rcases target_bad_family_small_or_projective_high_dataEleven_leaf
      U Gamma agreement selected hdegree hcard hagrees hbad with
    hsmall | hleaf
  · exact Or.inl hsmall
  · exact Or.inr <| hleaf.map fun leaf ↦
      ⟨leaf, hdegree, hcard, hagrees, hbad⟩

#print axioms ProjectiveHighDataElevenHighEClosedIncidenceLeaf
#print axioms target_bad_family_small_or_projective_high_dataEleven_incidence_leaf

end
end ProximityPrize.SubmissionLower.ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900
