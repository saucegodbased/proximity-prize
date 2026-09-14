import UniversalProjectiveHighDirectionEndpointCut6900
import DataElevenHighEClosedFrontier6900

/-!
# Projective high-tail information on the exact surviving DataEleven leaf

This adapter keeps the projective scalar-cut breakthrough on the same witness
as the already compiled `DataElevenHighEClosedLeaf`.  Consequently downstream
work on the low-`E0` terminal branch may use both the complete rational-cross
structure and the fact that every nonzero constant received-row direction has
canonical degree at least `133120`.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighDataElevenHighEClosedFrontier6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open UniversalProjectiveHighDirectionEndpointCut6900
open DataElevenHighEClosedFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP IRSProfile.Field 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

structure ProjectiveHighDataElevenHighEClosedLeaf
    (U : Fin 2 → Index → ExtensionField)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X]) where
  toDataElevenHighEClosedLeaf :
    DataElevenHighEClosedLeaf U Gamma agreement selected
  projectiveHigh :
    CanonicalHighTailDirectionIndependent IRSProfile.domain U

/-- Any family not already below the exact MCA cap reaches the same
DataEleven high-E-closed leaf together with the new projective high-tail
invariant. -/
theorem target_bad_family_small_or_projective_high_dataEleven_leaf
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
      Nonempty (ProjectiveHighDataElevenHighEClosedLeaf
        U Gamma agreement selected) := by
  classical
  by_cases hsmall : Gamma.card < 254684620614660120
  · exact Or.inl hsmall
  · right
    have hI : Fintype.card Index = 262144 := by
      norm_num [Index, IRSProfile.Index]
    rcases bad_family_small_or_canonicalHighTailDirectionIndependent
        IRSProfile.domain hI U Gamma agreement selected hdegree hcard hagrees
          hbad with
      hsmall' | hprojective
    · exact (hsmall hsmall').elim
    · rcases target_bad_family_small_or_dataEleven_high_e_closed_leaf
          U Gamma agreement selected hdegree hcard hagrees hbad with
        hsmall' | hleaf
      · exact (hsmall hsmall').elim
      · exact Nonempty.map (fun leaf ↦ ⟨leaf, hprojective⟩) hleaf

#print axioms target_bad_family_small_or_projective_high_dataEleven_leaf

end
end ProximityPrize.SubmissionLower.ProjectiveHighDataElevenHighEClosedFrontier6900
