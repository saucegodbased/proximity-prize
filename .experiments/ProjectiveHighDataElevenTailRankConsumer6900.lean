import ProjectiveHighDataElevenHighEClosedFrontier6900
import CanonicalHighTailCoefficientRank6900

/-! Same-witness export of the canonical coefficient-tail rank on the exact
post-high-E DataEleven leaf. -/

namespace ProximityPrize.SubmissionLower.ProjectiveHighDataElevenTailRankConsumer6900

open Polynomial ProximityPrize.Benchmark
open CanonicalHighTailCoefficientRank6900
open ProjectiveHighDataElevenHighEClosedFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

/-- No witness exchange: this is the literal `U` carried by the terminal
DataEleven leaf. -/
theorem ProjectiveHighDataElevenHighEClosedLeaf.canonical_tail_rank_two
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (agreement : IRSProfile.Field → Finset IRSProfile.Index)
    (selected : IRSProfile.Field → IRSProfile.Field[X])
    (leaf : ProjectiveHighDataElevenHighEClosedLeaf
      U Gamma agreement selected) :
    Module.finrank IRSProfile.Field
      (Submodule.span IRSProfile.Field
        (Set.range (canonicalHighCoefficientTail IRSProfile.domain U))) = 2 :=
  canonicalHighCoefficientTail_span_finrank_eq_two IRSProfile.domain U
    leaf.projectiveHigh

#print axioms ProjectiveHighDataElevenHighEClosedLeaf.canonical_tail_rank_two

end
end ProximityPrize.SubmissionLower.ProjectiveHighDataElevenTailRankConsumer6900
