import TwoSourceSharpProjectiveHighEIncidenceFrontier6900
import FixedLinearNodeSupportConcentration6900
import IdentityNode2Dichotomy6900
import TwoSourceSharpIdentityNodeSplit6900

/-!
# Exact two-exception identity-node split for the sharp two-source leaf

This retunes the already formal affine-node injection at the strongest
currently viable shortened-universe cutoff.  Either the W133225 list-count
consumer runs on at most `262142` nodes, or the fixed residual relation is an
identity on at least `262143` of the `262144` evaluation nodes.
-/
namespace ProximityPrize.SubmissionLower.TwoSourceSharpIdentityNode2Split6900

open Polynomial ProximityPrize.Benchmark
open SupportRecurrence6900 SupportRecurrence6900.Target
open TwoSourceSharpProjectiveHighEIncidenceFrontier6900
open TwoSourceSharpProjectiveResidualPackage6900
open FixedLinearNodeSupportConcentration6900
open IdentityNode2Dichotomy6900
open TwoSourceSharpIdentityNodeSplit6900
open ActualAlignedRationalCrossData6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Exact cutoff-two dichotomy.  In the small-universe branch every retained
seed keeps its entire original agreement set. -/
theorem sharp_identity_node_2_dichotomy
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) :
    let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
    let nodes : Finset Index := Finset.univ
    let row0 := fun i : Index ↦
      P.E0.eval (IRSProfile.domain i) * U 0 i -
        P.a.eval (IRSProfile.domain i) -
          P.Q.eval (IRSProfile.domain i) *
            leaf.toWeightedLeaf.cross.c.eval (IRSProfile.domain i) * P.centre i
    let row1 := fun i : Index ↦
      P.E0.eval (IRSProfile.domain i) * U 1 i -
        P.b.eval (IRSProfile.domain i) -
          P.Q.eval (IRSProfile.domain i) *
            leaf.toWeightedLeaf.cross.d.eval (IRSProfile.domain i) * P.centre i
    let z := identityNodes nodes row0 row1
    let core := supportCore P.Good agreement z
    (z.card ≤ 262142 ∧
      263611557201523206 ≤ core.card ∧
      core ⊆ P.Good ∧
      (∀ gamma ∈ core, agreement gamma ⊆ z)) ∨
      262143 ≤ z.card := by
  classical
  dsimp only
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  let nodes : Finset Index := Finset.univ
  let row0 := fun i : Index ↦
    P.E0.eval (IRSProfile.domain i) * U 0 i -
      P.a.eval (IRSProfile.domain i) -
        P.Q.eval (IRSProfile.domain i) *
          leaf.toWeightedLeaf.cross.c.eval (IRSProfile.domain i) * P.centre i
  let row1 := fun i : Index ↦
    P.E0.eval (IRSProfile.domain i) * U 1 i -
      P.b.eval (IRSProfile.domain i) -
        P.Q.eval (IRSProfile.domain i) *
          leaf.toWeightedLeaf.cross.d.eval (IRSProfile.domain i) * P.centre i
  have hlinear : ∀ gamma ∈ P.Good, ∀ i ∈ agreement gamma,
      row0 i + gamma * row1 i = 0 := by
    simpa only [P, row0, row1] using
      (sharp_agreement_fixed_linear_equation leaf)
  have hnodes : ∀ gamma ∈ P.Good, agreement gamma ⊆ nodes := by
    intro gamma hgamma i hi
    simp only [nodes, Finset.mem_univ]
  have hnodesCard : nodes.card = 262144 := by
    simp only [nodes, Finset.card_univ]
    norm_num [Index, IRSProfile.Index]
  have hretained : 263611557201785350 ≤ P.Good.card :=
    P.retained_card_ge
  simpa only [P, nodes, row0, row1] using
    (identity_node_2_dichotomy P.Good nodes agreement row0 row1
      hnodesCard hretained hnodes hlinear)

#print axioms sharp_identity_node_2_dichotomy

end
end ProximityPrize.SubmissionLower.TwoSourceSharpIdentityNode2Split6900
