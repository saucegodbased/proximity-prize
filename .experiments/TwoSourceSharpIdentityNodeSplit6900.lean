import TwoSourceSharpProjectiveHighEIncidenceFrontier6900
import FixedLinearNodeSupportConcentration6900
import IdentityNode293Dichotomy6900

/-!
# Exact identity-node split for the sharp two-source leaf

For a retained scalar seed `gamma`, evaluation of the sharp residual identity
on one of its agreement nodes is affine in `gamma`.  A node where the two
fixed coefficients do not both vanish can therefore support at most one
retained seed.  This file attaches that generic concentration theorem to the
*same* sharp/projective/high-E witness produced by the benchmark-facing leaf.

The useful numerical split is at 293 exceptional nodes:

* either the fixed identity-node universe has cardinality at most `261851`,
  while at least `263611557201523206` retained seeds keep their entire
  `180413`-point agreement set inside it; or
* at least `261852` of the `262144` domain nodes are fixed identity nodes.

The first branch is the exact shortened universe on which the W133225 helper
dimension turns positive.  The second branch is the isolated structural debt.
-/
namespace ProximityPrize.SubmissionLower.TwoSourceSharpIdentityNodeSplit6900

open Polynomial ProximityPrize.Benchmark
open SupportRecurrence6900 SupportRecurrence6900.Target
open TwoSourceSharpProjectiveHighEIncidenceFrontier6900
open TwoSourceSharpProjectiveResidualPackage6900
open FixedLinearNodeSupportConcentration6900
open IdentityNode293Dichotomy6900
open ActualAlignedRationalCrossData6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Evaluation of the same-witness sharp scalar residual gives the fixed
affine node equation used by the concentration theorem. -/
theorem sharp_agreement_fixed_linear_equation
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) :
    let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
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
    ∀ gamma ∈ P.Good, ∀ i ∈ agreement gamma,
      row0 i + gamma * row1 i = 0 := by
  classical
  dsimp only
  intro gamma hgamma i hi
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  have hgammaGamma : gamma ∈ Gamma := P.good_subset hgamma
  have hselected := leaf.selected_agrees gamma hgammaGamma i hi
  have hscalar := (P.scalar_data gamma hgamma).2.2.2 i hi
  have hresidual := polynomial_residual_node_equation gamma
    (IRSProfile.domain i) (U 0 i) (U 1 i) (P.centre i)
    P.E0 P.Q P.a P.b leaf.toWeightedLeaf.cross.c
      leaf.toWeightedLeaf.cross.d (selected gamma) (P.scalar gamma)
    (P.scalar_data gamma hgamma).2.2.1 hselected hscalar
  exact evaluated_residual_fixed_linear_equation gamma
    (P.E0.eval (IRSProfile.domain i))
    (P.Q.eval (IRSProfile.domain i))
    (P.a.eval (IRSProfile.domain i))
    (P.b.eval (IRSProfile.domain i))
    (leaf.toWeightedLeaf.cross.c.eval (IRSProfile.domain i))
    (leaf.toWeightedLeaf.cross.d.eval (IRSProfile.domain i))
    (P.centre i) (U 0 i) (U 1 i) hresidual

/-- Exact 293-node dichotomy.  No seed is reselected and no agreement point
is removed: in the small-universe branch every surviving seed keeps its
original agreement set. -/
theorem sharp_identity_node_293_dichotomy
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
    (z.card ≤ 261851 ∧
      263611557201523206 ≤ core.card ∧
      core ⊆ P.Good ∧
      (∀ gamma ∈ core, agreement gamma ⊆ z)) ∨
      261852 ≤ z.card := by
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
    simpa only [P, row0, row1] using sharp_agreement_fixed_linear_equation leaf
  have hnodes : ∀ gamma ∈ P.Good, agreement gamma ⊆ nodes := by
    intro gamma hgamma i hi
    simp only [nodes, Finset.mem_univ]
  have hnodesCard : nodes.card = 262144 := by
    simp only [nodes, Finset.card_univ]
    norm_num [Index, IRSProfile.Index]
  have hretained : 263611557201785350 ≤ P.Good.card := by
    exact P.retained_card_ge
  simpa only [P, nodes, row0, row1] using
    (identity_node_293_dichotomy P.Good nodes agreement row0 row1
      hnodesCard hretained hnodes hlinear)

#print axioms sharp_agreement_fixed_linear_equation
#print axioms sharp_identity_node_293_dichotomy

end
end ProximityPrize.SubmissionLower.TwoSourceSharpIdentityNodeSplit6900
