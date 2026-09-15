import WeightedCutoff2ScalarListW1332256900
import TwoSourceSharpIdentityNodeSplit6900
import IdentityNode2Dichotomy6900

/-! Same-witness adapter from the cutoff-two identity-node split to the `W=133225` list bound. -/
namespace ProximityPrize.SubmissionLower.TwoSourceSharpCutoff2ScalarAdapter6900

open Polynomial ProximityPrize.Benchmark
open SupportRecurrence6900 SupportRecurrence6900.Target
open TwoSourceSharpProjectiveHighEIncidenceFrontier6900
open TwoSourceSharpProjectiveResidualPackage6900
open FixedLinearNodeSupportConcentration6900
open TwoSourceSharpIdentityNodeSplit6900 IdentityNode2Dichotomy6900
open ActualAlignedRationalCrossData6900
open WeightedCutoff2RepresentativeLedgerW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP ExtensionField 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- Restricting to an identity-node subtype loses no agreement from the
support core.  Thus the cutoff-two scalar consumer applies literally to the
same retained scalars and fixed centre. -/
theorem support_core_scalar_card_lt
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected)
    (z : Finset Index) (core : Finset ExtensionField)
    (hz : z.card≤n)
    (hcoreGood : core⊆
      leaf.sharpPackage.toSharpProjectiveResidualPackage.Good)
    (hcoreAgreement : ∀ gamma∈core,agreement gamma⊆z)
    (hdegree : ∀ gamma∈core,
      (leaf.sharpPackage.toSharpProjectiveResidualPackage.scalar gamma).natDegree≤w) :
    core.card<retained := by
  classical
  letI : DecidableEq ExtensionField :=
    WeightedCutoff2ScalarListW1332256900.instDecidableEq_weightedCutoff2ScalarListW1332256900
  letI : Fintype ↑z := Finset.Subtype.fintype z
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  let nodeZ : ↑z→ExtensionField := fun i => IRSProfile.domain i.1
  let centreZ : ↑z→ExtensionField := fun i => P.centre i.1
  have hnodeZ : Function.Injective nodeZ := by
    intro i j hij
    apply Subtype.ext
    exact IRSProfile.domain.injective hij
  have hcardZ : Fintype.card ↑z≤n := by
    simpa using hz
  have hscalar : Set.InjOn P.scalar (↑core : Set ExtensionField) :=
    P.scalar_injective.mono hcoreGood
  apply WeightedCutoff2ScalarListW1332256900.scalarized_seed_family_card_lt_retained
    nodeZ centreZ hnodeZ hcardZ core P.scalar hscalar hdegree
  intro gamma hgamma
  have hgammaGood : gamma∈P.Good := hcoreGood hgamma
  have hgammaGamma : gamma∈Gamma := P.good_subset hgammaGood
  have hsubZ : agreement gamma⊆z := hcoreAgreement gamma hgamma
  let e : ↑(agreement gamma)↪↑z :=
    ⟨fun i => ⟨i.1,hsubZ i.2⟩,fun i j hij => by
      apply Subtype.ext
      exact congrArg (fun x : ↑z => x.1) hij⟩
  have himage : (agreement gamma).attach.map e⊆
      z.attach.filter fun i : ↑z =>
        (P.scalar gamma).eval (nodeZ i)=centreZ i := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    refine Finset.mem_filter.mpr ⟨by simp,?_⟩
    exact (P.scalar_data gamma hgammaGood).2.2.2 i.1 i.2
  have hmapCard : (agreement gamma).card=((agreement gamma).attach.map e).card := by
    simp
  have hbase := leaf.agreement_card gamma hgammaGamma
  have hle := Finset.card_le_card himage
  norm_num [a] at hbase ⊢
  omega

/-- The exact small-identity-core branch forces an actual retained scalar of
degree at least `133226`; it cannot survive as a low-degree list. -/
theorem small_identity_core_forces_degree_133226
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected)
    (z : Finset Index) (core : Finset ExtensionField)
    (hz : z.card≤n) (hlarge : retained≤core.card)
    (hcoreGood : core⊆
      leaf.sharpPackage.toSharpProjectiveResidualPackage.Good)
    (hcoreAgreement : ∀ gamma∈core,agreement gamma⊆z) :
    ∃ gamma∈core,133226≤
      (leaf.sharpPackage.toSharpProjectiveResidualPackage.scalar gamma).natDegree := by
  classical
  by_contra hnot
  push Not at hnot
  have hdegree : ∀ gamma∈core,
      (leaf.sharpPackage.toSharpProjectiveResidualPackage.scalar gamma).natDegree≤w := by
    intro gamma hgamma
    have h := hnot gamma hgamma
    norm_num [w] at h ⊢
    omega
  have hsmall := support_core_scalar_card_lt leaf z core hz
    hcoreGood hcoreAgreement hdegree
  omega

/-- Full same-witness result: either the scalar allowance improves from
`133225` to `133226`, or the only remaining case is the hard identity locus
on at least `262143` of the original nodes. -/
theorem sharp_scalar_allowance_133226_or_hard_identity
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
    133226≤((131071+P.E0.natDegree)-
        max leaf.toWeightedLeaf.cross.c.natDegree
          leaf.toWeightedLeaf.cross.d.natDegree)-P.Q.natDegree ∨
      262143≤z.card := by
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
  let z := identityNodes nodes row0 row1
  let core := supportCore P.Good agreement z
  have hlinear : ∀ gamma∈P.Good, ∀ i∈agreement gamma,
      row0 i+gamma*row1 i=0 := by
    simpa only [P,row0,row1] using sharp_agreement_fixed_linear_equation leaf
  have hnodes : ∀ gamma∈P.Good,agreement gamma⊆nodes := by
    intro gamma hgamma i hi
    simp only [nodes,Finset.mem_univ]
  have hnodesCard : nodes.card=262144 := by
    simp only [nodes,Finset.card_univ]
    norm_num [Index,IRSProfile.Index]
  obtain hsmall | hhard := identity_node_2_dichotomy P.Good nodes agreement
    row0 row1 hnodesCard P.retained_card_ge hnodes hlinear
  · left
    obtain ⟨gamma,hgamma,hdeg⟩ :=
      small_identity_core_forces_degree_133226 leaf z core
        hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2
    exact hdeg.trans (P.scalar_data gamma (hsmall.2.2.1 hgamma)).2.1
  · exact Or.inr hhard

end
end ProximityPrize.SubmissionLower.TwoSourceSharpCutoff2ScalarAdapter6900

#print axioms ProximityPrize.SubmissionLower.TwoSourceSharpCutoff2ScalarAdapter6900.support_core_scalar_card_lt
#print axioms ProximityPrize.SubmissionLower.TwoSourceSharpCutoff2ScalarAdapter6900.sharp_scalar_allowance_133226_or_hard_identity
