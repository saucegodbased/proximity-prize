import HeterogeneousLinearInterpolationSource6900
import TwoSourceSharpProjectiveHighEIncidenceFrontier6900
import FixedLinearNodeSupportConcentration6900

/-!
# Exact sharp-leaf adapter for the adaptive heterogeneous source

This file applies the matrix-free source to the literal sharp projective
leaf, without changing `U`, `Gamma`, `agreement`, `selected`, `Good`, the
scalar family, or its centre.  It also records the exact conditional semantic
endpoint: the source globalizes simultaneously on every retained candidate
provided the package's single scalar allowance is at most `148023`.
-/

namespace ProximityPrize.SubmissionLower.HeterogeneousLinearInterpolationSharpAdapter6900

open Polynomial ProximityPrize.Benchmark
open SupportRecurrence6900 SupportRecurrence6900.Target
open HeterogeneousLinearInterpolationSource6900
open TwoSourceSharpProjectiveHighEIncidenceFrontier6900
open FixedLinearNodeSupportConcentration6900 SupportRecurrence6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

noncomputable section

/-- The adaptive one-dimensional kernel exists on the exact node values and
centre carried by the sharp leaf.  This is still only a source until its
scalar cap is checked. -/
theorem exact_leaf_has_adaptive_nodal_kernel
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) :
    let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
    ∃ source : SourceSpace ExtensionField 180413 131071 148023 262145,
      source ≠ 0 ∧
      nodalConstraintMap ExtensionField IRSProfile.domain
        (fun i ↦ U 0 i) (fun i ↦ U 1 i) P.centre
        180413 131071 148023 262145 source = 0 := by
  dsimp only
  apply target_exists_nonzero_adaptive_nodal_kernel ExtensionField
  norm_num [Index, IRSProfile.Index]

/-- Exact conditional endpoint.  The source and all global syzygies use the
same retained scalar/candidate family from the leaf. -/
theorem exact_leaf_global_syzygies_of_gap
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected)
    (W r : Nat) (hW : W < 180413)
    (hgap :
      262144 * (r + 1) <
        r * (180413 + (180413 - 131071) + (180413 - W)))
    (hallowance :
      ((131071 +
          leaf.sharpPackage.toSharpProjectiveResidualPackage.E0.natDegree) -
        max
          leaf.toWeightedLeaf.cross.c.natDegree
          leaf.toWeightedLeaf.cross.d.natDegree) -
        leaf.sharpPackage.toSharpProjectiveResidualPackage.Q.natDegree ≤
          W) :
    let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
    ∃ source : SourceSpace ExtensionField 180413 131071 W r,
      source ≠ 0 ∧
      nodalConstraintMap ExtensionField IRSProfile.domain
        (fun i ↦ U 0 i) (fun i ↦ U 1 i) P.centre
        180413 131071 W r source = 0 ∧
      ∀ gamma ∈ P.Good,
        (specializeFamily ExtensionField source.1 gamma).val +
            (specializeFamily ExtensionField source.2.1 gamma).val *
              selected gamma +
            (specializeFamily ExtensionField source.2.2 gamma).val *
              P.scalar gamma = 0 := by
  classical
  dsimp only
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  have hIndex : Fintype.card Index = 262144 := by
    norm_num [Index, IRSProfile.Index]
  have hgap' : Fintype.card Index * (r + 1) <
      r * (180413 + (180413 - 131071) + (180413 - W)) := by
    rw [hIndex]
    exact hgap
  obtain ⟨source, hsource_ne, hsource⟩ :=
    exists_nonzero_nodal_kernel_of_gap ExtensionField IRSProfile.domain
      (fun i ↦ U 0 i) (fun i ↦ U 1 i) P.centre
      180413 131071 W r hgap'
  refine ⟨source, hsource_ne, hsource, ?_⟩
  intro gamma hgamma
  apply kernel_global_syzygy ExtensionField IRSProfile.domain
    (fun i ↦ U 0 i) (fun i ↦ U 1 i) P.centre
    180413 131071 W r source hsource gamma
    (selected gamma) (P.scalar gamma) (agreement gamma)
  · exact IRSProfile.domain.injective
  · norm_num
  · norm_num
  · exact hW
  · exact leaf.selected_degree gamma (P.good_subset hgamma)
  · exact (P.scalar_data gamma hgamma).2.1.trans hallowance
  · exact leaf.agreement_card gamma (P.good_subset hgamma)
  · intro i hi
    exact leaf.selected_agrees gamma (P.good_subset hgamma) i hi
  · intro i hi
    exact (P.scalar_data gamma hgamma).2.2.2 i hi

def sharpRow0
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) (i : Index) : ExtensionField :=
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  P.E0.eval (IRSProfile.domain i) * U 0 i -
    P.a.eval (IRSProfile.domain i) -
      P.Q.eval (IRSProfile.domain i) *
        leaf.toWeightedLeaf.cross.c.eval (IRSProfile.domain i) * P.centre i

def sharpRow1
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) (i : Index) : ExtensionField :=
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  P.E0.eval (IRSProfile.domain i) * U 1 i -
    P.b.eval (IRSProfile.domain i) -
      P.Q.eval (IRSProfile.domain i) *
        leaf.toWeightedLeaf.cross.d.eval (IRSProfile.domain i) * P.centre i

def sharpIdentityNodes
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) : Finset Index :=
  identityNodes Finset.univ (sharpRow0 leaf) (sharpRow1 leaf)

def sharpExceptionalNodes
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) : Finset Index :=
  Finset.univ \ sharpIdentityNodes leaf

/-- In the large-identity branch, the locator of the at most 292 exceptional
nodes masks the already-known fixed scalar relation into an all-node
identity.  Opaque row definitions keep this exact endpoint cheap to check. -/
theorem exact_leaf_large_identity_mask
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected)
    (hZ : 261852 ≤ (sharpIdentityNodes leaf).card) :
      (sharpExceptionalNodes leaf).card ≤ 292 ∧
      (supportLocator IRSProfile.domain
        (sharpExceptionalNodes leaf)).natDegree ≤ 292 ∧
      ∀ i gamma,
        (supportLocator IRSProfile.domain
            (sharpExceptionalNodes leaf)).eval
            (IRSProfile.domain i) *
          (sharpRow0 leaf i + gamma * sharpRow1 leaf i) = 0 := by
  classical
  have hZsub : sharpIdentityNodes leaf ⊆
      (Finset.univ : Finset Index) := by
    intro i hi
    exact Finset.mem_univ i
  have huniv : (Finset.univ : Finset Index).card = 262144 := by
    norm_num [Index, IRSProfile.Index]
  have hcardEq : (sharpExceptionalNodes leaf).card =
      (Finset.univ : Finset Index).card -
        (sharpIdentityNodes leaf).card := by
    dsimp only [sharpExceptionalNodes]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hZsub]
  have hexceptional : (sharpExceptionalNodes leaf).card ≤ 292 := by
    omega
  refine ⟨hexceptional, ?_, ?_⟩
  · rw [supportLocator_natDegree]
    exact hexceptional
  · intro i gamma
    by_cases hi : i ∈ sharpIdentityNodes leaf
    · have hrows : sharpRow0 leaf i = 0 ∧ sharpRow1 leaf i = 0 := by
        simpa only [sharpIdentityNodes, identityNodes,
          Finset.mem_filter, Finset.mem_univ, true_and] using hi
      rw [hrows.1, hrows.2]
      ring
    · have hiExceptional : i ∈ sharpExceptionalNodes leaf := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
      rw [supportLocator_eval_eq_zero IRSProfile.domain
        (sharpExceptionalNodes leaf)
        hiExceptional, zero_mul]

#print axioms exact_leaf_has_adaptive_nodal_kernel
#print axioms exact_leaf_global_syzygies_of_gap
#print axioms exact_leaf_large_identity_mask

end
end ProximityPrize.SubmissionLower.HeterogeneousLinearInterpolationSharpAdapter6900
