import TwoSourceSharpProjectiveHighEIncidenceFrontier6900
import WeightedExtendedEndpointClosedW1332266900

/-!
# Same-witness adapter for the full-node W=133226 endpoint

The sharp package already supplies a large injective family of scalar
polynomials, all evaluated against one fixed centre on their original
agreement sets.  This file maps that exact retained `Good` family into a
polynomial finset and feeds it directly to the full-domain endpoint.  No
identity-node split or support-core restriction is used.
-/
namespace ProximityPrize.SubmissionLower.TwoSourceSharpScalarEndpointW133226Adapter6900

open Polynomial ProximityPrize.Benchmark
open SupportRecurrence6900 SupportRecurrence6900.Target
open TwoSourceSharpProjectiveHighEIncidenceFrontier6900
open TwoSourceSharpProjectiveResidualPackage6900
open TwoSourceSharpFixedScalarRetarget6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance (priority := 10000) : DecidableEq ExtensionField :=
  WeightedExtendedEndpointClosedW1332266900.«instDecidableEq_.experiments»
local instance : CharP ExtensionField 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- The exact retained scalar family cannot have scalar allowance at most
`133226`.  This is the direct full-domain join between the sharp structural
leaf and the closed weighted endpoint. -/
theorem sharp_scalar_allowance_ge_133227
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) :
    133227 ≤
      ((131071 +
          leaf.sharpPackage.toSharpProjectiveResidualPackage.E0.natDegree) -
        max leaf.toWeightedLeaf.cross.c.natDegree
          leaf.toWeightedLeaf.cross.d.natDegree) -
        leaf.sharpPackage.toSharpProjectiveResidualPackage.Q.natDegree := by
  classical
  let P := leaf.sharpPackage.toSharpProjectiveResidualPackage
  let W := ((131071 + P.E0.natDegree) -
    max leaf.toWeightedLeaf.cross.c.natDegree
      leaf.toWeightedLeaf.cross.d.natDegree) - P.Q.natDegree
  let ScalarGamma : Finset (Polynomial ExtensionField) :=
    P.Good.image P.scalar
  by_contra hnot
  have hW : W ≤ 133226 := by
    dsimp only [W,P]
    omega
  have hdegree : ∀ S∈ScalarGamma, S.natDegree≤133226 := by
    intro S hS
    obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hS
    exact (P.scalar_data gamma hgamma).2.1.trans hW
  have hcardImage : ScalarGamma.card=P.Good.card := by
    exact Finset.card_image_iff.mpr P.scalar_injective
  have hlarge :
      WeightedIdentityExtendedLShapeArithmeticW1332266900.coreFloor≤
        ScalarGamma.card := by
    calc
      WeightedIdentityExtendedLShapeArithmeticW1332266900.coreFloor
          ≤ sharpRetainedBudget := by
            norm_num
              [WeightedIdentityExtendedLShapeArithmeticW1332266900.coreFloor,
                sharpRetainedBudget]
      _ ≤ P.Good.card := P.retained_card_ge
      _ = ScalarGamma.card := hcardImage.symm
  have hIndex : Fintype.card IRSProfile.Index=262144 := by
    rw [Fintype.card_fin]
    norm_num
  apply WeightedExtendedEndpointClosedW1332266900.hard_endpoint_coreFloor_contradiction
    (K:=ExtensionField) (I:=IRSProfile.Index) IRSProfile.domain P.centre
      IRSProfile.domain.injective hIndex ScalarGamma
  · exact hdegree
  · intro S hS
    obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hS
    have hgammaGamma : gamma∈Gamma := P.good_subset hgamma
    apply (leaf.agreement_card gamma hgammaGamma).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i,(P.scalar_data gamma hgamma).2.2.2 i hi⟩
  · exact hlarge

#print axioms sharp_scalar_allowance_ge_133227

end
end ProximityPrize.SubmissionLower.TwoSourceSharpScalarEndpointW133226Adapter6900
