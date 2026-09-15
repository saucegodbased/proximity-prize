import FixedLinearNodeSupportConcentration6900

/-!
# Exact two-exception identity-node split

If the fixed affine node equation is nonzero at a node, that node belongs to
the support of at most one scalar seed.  At the cutoff `|Z| ≤ 262142`, this
leaves a full-support core large enough for the shortened W133225 list count.
The complementary branch has at most one nonidentity node.
-/
namespace ProximityPrize.SubmissionLower.IdentityNode2Dichotomy6900

open FixedLinearNodeSupportConcentration6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000

noncomputable section
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem identity_node_2_dichotomy
    {K I : Type*} [Field K]
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K)
    (hnodesCard : nodes.card = 262144)
    (hlarge : 263611557201785350 ≤ Gamma.card)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0) :
    let z := identityNodes nodes row0 row1
    let core := supportCore Gamma support z
    (z.card ≤ 262142 ∧
      263611557201523206 ≤ core.card ∧
      core ⊆ Gamma ∧
      ∀ gamma ∈ core, support gamma ⊆ z) ∨
      262143 ≤ z.card := by
  classical
  let z := identityNodes nodes row0 row1
  let core := supportCore Gamma support z
  change (z.card ≤ 262142 ∧
      263611557201523206 ≤ core.card ∧
      core ⊆ Gamma ∧
      ∀ gamma ∈ core, support gamma ⊆ z) ∨
      262143 ≤ z.card
  have hescape : (Gamma \ core).card ≤ nodes.card - z.card := by
    simpa only [z, core] using
      (escape_card_le_identity_complement Gamma nodes support row0 row1
        hnodes hlinear)
  have hcoreSub : core ⊆ Gamma := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).1
  have hsplit : (Gamma \ core).card + core.card = Gamma.card :=
    Finset.card_sdiff_add_card_eq_card hcoreSub
  have hescapeCoarse : (Gamma \ core).card ≤ 262144 := by
    calc
      (Gamma \ core).card ≤ nodes.card - z.card := hescape
      _ ≤ nodes.card := Nat.sub_le _ _
      _ = 262144 := hnodesCard
  have hcoreCard : 263611557201523206 ≤ core.card := by omega
  have hcoreSupport : ∀ gamma ∈ core, support gamma ⊆ z := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  by_cases hsmall : z.card ≤ 262142
  · exact Or.inl ⟨hsmall, hcoreCard, hcoreSub, hcoreSupport⟩
  · exact Or.inr (by omega)

#print axioms identity_node_2_dichotomy

end
end ProximityPrize.SubmissionLower.IdentityNode2Dichotomy6900
