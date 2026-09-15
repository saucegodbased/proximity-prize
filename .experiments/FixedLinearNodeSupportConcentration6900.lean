import ScalarFixedCommonNodesExactJohnson6900
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic

/-!
The fixed affine node equation left by the weighted low-window scalarization.

At a node used by seed `gamma`, write the evaluated residual identity as

`row0 i + gamma * row1 i = 0`.

Outside the simultaneous zero set of the two rows, a node belongs to the
support of at most one seed.  Thus deleting at most the complement of that
zero set leaves a whole family whose supports lie in the zero set.  The exact
mass Johnson inequality can then be applied on that shortened universe.
-/
namespace ProximityPrize.SubmissionLower.FixedLinearNodeSupportConcentration6900

open ProximityPrize.SubmissionLower.ScalarFixedCommonNodesExactJohnson6900
open ProximityPrize.SubmissionLower.ScalarShortenedJohnsonCommonCap6900
open Polynomial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

noncomputable section
local instance {T : Type*} : DecidableEq T := Classical.decEq T

variable {K I : Type*} [Field K]

def identityNodes (nodes : Finset I) (row0 row1 : I → K) : Finset I :=
  nodes.filter (fun i ↦ row0 i = 0 ∧ row1 i = 0)

def supportCore (Gamma : Finset K) (support : K → Finset I)
    (Z : Finset I) : Finset K :=
  Gamma.filter (fun gamma ↦ support gamma ⊆ Z)

theorem escape_card_le_identity_complement
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0) :
    (Gamma \ supportCore Gamma support (identityNodes nodes row0 row1)).card ≤
      nodes.card - (identityNodes nodes row0 row1).card := by
  classical
  let Z := identityNodes nodes row0 row1
  let Core := supportCore Gamma support Z
  let Bad := Gamma \ Core
  have hZsub : Z ⊆ nodes := Finset.filter_subset _ _
  have hBadsub : Bad ⊆ Gamma := Finset.sdiff_subset
  have hwitness (gamma : {x // x ∈ Bad}) :
      ∃ i ∈ support gamma.val, i ∉ Z := by
    have hg : gamma.val ∈ Gamma := hBadsub gamma.property
    have hnot : gamma.val ∉ Core := (Finset.mem_sdiff.mp gamma.property).2
    by_contra hnone
    have hsubset : support gamma.val ⊆ Z := by
      intro i hi
      by_contra hiZ
      exact hnone ⟨i, hi, hiZ⟩
    exact hnot (Finset.mem_filter.mpr ⟨hg, hsubset⟩)
  let witness : {x // x ∈ Bad} → I := fun gamma ↦
    Classical.choose (hwitness gamma)
  have hw (gamma : {x // x ∈ Bad}) :
      witness gamma ∈ support gamma.val ∧ witness gamma ∉ Z := by
    simpa only [witness] using Classical.choose_spec (hwitness gamma)
  have hBadcard : Bad.card ≤ (nodes \ Z).card := by
    have hh : Bad.attach.card ≤ (nodes \ Z).card := by
      apply Finset.card_le_card_of_injOn witness
      · intro gamma _
        exact Finset.mem_sdiff.mpr
          ⟨hnodes gamma.val (hBadsub gamma.property) (hw gamma).1, (hw gamma).2⟩
      · intro gamma _ eta _ heq
        have hgamma := hlinear gamma.val (hBadsub gamma.property)
          (witness gamma) (hw gamma).1
        have heta := hlinear eta.val (hBadsub eta.property)
          (witness eta) (hw eta).1
        have heta' : row0 (witness gamma) + eta.val * row1 (witness gamma) = 0 := by
          simpa only [heq] using heta
        have hrow1 : row1 (witness gamma) ≠ 0 := by
          intro hz
          have hrow0 : row0 (witness gamma) = 0 := by
            rw [hz, mul_zero, add_zero] at hgamma
            exact hgamma
          exact (hw gamma).2 (Finset.mem_filter.mpr
            ⟨hnodes gamma.val (hBadsub gamma.property) (hw gamma).1, hrow0, hz⟩)
        have hmul : (gamma.val - eta.val) * row1 (witness gamma) = 0 := by
          linear_combination hgamma - heta'
        apply Subtype.ext
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hrow1)
    simpa only [Finset.card_attach] using hh
  change Bad.card ≤ nodes.card - Z.card
  rw [← Finset.card_sdiff_of_subset hZsub]
  exact hBadcard

theorem support_core_johnson_bound
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K) (A W : ℕ) (hWA : W ≤ A)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0)
    (hmass : ∀ gamma ∈ Gamma, A ≤ (support gamma).card)
    (hpair : ∀ gamma ∈ Gamma, ∀ eta ∈ Gamma, gamma ≠ eta →
      ((support gamma) ∩ (support eta)).card ≤ W) :
    let Z := identityNodes nodes row0 row1
    let Core := supportCore Gamma support Z
    (Gamma \ Core).card ≤ nodes.card - Z.card ∧
      Core.card * (A ^ 2 - Z.card * W) ≤ Z.card * (A - W) := by
  classical
  dsimp only
  let Z := identityNodes nodes row0 row1
  let Core := supportCore Gamma support Z
  have hCsub : Core ⊆ Gamma := Finset.filter_subset _ _
  refine ⟨escape_card_le_identity_complement Gamma nodes support row0 row1
    hnodes hlinear, ?_⟩
  apply relation_johnson_bound_mass_at_least Core Z
    (fun gamma i ↦ i ∈ support gamma) A W hWA
  · intro gamma hgamma
    have hsupp : support gamma ⊆ Z := (Finset.mem_filter.mp hgamma).2
    have heq : Z.filter (fun i ↦ i ∈ support gamma) = support gamma := by
      ext i
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun hi ↦ hsupp hi)
    rw [heq]
    exact hmass gamma (hCsub hgamma)
  · intro gamma hgamma eta heta hne
    have heq : Z.filter (fun i ↦ i ∈ support gamma ∧ i ∈ support eta) =
        support gamma ∩ support eta := by
      have hgsub : support gamma ⊆ Z := (Finset.mem_filter.mp hgamma).2
      have hesub : support eta ⊆ Z := (Finset.mem_filter.mp heta).2
      ext i
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · exact fun hi ↦ ⟨hi.2.1, hi.2.2⟩
      · exact fun hi ↦ ⟨hgsub hi.1, hi.1, hi.2⟩
    rw [heq]
    exact hpair gamma (hCsub hgamma) eta (hCsub heta) hne

theorem scalar_support_pair_card_le
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (node centre : I → K) (scalar : K → K[X]) (W : ℕ)
    (hnode : Set.InjOn node nodes)
    (hscalar : Set.InjOn scalar (↑Gamma : Set K))
    (hdegree : ∀ gamma ∈ Gamma, (scalar gamma).natDegree ≤ W)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      (scalar gamma).eval (node i) = centre i) :
    ∀ gamma ∈ Gamma, ∀ eta ∈ Gamma, gamma ≠ eta →
      ((support gamma) ∩ (support eta)).card ≤ W := by
  classical
  intro gamma hgamma eta heta hne
  have hpoly : scalar gamma ≠ scalar eta := by
    intro heq
    exact hne (hscalar hgamma heta heq)
  apply (Finset.card_le_card ?_).trans
    (distinct_polynomial_common_agreements_card_le nodes node centre hnode
      (scalar gamma) (scalar eta) hpoly W
      (hdegree gamma hgamma) (hdegree eta heta))
  intro i hi
  obtain ⟨hig, hie⟩ := Finset.mem_inter.mp hi
  exact Finset.mem_filter.mpr
    ⟨hnodes gamma hgamma hig, hagrees gamma hgamma i hig,
      hagrees eta heta i hie⟩

theorem evaluated_residual_fixed_linear_equation
    (gamma E Q a b c d f U0 U1 : K)
    (hresidual : E * (U0 + gamma * U1) =
      a + gamma * b + Q * (c + gamma * d) * f) :
    (E * U0 - a - Q * c * f) + gamma * (E * U1 - b - Q * d * f) = 0 := by
  linear_combination hresidual

theorem polynomial_residual_node_equation
    (gamma x U0 U1 f : K) (E Q a b c d selected scalar : K[X])
    (hresidual : E * selected =
      a + C gamma * b + Q * (c + C gamma * d) * scalar)
    (hselected : selected.eval x = U0 + gamma * U1)
    (hscalar : scalar.eval x = f) :
    E.eval x * (U0 + gamma * U1) =
      a.eval x + gamma * b.eval x +
        Q.eval x * (c.eval x + gamma * d.eval x) * f := by
  have h := congrArg (fun P : K[X] ↦ P.eval x) hresidual
  simpa only [eval_mul, eval_add, eval_C, hselected, hscalar] using h

theorem cross_equation_of_identity_rows
    (E Q a b c d f U0 U1 N : K)
    (hrow0 : E * U0 - a - Q * c * f = 0)
    (hrow1 : E * U1 - b - Q * d * f = 0)
    (hdet : a * d - b * c = N) :
    E * (d * U0 - c * U1) = N := by
  rw [← hdet]
  linear_combination d * hrow0 - c * hrow1

/-! The fixed identity locus has no subgroup or interval structure by itself.
Even with unit `E,Q`, nonzero determinant, the residual equation on the locus,
and the cross equation on every node, it can be an arbitrary subset. -/
theorem arbitrary_subset_is_fixed_identity_locus
    (nodes Z : Finset I) (hZ : Z ⊆ nodes) :
    let U0 : I → K := fun i ↦ if i ∈ Z then 0 else 1
    let U1 : I → K := fun _ ↦ -1
    let E : I → K := fun _ ↦ 1
    let Q : I → K := fun _ ↦ 1
    let a : I → K := fun _ ↦ 0
    let b : I → K := fun _ ↦ -1
    let c : I → K := fun _ ↦ 1
    let d : I → K := fun _ ↦ 0
    let centre : I → K := fun _ ↦ 0
    let row0 := fun i ↦ E i * U0 i - a i - Q i * c i * centre i
    let row1 := fun i ↦ E i * U1 i - b i - Q i * d i * centre i
    identityNodes nodes row0 row1 = Z ∧
      (∀ gamma i, i ∈ Z → E i * (U0 i + gamma * U1 i) =
        a i + gamma * b i + Q i * (c i + gamma * d i) * centre i) ∧
      (∀ i, a i * d i - b i * c i = 1) ∧
      ∀ i, E i * (d i * U0 i - c i * U1 i) = 1 := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    by_cases hi : i ∈ Z
    · simp [identityNodes, hi, hZ hi]
    · simp [identityNodes, hi]
  · intro gamma i hi
    simp [hi]
  · intro i
    ring
  · intro i
    ring

theorem identity_product_ge_6900
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K) (W : ℕ)
    (hn : nodes.card = 262144)
    (hlarge : 253511670984674103 ≤ Gamma.card)
    (hWA : W ≤ 180413)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0)
    (hmass : ∀ gamma ∈ Gamma, 180413 ≤ (support gamma).card)
    (hpair : ∀ gamma ∈ Gamma, ∀ eta ∈ Gamma, gamma ≠ eta →
      ((support gamma) ∩ (support eta)).card ≤ W) :
    32548850569 ≤ (identityNodes nodes row0 row1).card * W := by
  classical
  let Z := identityNodes nodes row0 row1
  let Core := supportCore Gamma support Z
  obtain ⟨hescape, hjohnson⟩ := support_core_johnson_bound Gamma nodes support
    row0 row1 180413 W hWA hnodes hlinear hmass hpair
  have hCsub : Core ⊆ Gamma := Finset.filter_subset _ _
  have hsplit := Finset.card_sdiff_add_card_eq_card hCsub
  have hescape' : (Gamma \ Core).card ≤ 262144 := by
    calc
      (Gamma \ Core).card ≤ nodes.card - Z.card := hescape
      _ ≤ nodes.card := Nat.sub_le _ _
      _ = 262144 := hn
  have hcorelarge : 47294185472 < Core.card := by omega
  have hZcard : Z.card ≤ 262144 := by
    calc
      Z.card ≤ nodes.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 262144 := hn
  change 32548850569 ≤ Z.card * W
  by_contra hnot
  have hprodlt : Z.card * W < 32548850569 := Nat.lt_of_not_ge hnot
  have hsq : 180413 ^ 2 = 32548850569 := by norm_num
  rw [hsq] at hjohnson
  have hgap : 1 ≤ 32548850569 - Z.card * W := by omega
  have hself : Core.card ≤ Core.card * (32548850569 - Z.card * W) := by
    simpa only [mul_one] using Nat.mul_le_mul_left Core.card hgap
  have hright : Z.card * (180413 - W) ≤ 47294185472 := by
    calc
      Z.card * (180413 - W) ≤ Z.card * 180413 :=
        Nat.mul_le_mul_left Z.card (Nat.sub_le _ _)
      _ ≤ 262144 * 180413 := Nat.mul_le_mul_right 180413 hZcard
      _ = 47294185472 := by norm_num
  have hcoreupper : Core.card ≤ 47294185472 := hself.trans (hjohnson.trans hright)
  omega

theorem identity_card_ge_217317_6900
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K) (W : ℕ)
    (hn : nodes.card = 262144)
    (hlarge : 253511670984674103 ≤ Gamma.card)
    (hW : W ≤ 149776) (hWA : W ≤ 180413)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0)
    (hmass : ∀ gamma ∈ Gamma, 180413 ≤ (support gamma).card)
    (hpair : ∀ gamma ∈ Gamma, ∀ eta ∈ Gamma, gamma ≠ eta →
      ((support gamma) ∩ (support eta)).card ≤ W) :
    217317 ≤ (identityNodes nodes row0 row1).card := by
  have hprod := identity_product_ge_6900 Gamma nodes support row0 row1 W hn
    hlarge hWA hnodes hlinear hmass hpair
  by_contra hnot
  have hz : (identityNodes nodes row0 row1).card ≤ 217316 := by omega
  have hm := Nat.mul_le_mul hz hW
  norm_num at hm
  omega

theorem identity_card_ge_244508_at_W133120_6900
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K)
    (hn : nodes.card = 262144)
    (hlarge : 253511670984674103 ≤ Gamma.card)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0)
    (hmass : ∀ gamma ∈ Gamma, 180413 ≤ (support gamma).card)
    (hpair : ∀ gamma ∈ Gamma, ∀ eta ∈ Gamma, gamma ≠ eta →
      ((support gamma) ∩ (support eta)).card ≤ 133120) :
    244508 ≤ (identityNodes nodes row0 row1).card := by
  have hprod := identity_product_ge_6900 Gamma nodes support row0 row1 133120 hn
    hlarge (by norm_num) hnodes hlinear hmass hpair
  by_contra hnot
  have hz : (identityNodes nodes row0 row1).card ≤ 244507 := by omega
  have hm := Nat.mul_le_mul_right 133120 hz
  norm_num at hm
  omega

theorem escape_card_le_44827_of_identity_card_6900
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K)
    (hn : nodes.card = 262144)
    (hZ : 217317 ≤ (identityNodes nodes row0 row1).card)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0) :
    (Gamma \ supportCore Gamma support (identityNodes nodes row0 row1)).card ≤
      44827 := by
  have hescape := escape_card_le_identity_complement Gamma nodes support row0 row1
    hnodes hlinear
  omega

theorem escape_card_le_17636_of_identity_card_6900
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (row0 row1 : I → K)
    (hn : nodes.card = 262144)
    (hZ : 244508 ≤ (identityNodes nodes row0 row1).card)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0) :
    (Gamma \ supportCore Gamma support (identityNodes nodes row0 row1)).card ≤
      17636 := by
  have hescape := escape_card_le_identity_complement Gamma nodes support row0 row1
    hnodes hlinear
  omega

theorem scalar_residual_support_concentration_6900
    (Gamma : Finset K) (nodes : Finset I) (support : K → Finset I)
    (node centre : I → K) (scalar : K → K[X])
    (E Q a b c d U0 U1 : I → K) (W : ℕ)
    (hn : nodes.card = 262144)
    (hlarge : 253511670984674103 ≤ Gamma.card)
    (hW : W ≤ 149776)
    (hnode : Set.InjOn node nodes)
    (hscalar : Set.InjOn scalar (↑Gamma : Set K))
    (hdegree : ∀ gamma ∈ Gamma, (scalar gamma).natDegree ≤ W)
    (hnodes : ∀ gamma ∈ Gamma, support gamma ⊆ nodes)
    (hmass : ∀ gamma ∈ Gamma, 180413 ≤ (support gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      (scalar gamma).eval (node i) = centre i)
    (hresidual : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      E i * (U0 i + gamma * U1 i) =
        a i + gamma * b i + Q i * (c i + gamma * d i) * centre i) :
    let row0 := fun i ↦ E i * U0 i - a i - Q i * c i * centre i
    let row1 := fun i ↦ E i * U1 i - b i - Q i * d i * centre i
    let Z := identityNodes nodes row0 row1
    let Core := supportCore Gamma support Z
    217317 ≤ Z.card ∧ (Gamma \ Core).card ≤ 44827 := by
  classical
  dsimp only
  let row0 := fun i ↦ E i * U0 i - a i - Q i * c i * centre i
  let row1 := fun i ↦ E i * U1 i - b i - Q i * d i * centre i
  have hlinear : ∀ gamma ∈ Gamma, ∀ i ∈ support gamma,
      row0 i + gamma * row1 i = 0 := by
    intro gamma hgamma i hi
    exact evaluated_residual_fixed_linear_equation gamma (E i) (Q i) (a i) (b i)
      (c i) (d i) (centre i) (U0 i) (U1 i) (hresidual gamma hgamma i hi)
  have hpair := scalar_support_pair_card_le Gamma nodes support node centre scalar W
    hnode hscalar hdegree hnodes hagrees
  have hZ := identity_card_ge_217317_6900 Gamma nodes support row0 row1 W hn hlarge
    hW (hW.trans (by norm_num)) hnodes hlinear hmass hpair
  exact ⟨hZ, escape_card_le_44827_of_identity_card_6900 Gamma nodes support
    row0 row1 hn hZ hnodes hlinear⟩

#print axioms escape_card_le_identity_complement
#print axioms support_core_johnson_bound
#print axioms scalar_support_pair_card_le
#print axioms evaluated_residual_fixed_linear_equation
#print axioms polynomial_residual_node_equation
#print axioms cross_equation_of_identity_rows
#print axioms arbitrary_subset_is_fixed_identity_locus
#print axioms identity_product_ge_6900
#print axioms identity_card_ge_217317_6900
#print axioms identity_card_ge_244508_at_W133120_6900
#print axioms escape_card_le_44827_of_identity_card_6900
#print axioms escape_card_le_17636_of_identity_card_6900
#print axioms scalar_residual_support_concentration_6900

end
end ProximityPrize.SubmissionLower.FixedLinearNodeSupportConcentration6900
