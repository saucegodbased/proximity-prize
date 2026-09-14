import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# m69 first-defect rational two-power gate

This file isolates two facts needed before the proposed rational rescue can
be attached to the DataEleven leaf.

* In the no-wrap numerator regime, the square-channel dual relation already
  has zero kernel.  The exact sufficient cutoff is `deg N0 <= 129449`.
* Cancelling the common factor `B` at an NTT node is genuinely conditional on
  `B` being nonzero there.  A degree-`2049`, root-free denominator does not
  repair that logical gap.

The first theorem is a dual-kernel lemma, not by itself a construction of the
physical Full187 source map.
-/

namespace ProximityPrize.SubmissionLower.M69RationalTwoPowerGate6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Once cyclic congruence has been upgraded to a polynomial identity, the
coprime square relation forces the short dual numerator to vanish. -/
theorem short_square_relation_forces_zero
    {K : Type*} [Field K] (E N H H2 : K[X])
    (hcop : IsCoprime E N) (he : 2049 ≤ E.natDegree)
    (hH : H.natDegree < 3246)
    (hrelation : N ^ 2 * H = E ^ 2 * H2) :
    H = 0 := by
  have hE : E ≠ 0 := by
    intro hzero
    simp only [hzero, natDegree_zero] at he
    omega
  have hdiv : E ^ 2 ∣ N ^ 2 * H := by
    refine ⟨H2, ?_⟩
    rw [hrelation]
  have hEH : E ^ 2 ∣ H :=
    (show IsCoprime (E ^ 2) (N ^ 2) from hcop.pow).dvd_of_dvd_mul_left hdiv
  obtain ⟨T, rfl⟩ := hEH
  by_cases hT : T = 0
  · simp [hT]
  · have hdegree : (E ^ 2 * T).natDegree = 2 * E.natDegree + T.natDegree := by
      rw [natDegree_mul (pow_ne_zero 2 hE) hT, natDegree_pow]
    rw [hdegree] at hH
    omega

/-- The exact no-wrap sufficient regime for the first m69 defect.  Both
sides have degree below `262144`, so agreement at all NTT nodes is an honest
polynomial identity; coprimality and `2*2049 > 3245` then kill the dual
kernel. -/
theorem short_square_nodal_relation_forces_zero
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (hcard : Fintype.card I = 262144)
    (E N H H2 : K[X])
    (hcop : IsCoprime E N)
    (heLower : 2049 ≤ E.natDegree)
    (heUpper : E.natDegree ≤ 129449)
    (hnUpper : N.natDegree ≤ 129449)
    (hH : H.natDegree < 3246)
    (hH2 : H2.natDegree < 3244)
    (heval : ∀ i,
      (N ^ 2 * H).eval (nodes i) =
        (E ^ 2 * H2).eval (nodes i)) :
    H = 0 := by
  let F : K[X] := N ^ 2 * H - E ^ 2 * H2
  have hleft : (N ^ 2 * H).natDegree < 262144 := by
    calc
      (N ^ 2 * H).natDegree
          ≤ (N ^ 2).natDegree + H.natDegree := natDegree_mul_le
      _ ≤ 2 * N.natDegree + H.natDegree :=
        Nat.add_le_add_right natDegree_pow_le _
      _ < 262144 := by omega
  have hright : (E ^ 2 * H2).natDegree < 262144 := by
    calc
      (E ^ 2 * H2).natDegree
          ≤ (E ^ 2).natDegree + H2.natDegree := natDegree_mul_le
      _ ≤ 2 * E.natDegree + H2.natDegree :=
        Nat.add_le_add_right natDegree_pow_le _
      _ < 262144 := by omega
  have hFdegree : F.natDegree < 262144 := by
    exact (natDegree_sub_le _ _).trans_lt (max_lt hleft hright)
  have hFeval : ∀ i, F.eval (nodes i) = 0 := by
    intro i
    simp only [F, eval_sub, heval i, sub_self]
  have hFzero : F = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      F nodes.injective hFeval
    simpa only [hcard] using hFdegree
  have hrelation : N ^ 2 * H = E ^ 2 * H2 :=
    sub_eq_zero.mp (by simpa only [F] using hFzero)
  exact short_square_relation_forces_zero E N H H2 hcop heLower hH hrelation

/-- Exact arithmetic behind the no-wrap numerator threshold.  Raising the
cutoff by one permits degree `262145`, so this particular root-count proof no
longer applies. -/
theorem no_wrap_threshold_arithmetic :
    2 * 129449 + 3245 = 262143 ∧
    262144 ≤ 2 * 129450 + 3245 ∧
    3245 < 2 * 2049 := by
  norm_num

/-- The leaf grade and exact excess bound charge every possible common-factor
root.  Here `b` is `deg B`, `t=max(deg c,deg d)`, `q=deg Q`, and
`ell=max(deg L,deg M)`. -/
theorem common_factor_root_cost_arithmetic
    (b e t q ell j : Nat)
    (hgrade : b + e + t + ell = j)
    (hj : j ≤ 24932) (hexcess : t + q + 2049 ≤ e) :
    b + 2 * t + q + ell ≤ 22883 := by
  omega

/-- A nonzero common factor can hide the normalized cross on at most its
degree many injective evaluation nodes. -/
theorem nodal_root_card_le_natDegree
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I ↪ K) (B : K[X]) (hB : B ≠ 0) :
    ((Finset.univ : Finset I).filter
      (fun i ↦ B.eval (nodes i) = 0)).card ≤ B.natDegree := by
  let Z := (Finset.univ : Finset I).filter
    (fun i ↦ B.eval (nodes i) = 0)
  have hsubset : Z.image nodes ⊆ B.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hB).mpr (Finset.mem_filter.mp hi).2)
  calc
    Z.card = (Z.image nodes).card :=
      (Finset.card_image_iff.mpr nodes.injective.injOn).symm
    _ ≤ B.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ B.roots.card := Multiset.toFinset_card_le B.roots
    _ ≤ B.natDegree := Polynomial.card_roots' B

/-- Restriction of an all-coordinate word to a finite live set. -/
def restrictToFinset
    {I K : Type*} [Field K] (Live : Finset I) :
    (I → K) →ₗ[K] (↥Live → K) where
  toFun f i := f i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- If an ideal rational source is onto on all coordinates and the actual
source agrees with it on `Live`, then the actual source is onto after
restriction to `Live`.  No value at an omitted/common-factor root is used. -/
theorem live_restriction_surjective_of_agreement
    {I K V : Type*} [Fintype I] [Field K]
    [AddCommGroup V] [Module K V]
    (Live : Finset I) (ideal actual : V →ₗ[K] (I → K))
    (hideal : Function.Surjective ideal)
    (hagree : ∀ v i, i ∈ Live → actual v i = ideal v i) :
    Function.Surjective ((restrictToFinset Live).comp actual) := by
  classical
  intro y
  let yFull : I → K := fun i ↦
    if hi : i ∈ Live then y ⟨i, hi⟩ else 0
  obtain ⟨v, hv⟩ := hideal yFull
  refine ⟨v, ?_⟩
  funext i
  change actual v i.1 = y i
  rw [hagree v i.1 i.2, hv]
  simp only [yFull, dif_pos i.2]

/-- Exact worst-case extension cost: changing the source at `omitted`
coordinates can lose no more than `omitted.card` ranks.  This is the honest
conclusion available before an arbitrary-value robustness theorem is proved. -/
theorem full_rank_defect_le_omitted
    {I K V : Type*} [Fintype I] [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (Live omitted : Finset I)
    (ideal actual : V →ₗ[K] (I → K))
    (hpartition : Live.card + omitted.card = Fintype.card I)
    (hideal : Function.Surjective ideal)
    (hagree : ∀ v i, i ∈ Live → actual v i = ideal v i) :
    Fintype.card I - Module.finrank K (LinearMap.range actual) ≤
      omitted.card := by
  have hsurj := live_restriction_surjective_of_agreement
    Live ideal actual hideal hagree
  let factor : LinearMap.range actual →ₗ[K] (↥Live → K) :=
    (restrictToFinset Live).comp (LinearMap.range actual).subtype
  have hfactorSurj : Function.Surjective factor := by
    intro y
    obtain ⟨v, hv⟩ := hsurj y
    refine ⟨⟨actual v, ⟨v, rfl⟩⟩, ?_⟩
    exact hv
  have hrankMono := LinearMap.finrank_range_le factor
  rw [LinearMap.range_eq_top.mpr hfactorSurj, finrank_top K] at hrankMono
  have hdimLive : Module.finrank K (↥Live → K) = Live.card := by
    rw [Module.finrank_pi]
    simp
  have hliveRank : Live.card ≤
      Module.finrank K (LinearMap.range actual) := by
    simpa only [hdimLive] using hrankMono
  omega

/-- Cancellation of the factored cross is valid at, and only asserted at, a
node where the common factor is known nonzero. -/
theorem normalized_cross_at_nonroot
    {K : Type*} [Field K] (B E N : K[X]) (x z : K)
    (hB : B.eval x ≠ 0)
    (hcross : (B * E).eval x * z = (B * N).eval x) :
    E.eval x * z = N.eval x := by
  simp only [eval_mul] at hcross
  apply mul_left_cancel₀ hB
  simpa only [mul_assoc] using hcross

/-- Smallest hostile control for the all-node adapter.  The denominator has
exact degree `2049`, is nonzero at every nonzero node, and is coprime to the
numerator.  At the single root of `B`, however, the factored cross is vacuous
and the normalized rational identity can be false. -/
theorem factored_cross_vacuous_at_one_B_root
    {K : Type*} [Field K] (x : K) (hx : x ≠ 0) :
    let B : K[X] := X - C x
    let E : K[X] := X ^ 2049
    let N : K[X] := 1
    let z : K := 0
    B ≠ 0 ∧ E.natDegree = 2049 ∧ IsCoprime E N ∧
      (∀ y : K, y ≠ 0 → E.eval y ≠ 0) ∧
      E.eval x ≠ 0 ∧ B.eval x = 0 ∧
      (B * E).eval x * z = (B * N).eval x ∧
      E.eval x * z ≠ N.eval x := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact X_sub_C_ne_zero x
  · simp
  · exact isCoprime_one_right
  · intro y hy
    simp [hy]
  · simp [hx]
  · simp
  · simp
  · simp

#print axioms short_square_relation_forces_zero
#print axioms short_square_nodal_relation_forces_zero
#print axioms no_wrap_threshold_arithmetic
#print axioms common_factor_root_cost_arithmetic
#print axioms nodal_root_card_le_natDegree
#print axioms live_restriction_surjective_of_agreement
#print axioms full_rank_defect_le_omitted
#print axioms normalized_cross_at_nonroot
#print axioms factored_cross_vacuous_at_one_B_root

end
end ProximityPrize.SubmissionLower.M69RationalTwoPowerGate6900
