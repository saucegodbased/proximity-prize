import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Near-total identity produces a syndrome dependence, not transversality

This is the small, source-independent algebraic kernel of the exact
`W = 133225` cutoff-two hard branch.  In that branch every target node but
possibly one satisfies the fixed affine row identity.  After the exact
division `centre = r + E * beta` and
`a + gamma*b + Q*(c+gamma*d)*r = E*t`, that identity says pointwise

`originalError = q(node) * quotientError`

away from the sole exceptional node, where `deg q <= 8328`.  The theorem
below expands this statement into Hankel/syndrome rows.  Consequently the
49341 original rows add no independent directions beyond shifted quotient
rows and one geometric exceptional-node row: their joint span has at most
`49341 + 8328 + 1 = 57670` generators, strictly fewer than the 81732 columns.

Thus the proposed 81732-column joint original/quotient minor is identically
singular on this branch.  Near-global identity cannot supply the missing
transversality assumption; it supplies an explicit rational kernel instead.
-/
namespace ProximityPrize.SubmissionLower.NearTotalIdentitySharpFrontierStop6900

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators
open Polynomial

noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Weighted power syndrome of a word on a finite node set. -/
def syndrome {K I : Type*} [CommRing K] [Fintype I]
    (node weight word : I → K) (k : Nat) : K :=
  ∑ i, weight i * word i * node i ^ k

/-- A Hankel row is a consecutive window of syndromes. -/
def hankelRow {K I : Type*} [CommRing K] [Fintype I]
    (columns : Nat) (node weight word : I → K) (k : Nat) : Fin columns → K :=
  fun j ↦ syndrome node weight word (k + j.val)

/-- The row contributed by an error supported at one node. -/
def geometricRow {K : Type*} [CommRing K]
    (columns : Nat) (x : K) : Fin columns → K :=
  fun j ↦ x ^ j.val

/-- Pointwise algebra behind the hard-branch gauge.  This is the evaluated
form of the fixed identity row, exact division of the centre and selected
polynomial, and root-freeness of `E` at the node. -/
theorem identity_division_error_gauge
    {K : Type*} [Field K]
    (E q base U centre r beta t P C : K)
    (hE : E ≠ 0)
    (hidentity : E * U = base + q * centre)
    (hcentre : centre = r + E * beta)
    (hbase : base + q * r = E * t)
    (hselected : P = t + q * C) :
    U - P = q * (beta - C) := by
  apply sub_eq_zero.mp
  have hmul : E * ((U - P) - q * (beta - C)) = 0 := by
    rw [hselected]
    linear_combination hidentity + hbase + q * hcentre
  exact (mul_eq_zero.mp hmul).resolve_left hE

/-- Exact syndrome convolution when multiplication by a polynomial of degree
at most `s` holds away from one exceptional coordinate. -/
theorem syndrome_convolution_single_exception
    {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    (s : Nat) (node weight original quotient : I → K)
    (coeff : Nat → K) (exception : I) (spike : K)
    (hpoint : ∀ i,
      original i =
        (∑ t ∈ Finset.range (s + 1), coeff t * node i ^ t) * quotient i +
          if i = exception then spike else 0)
    (k : Nat) :
    syndrome node weight original k =
      ∑ t ∈ Finset.range (s + 1),
        coeff t * syndrome node weight quotient (k + t) +
      weight exception * spike * node exception ^ k := by
  classical
  unfold syndrome
  simp_rw [hpoint]
  simp_rw [mul_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · have hdistrib : ∀ i : I,
        weight i *
            ((∑ t ∈ Finset.range (s + 1), coeff t * node i ^ t) * quotient i) *
              node i ^ k =
          ∑ t ∈ Finset.range (s + 1),
            coeff t * (weight i * quotient i * node i ^ (k + t)) := by
      intro i
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      rw [pow_add]
      ring
    simp_rw [hdistrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mul_sum]
  · simp

/-- Row-vector form of `syndrome_convolution_single_exception`.  All original
Hankel rows lie in shifted quotient rows plus one fixed geometric direction. -/
theorem hankelRow_convolution_single_exception
    {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    (columns s : Nat) (node weight original quotient : I → K)
    (coeff : Nat → K) (exception : I) (spike : K)
    (hpoint : ∀ i,
      original i =
        (∑ t ∈ Finset.range (s + 1), coeff t * node i ^ t) * quotient i +
          if i = exception then spike else 0)
    (k : Nat) :
    hankelRow columns node weight original k =
      (∑ t ∈ Finset.range (s + 1),
        coeff t • hankelRow columns node weight quotient (k + t)) +
      (weight exception * spike * node exception ^ k) •
        geometricRow columns (node exception) := by
  funext j
  rw [show hankelRow columns node weight original k j =
      syndrome node weight original (k + j.val) by rfl]
  rw [syndrome_convolution_single_exception s node weight original quotient
    coeff exception spike hpoint (k + j.val)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    hankelRow, geometricRow]
  rw [pow_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    congr 2
    omega
  · ring

/-- A reusable finite-generator rank gate.  This avoids hiding the decisive
dimension loss behind a determinant computation. -/
theorem finite_generator_span_finrank_le
    {K V A B : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype B]
    (rows : A → V) (generators : B → V)
    (hrows : ∀ a, rows a ∈ Submodule.span K (Set.range generators)) :
    Module.finrank K (Submodule.span K (Set.range rows)) ≤ Fintype.card B := by
  classical
  calc
    Module.finrank K (Submodule.span K (Set.range rows)) ≤
        Module.finrank K (Submodule.span K (Set.range generators)) := by
      apply Submodule.finrank_mono
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact hrows a
    _ ≤ Fintype.card B := finrank_range_le_card generators

/-- Hence a family carried by fewer generators than the ambient finite
dimension cannot span the whole ambient space. -/
theorem finite_generator_span_ne_top
    {K V A B : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype B]
    (rows : A → V) (generators : B → V)
    (hrows : ∀ a, rows a ∈ Submodule.span K (Set.range generators))
    (hsmall : Fintype.card B < Module.finrank K V) :
    Submodule.span K (Set.range rows) ≠ ⊤ := by
  intro htop
  have hle := finite_generator_span_finrank_le rows generators hrows
  rw [htop, finrank_top] at hle
  omega

/-- The joint original/quotient Hankel family used by the proposed rational
carrier. -/
def jointHankelRows {K I : Type*} [CommRing K] [Fintype I]
    (originalRows quotientRows columns : Nat)
    (node weight original quotient : I → K) :
    (Fin originalRows ⊕ Fin quotientRows) → (Fin columns → K)
  | Sum.inl k => hankelRow columns node weight original k.val
  | Sum.inr k => hankelRow columns node weight quotient k.val

/-- Quotient shifts plus the sole exceptional geometric row. -/
def nearIdentityCarrierRows {K I : Type*} [CommRing K] [Fintype I]
    (originalRows columns s : Nat) (node weight quotient : I → K)
    (exception : I) :
    (Fin (originalRows + s) ⊕ Fin 1) → (Fin columns → K)
  | Sum.inl k => hankelRow columns node weight quotient k.val
  | Sum.inr _ => geometricRow columns (node exception)

/-- End-to-end STOP theorem for the candidate joint minor.  If the pointwise
error relation has at most one exceptional node, the joint Hankel rows cannot
span all columns whenever `originalRows + s + 1 < columns`. -/
theorem near_total_identity_joint_hankel_span_ne_top
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (originalRows quotientRows columns s : Nat)
    (node weight original quotient : I → K)
    (coeff : Nat → K) (exception : I) (spike : K)
    (hpoint : ∀ i,
      original i =
        (∑ t ∈ Finset.range (s + 1), coeff t * node i ^ t) * quotient i +
          if i = exception then spike else 0)
    (hquotient : quotientRows ≤ originalRows + s)
    (hcolumns : originalRows + s + 1 < columns) :
    Submodule.span K (Set.range
      (jointHankelRows originalRows quotientRows columns
        node weight original quotient)) ≠ ⊤ := by
  apply finite_generator_span_ne_top
    (jointHankelRows originalRows quotientRows columns
      node weight original quotient)
    (nearIdentityCarrierRows originalRows columns s node weight quotient exception)
  · intro row
    rcases row with k | k
    · rw [jointHankelRows,
        hankelRow_convolution_single_exception columns s node weight original
          quotient coeff exception spike hpoint k.val]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro t ht
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨Sum.inl ⟨k.val + t, ?_⟩, rfl⟩
        have ht' : t < s + 1 := Finset.mem_range.mp ht
        omega
      · apply Submodule.smul_mem
        apply Submodule.subset_span
        exact ⟨Sum.inr ⟨0, by omega⟩, rfl⟩
    · apply Submodule.subset_span
      refine ⟨Sum.inl ⟨k.val, ?_⟩, rfl⟩
      exact lt_of_lt_of_le k.isLt hquotient
  · simpa only [Fintype.card_sum, Fintype.card_fin, Module.finrank_pi,
      Module.finrank_self, Nat.mul_one] using hcolumns

/-- Literal endpoint specialization: the 81732-column joint matrix is forced
to be singular, with a 24062-dimensional row deficit before any accidental
dependencies among the listed generators. -/
theorem endpoint_joint_hankel_span_ne_top
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (node weight original quotient : I → K)
    (coeff : Nat → K) (exception : I) (spike : K)
    (hpoint : ∀ i,
      original i =
        (∑ t ∈ Finset.range (8328 + 1), coeff t * node i ^ t) * quotient i +
          if i = exception then spike else 0) :
    Submodule.span K (Set.range
      (jointHankelRows 49341 32391 81732 node weight original quotient)) ≠ ⊤ := by
  exact near_total_identity_joint_hankel_span_ne_top
    49341 32391 81732 8328 node weight original quotient coeff exception spike
    hpoint (by norm_num) (by norm_num)

/-- The support cut out by a family of node-membership polynomials in the
seed.  This is the exact extra observable absent from the current leaf. -/
def algebraicSeedSupport {K I : Type*} [Field K]
    (nodes : Finset I) (membership : I → K[X]) (gamma : K) : Finset I :=
  nodes.filter fun i ↦ (membership i).eval gamma = 0

/-- Nodes whose membership polynomial is identically zero. -/
def fixedSeedSupportNodes {K I : Type*} [Field K]
    (nodes : Finset I) (membership : I → K[X]) : Finset I :=
  nodes.filter fun i ↦ membership i = 0

/-- Direct root-incidence count for node-membership polynomials. -/
theorem algebraic_seed_support_incidence
    {K I : Type*} [Field K]
    (Gamma : Finset K) (nodes : Finset I) (membership : I → K[X])
    (A d : Nat)
    (hmass : ∀ gamma ∈ Gamma,
      (algebraicSeedSupport nodes membership gamma).card = A)
    (hdegree : ∀ i ∈ nodes, (membership i).natDegree ≤ d) :
    let fixed := fixedSeedSupportNodes nodes membership
    Gamma.card * (A - fixed.card) ≤ (nodes.card - fixed.card) * d := by
  classical
  let fixed := fixedSeedSupportNodes nodes membership
  let moving := nodes \ fixed
  have hfixedSub : fixed ⊆ nodes := by
    exact Finset.filter_subset _ _
  have hfixedMem : ∀ gamma, fixed ⊆ algebraicSeedSupport nodes membership gamma := by
    intro gamma i hi
    have hi' := (Finset.mem_filter.mp hi)
    exact Finset.mem_filter.mpr ⟨hi'.1, by simp [hi'.2]⟩
  have hrow : ∀ gamma ∈ Gamma,
      A - fixed.card ≤
        (moving.filter fun i ↦ (membership i).eval gamma = 0).card := by
    intro gamma hgamma
    have heq :
        moving.filter (fun i ↦ (membership i).eval gamma = 0) =
          algebraicSeedSupport nodes membership gamma \ fixed := by
      ext i
      simp only [moving, algebraicSeedSupport, Finset.mem_filter,
        Finset.mem_sdiff]
      tauto
    rw [heq, Finset.card_sdiff_of_subset (hfixedMem gamma), hmass gamma hgamma]
  have hcolumn : ∀ i ∈ moving,
      (Gamma.filter fun gamma ↦ (membership i).eval gamma = 0).card ≤ d := by
    intro i hi
    have hiNodes : i ∈ nodes := (Finset.mem_sdiff.mp hi).1
    have hiNonzero : membership i ≠ 0 := by
      intro hz
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨hiNodes, hz⟩)
    have hroots :
        (Gamma.filter fun gamma ↦ (membership i).eval gamma = 0).card ≤
          (membership i).natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro gamma hgamma
      exact (Polynomial.mem_roots hiNonzero).mpr
        (Finset.mem_filter.mp hgamma).2
    exact hroots.trans (hdegree i hiNodes)
  calc
    Gamma.card * (A - fixed.card) =
        ∑ gamma ∈ Gamma, (A - fixed.card) := by simp
    _ ≤ ∑ gamma ∈ Gamma,
        (moving.filter fun i ↦ (membership i).eval gamma = 0).card := by
      exact Finset.sum_le_sum hrow
    _ = ∑ i ∈ moving,
        (Gamma.filter fun gamma ↦ (membership i).eval gamma = 0).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _i ∈ moving, d := Finset.sum_le_sum hcolumn
    _ = (nodes.card - fixed.card) * d := by
      simp [moving, Finset.card_sdiff_of_subset hfixedSub]

/-- A bounded-seed-degree locator would close the hard branch.  Exact support
mass plus support injectivity gives either one fixed support, or the root
incidence bound `|Gamma| ≤ |nodes|*d`. -/
theorem bounded_seed_degree_support_locator_gate
    {K I : Type*} [Field K]
    (Gamma : Finset K) (nodes : Finset I) (membership : I → K[X])
    (A d : Nat)
    (hmass : ∀ gamma ∈ Gamma,
      (algebraicSeedSupport nodes membership gamma).card = A)
    (hdegree : ∀ i ∈ nodes, (membership i).natDegree ≤ d)
    (hinjective : Set.InjOn
      (algebraicSeedSupport nodes membership) (↑Gamma : Set K)) :
    Gamma.card ≤ max 1 (nodes.card * d) := by
  classical
  by_cases hGamma : Gamma.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hGamma]
    simp
  let fixed := fixedSeedSupportNodes nodes membership
  have hfixedMem : ∀ gamma, fixed ⊆ algebraicSeedSupport nodes membership gamma := by
    intro gamma i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi'.1, by simp [hi'.2]⟩
  by_cases hsmall : fixed.card < A
  · have hincidence := algebraic_seed_support_incidence
      Gamma nodes membership A d hmass hdegree
    dsimp only at hincidence
    apply le_max_of_le_right
    calc
      Gamma.card ≤ Gamma.card * (A - fixed.card) := by
        have hpos : 1 ≤ A - fixed.card := by omega
        simpa only [mul_one] using Nat.mul_le_mul_left Gamma.card hpos
      _ ≤ (nodes.card - fixed.card) * d := hincidence
      _ ≤ nodes.card * d :=
        Nat.mul_le_mul_right d (Nat.sub_le nodes.card fixed.card)
  · have hfixedCard : fixed.card = A := by
      have hle : fixed.card ≤ A := by
        obtain ⟨gamma, hgamma⟩ := hGamma
        calc
          fixed.card ≤
              (algebraicSeedSupport nodes membership gamma).card :=
            Finset.card_le_card (hfixedMem gamma)
          _ = A := hmass gamma hgamma
      omega
    have hconstant : ∀ gamma ∈ Gamma,
        algebraicSeedSupport nodes membership gamma = fixed := by
      intro gamma hgamma
      apply Finset.Subset.antisymm
      · have hsameCard :
            (algebraicSeedSupport nodes membership gamma).card = fixed.card := by
          rw [hmass gamma hgamma, hfixedCard]
        exact (Finset.eq_of_subset_of_card_le
          (hfixedMem gamma) hsameCard.le).symm.subset
      · exact hfixedMem gamma
    apply le_max_of_le_left
    rw [Finset.card_le_one]
    intro gamma hgamma delta hdelta
    apply hinjective hgamma hdelta
    rw [hconstant gamma hgamma, hconstant delta hdelta]

/-- At the literal endpoint, any support-locator family whose node-membership
polynomials have seed degree at most `1005598286444` is too small. -/
theorem endpoint_bounded_seed_degree_locator_contradiction
    {K I : Type*} [Field K]
    (Gamma : Finset K) (nodes : Finset I) (membership : I → K[X])
    (hmass : ∀ gamma ∈ Gamma,
      (algebraicSeedSupport nodes membership gamma).card = 180413)
    (hdegree : ∀ i ∈ nodes,
      (membership i).natDegree ≤ 1005598286444)
    (hinjective : Set.InjOn
      (algebraicSeedSupport nodes membership) (↑Gamma : Set K))
    (hnodes : nodes.card = 262144)
    (hlarge : 263611557201785350 ≤ Gamma.card) : False := by
  have hcap := bounded_seed_degree_support_locator_gate Gamma nodes membership
    180413 1005598286444 hmass hdegree hinjective
  rw [hnodes] at hcap
  norm_num at hcap
  omega

/-- The exact generator count forced by the sharp endpoint parameters. -/
theorem near_total_joint_generator_count :
    49341 + 8328 + 1 = 57670 ∧
    32391 ≤ 49341 + 8328 ∧
    57670 < 81732 ∧
    81732 - 57670 = 24062 := by
  norm_num

/-- The cutoff-two enumerative branch closes with this exact positive margin;
the complementary hard branch therefore cannot be paid as an exception. -/
theorem cutoff_two_margin_receipt :
    263611557201785348 - 263611056734953625 = 500466831723 ∧
    263611056734953625 < 263611557201785348 := by
  norm_num

/-- Pair/triple agreement intersections remain below the selected degree, so
ordinary two- or three-seed root counting cannot close the hard branch. -/
theorem near_total_pair_triple_phase_receipt :
    2 * 180413 - 262144 = 98682 ∧
    3 * 180413 - 2 * 262144 = 16951 ∧
    98682 < 131072 ∧
    16951 < 131072 := by
  norm_num

#print axioms syndrome_convolution_single_exception
#print axioms identity_division_error_gauge
#print axioms hankelRow_convolution_single_exception
#print axioms finite_generator_span_finrank_le
#print axioms finite_generator_span_ne_top
#print axioms near_total_identity_joint_hankel_span_ne_top
#print axioms endpoint_joint_hankel_span_ne_top
#print axioms algebraic_seed_support_incidence
#print axioms bounded_seed_degree_support_locator_gate
#print axioms endpoint_bounded_seed_degree_locator_contradiction
#print axioms near_total_joint_generator_count
#print axioms cutoff_two_margin_receipt
#print axioms near_total_pair_triple_phase_receipt

end
end ProximityPrize.SubmissionLower.NearTotalIdentitySharpFrontierStop6900
