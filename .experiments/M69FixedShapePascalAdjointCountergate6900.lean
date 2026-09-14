import M69Full187PrefixDualSourceAdapter6900
import Mathlib.Tactic.Ring

/-!
# Literal fixed-shape Pascal adjoint for the m69 source

Fix one physical shape `(r,s,q)`.  If `y` is an output contact and `k` is a
source contact, the literal coefficient is

`choose k y * W^(k-y)`.

Consequently a tuple of output covectors `lambda_y` does **not** produce the
single-covector sequence `lambda * W^k`.  Its source-facing transpose is

`mu_k(i) = sum_{y in Y, y <= k} choose k y * W(i)^(k-y) * lambda_y(i)`.

This file proves the transpose pairing identity, extracts the honest short
RS dual polynomial for every `mu_k`, and proves a countergate: on the first
square block of consecutive contacts the Pascal transform is unit lower
triangular and hence surjective.  Thus prefix orthogonality alone cannot
force an adjacent rational recurrence between the extracted polynomials.
Later shared-tail and terminal contacts do give extra orthogonality equations,
but an adjacent recurrence requires the explicit correction to vanish; that
vanishing is not a consequence of the source definition proved here.
-/

namespace ProximityPrize.SubmissionLower.M69FixedShapePascalAdjointCountergate6900

open Polynomial
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Ordinary RS-prefix orthogonality of one source-facing covector. -/
def PrefixOrthogonal
    {I K : Type*} [Fintype I] [Field K]
    (nodes : I -> K) (mu : I -> K) (f : Nat) : Prop :=
  forall P : K[X], P.natDegree < f ->
    (∑ i, mu i * P.eval (nodes i)) = 0

/-- Literal output at contact `y` of a finite fixed-shape Pascal source. -/
def fixedShapeSourceOutput
    {I K : Type*} [CommRing K]
    (sources : Finset Nat) (W : I -> K) (u : Nat -> I -> K)
    (y : Nat) (i : I) : K :=
  ∑ k ∈ sources,
    if y <= k then
      (Nat.choose k y : K) * W i ^ (k - y) * u k i
    else 0

/-- The exact source-facing transpose of a tuple of output covectors. -/
def fixedShapeAdjoint
    {I K : Type*} [CommRing K]
    (outputs : Finset Nat) (W : I -> K) (lambda : Nat -> I -> K)
    (k : Nat) (i : I) : K :=
  ∑ y ∈ outputs,
    if y <= k then
      (Nat.choose k y : K) * W i ^ (k - y) * lambda y i
    else 0

/-- The finite Pascal formula above is exactly the transpose of the literal
fixed-shape source at each evaluation node. -/
theorem fixedShape_pairing_at_node
    {I K : Type*} [CommRing K]
    (outputs sources : Finset Nat) (W : I -> K)
    (lambda u : Nat -> I -> K) (i : I) :
    (∑ y ∈ outputs,
        lambda y i * fixedShapeSourceOutput sources W u y i) =
      ∑ k ∈ sources, fixedShapeAdjoint outputs W lambda k i * u k i := by
  simp only [fixedShapeSourceOutput, fixedShapeAdjoint, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyk : y <= k
  · simp only [hyk, if_true]
    ring
  · simp only [hyk, if_false, mul_zero, zero_mul]

/-- Global transpose identity, including the sum over all NTT nodes. -/
theorem fixedShape_pairing
    {I K : Type*} [Fintype I] [CommRing K]
    (outputs sources : Finset Nat) (W : I -> K)
    (lambda u : Nat -> I -> K) :
    (∑ y ∈ outputs, ∑ i,
        lambda y i * fixedShapeSourceOutput sources W u y i) =
      ∑ k ∈ sources, ∑ i,
        fixedShapeAdjoint outputs W lambda k i * u k i := by
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ y ∈ outputs,
        lambda y i * fixedShapeSourceOutput sources W u y i) =
        ∑ i, ∑ k ∈ sources,
          fixedShapeAdjoint outputs W lambda k i * u k i := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact fixedShape_pairing_at_node outputs sources W lambda u i
    _ = ∑ k ∈ sources, ∑ i,
          fixedShapeAdjoint outputs W lambda k i * u k i := by
            rw [Finset.sum_comm]

/-- An annihilator of the literal fixed-shape polynomial-prefix source.  The
polynomial at each source contact is independently selectable. -/
def FixedShapeSourceAnnihilator
    {I K : Type*} [Fintype I] [Field K]
    (outputs sources : Finset Nat) (nodes W : I -> K)
    (lambda : Nat -> I -> K) (cap : Nat -> Nat) : Prop :=
  forall P : Nat -> K[X],
    (forall k, k ∈ sources -> (P k).natDegree < cap k) ->
    (∑ y ∈ outputs, ∑ i,
      lambda y i * fixedShapeSourceOutput sources W
        (fun k i => (P k).eval (nodes i)) y i) = 0

/-- Source annihilation is equivalent to prefix orthogonality of every
Pascal-adjoint covector.  Positivity of each cap is needed only to use zero
polynomials while isolating one source contact. -/
theorem fixedShapeSourceAnnihilator_iff_adjoint_prefixes
    {I K : Type*} [Fintype I] [Field K]
    (outputs sources : Finset Nat) (nodes W : I -> K)
    (lambda : Nat -> I -> K) (cap : Nat -> Nat)
    (hcapPos : forall k, k ∈ sources -> 0 < cap k) :
    FixedShapeSourceAnnihilator outputs sources nodes W lambda cap <->
      forall k, k ∈ sources ->
        PrefixOrthogonal nodes (fixedShapeAdjoint outputs W lambda k) (cap k) := by
  constructor
  · intro hann k hk P hP
    let selected : Nat -> K[X] := fun j => if j = k then P else 0
    have hselected : forall j, j ∈ sources ->
        (selected j).natDegree < cap j := by
      intro j hj
      by_cases hjk : j = k
      · subst j
        simpa only [selected, if_pos] using hP
      · simp only [selected, if_neg hjk, natDegree_zero]
        exact hcapPos j hj
    have h := hann selected hselected
    rw [fixedShape_pairing outputs sources W lambda
      (fun j i => (selected j).eval (nodes i))] at h
    have heval : forall j i,
        (selected j).eval (nodes i) =
          if j = k then P.eval (nodes i) else 0 := by
      intro j i
      simp only [selected]
      split <;> simp_all
    simp_rw [heval] at h
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', hk, if_true] at h
    exact h
  · intro hadj P hP
    rw [fixedShape_pairing outputs sources W lambda
      (fun k i => (P k).eval (nodes i))]
    apply Finset.sum_eq_zero
    intro k hk
    exact hadj k hk (P k) (hP k hk)

/-- Every source contact has its own unique short dual polynomial.  This is
the valid prefix-dual conclusion for the literal Pascal source. -/
theorem exists_fixedShape_pascal_duals
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (outputs sources : Finset Nat) (W : D.Idx -> K)
    (lambda : Nat -> D.Idx -> K) (cap : Nat -> Nat)
    (hcapPos : forall k, k ∈ sources -> 0 < cap k)
    (hcap : forall k, k ∈ sources -> cap k < D.n)
    (hann : FixedShapeSourceAnnihilator outputs sources D.node W lambda cap) :
    exists H : Nat -> K[X], forall k, k ∈ sources ->
      (H k).natDegree < D.n - cap k ∧
      forall i, fixedShapeAdjoint outputs W lambda k i =
        D.node i * (H k).eval (D.node i) := by
  have hadj :=
    (fixedShapeSourceAnnihilator_iff_adjoint_prefixes
      outputs sources D.node W lambda cap hcapPos).mp hann
  let witness : forall k, k ∈ sources ->
      exists H : K[X], H.natDegree < D.n - cap k ∧
        forall i, fixedShapeAdjoint outputs W lambda k i =
          D.node i * H.eval (D.node i) := fun k hk =>
    M69Full187PrefixDualSourceAdapter6900.exists_ntt_prefix_dual D
      (fixedShapeAdjoint outputs W lambda k) (cap k) (hcap k hk) (by
        intro j hj
        have hmoment := hadj k hk ((Polynomial.X : K[X]) ^ j)
          (by simpa only [natDegree_X_pow] using hj)
        simpa only [eval_pow, eval_X] using hmoment)
  let H : Nat -> K[X] := fun k =>
    if hk : k ∈ sources then Classical.choose (witness k hk) else 0
  refine ⟨H, ?_⟩
  intro k hk
  simpa only [H, dif_pos hk] using Classical.choose_spec (witness k hk)

/-- First-square-block form of the Pascal transpose.  Contact `h` means the
absolute source contact `a+h`, while `d` indexes output contact `a+d`. -/
def prefixPascalAdjointFrom
    {I K : Type*} [CommRing K]
    (a : Nat) (W : I -> K) (lambda : Nat -> I -> K)
    (h : Nat) (i : I) : K :=
  ∑ d ∈ Finset.range (h + 1),
    (Nat.choose (a + h) (a + d) : K) *
      W i ^ (h - d) * lambda d i

/-- The first consecutive square block is unit lower triangular: every
prescribed family `mu_0,...,mu_(m-1)` has an output-covector preimage. -/
theorem exists_prefixPascalAdjointFrom_preimage
    {I K : Type*} [Field K]
    (a : Nat) (W : I -> K) (mu : Nat -> I -> K) (m : Nat) :
    exists lambda : Nat -> I -> K, forall h, h < m -> forall i,
      prefixPascalAdjointFrom a W lambda h i = mu h i := by
  induction m with
  | zero =>
      exact ⟨fun _ _ => 0, by intro h hh; omega⟩
  | succ m ih =>
      obtain ⟨lambda, hlambda⟩ := ih
      let lower : I -> K := fun i =>
        ∑ d ∈ Finset.range m,
          (Nat.choose (a + m) (a + d) : K) *
            W i ^ (m - d) * lambda d i
      let lambda' : Nat -> I -> K := fun d i =>
        if d = m then mu m i - lower i else lambda d i
      refine ⟨lambda', ?_⟩
      intro h hh i
      by_cases hhm : h = m
      · subst h
        rw [prefixPascalAdjointFrom, Finset.sum_range_succ]
        have hlower :
            (∑ d ∈ Finset.range m,
              (Nat.choose (a + m) (a + d) : K) *
                W i ^ (m - d) * lambda' d i) = lower i := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdm : d ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hd)
          simp only [lambda', if_neg hdm]
        rw [hlower]
        simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
          pow_zero, one_mul, lambda', if_pos]
        ring
      · have hlt : h < m := by omega
        rw [prefixPascalAdjointFrom]
        calc
          (∑ d ∈ Finset.range (h + 1),
              (Nat.choose (a + h) (a + d) : K) *
                W i ^ (h - d) * lambda' d i) =
              ∑ d ∈ Finset.range (h + 1),
                (Nat.choose (a + h) (a + d) : K) *
                  W i ^ (h - d) * lambda d i := by
                    apply Finset.sum_congr rfl
                    intro d hd
                    have hdle : d <= h := by
                      have := Finset.mem_range.mp hd
                      omega
                    have hdm : d ≠ m := by omega
                    simp only [lambda', if_neg hdm]
          _ = mu h i := hlambda h hlt i

/-- In particular, the first two Pascal-adjoint covectors can be prescribed
independently.  No adjacent relation follows from the triangular source
transpose itself. -/
theorem first_two_pascal_adjoints_surjective
    {I K : Type*} [Field K]
    (a : Nat) (W : I -> K) (mu0 mu1 : I -> K) :
    exists lambda : Nat -> I -> K,
      (forall i, prefixPascalAdjointFrom a W lambda 0 i = mu0 i) ∧
      (forall i, prefixPascalAdjointFrom a W lambda 1 i = mu1 i) := by
  obtain ⟨lambda, h⟩ :=
    exists_prefixPascalAdjointFrom_preimage a W
      (fun k => if k = 0 then mu0 else mu1) 2
  refine ⟨lambda, ?_, ?_⟩
  · intro i
    simpa only [if_pos] using h 0 (by omega) i
  · intro i
    simpa only [if_neg (by omega : (1 : Nat) ≠ 0)] using h 1 (by omega) i

/-- Exact first adjacent formula.  The correction is
`a*W*lambda_0 + lambda_1`, so even the first step is not multiplication by
`W` unless this additional covector identity is proved. -/
theorem first_pascal_adjacent_correction
    {I K : Type*} [Field K]
    (a : Nat) (W : I -> K) (lambda : Nat -> I -> K) (i : I) :
    prefixPascalAdjointFrom a W lambda 1 i =
      W i * prefixPascalAdjointFrom a W lambda 0 i +
        (a : K) * W i * lambda 0 i + lambda 1 i := by
  simp only [prefixPascalAdjointFrom, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Nat.choose_self, Nat.cast_one,
    one_mul, Nat.sub_self, pow_zero, Nat.add_zero]
  rw [Nat.choose_succ_self_right]
  push_cast
  ring

/-- The exact extra condition needed to recover the first adjacent
`mu_1=W*mu_0` relation.  The literal source definition supplies no such
vanishing equation by itself. -/
theorem first_pascal_adjacent_iff_correction_zero
    {I K : Type*} [Field K]
    (a : Nat) (W : I -> K) (lambda : Nat -> I -> K) :
    (forall i, prefixPascalAdjointFrom a W lambda 1 i =
      W i * prefixPascalAdjointFrom a W lambda 0 i) <->
    (forall i, (a : K) * W i * lambda 0 i + lambda 1 i = 0) := by
  constructor <;> intro h i
  · have hformula := first_pascal_adjacent_correction a W lambda i
    have heq := h i
    rw [hformula] at heq
    linear_combination heq
  · rw [first_pascal_adjacent_correction a W lambda i]
    linear_combination h i

/-- A concrete algebraic counterexample to automatic adjacent coupling. -/
theorem first_pascal_adjacent_not_automatic
    {K : Type*} [Field K] (a : Nat) (w : K) :
    let W : Fin 1 -> K := fun _ => w
    let lambda : Nat -> Fin 1 -> K := fun d _ => if d = 1 then 1 else 0
    prefixPascalAdjointFrom a W lambda 0 0 = 0 ∧
      prefixPascalAdjointFrom a W lambda 1 0 = 1 ∧
      prefixPascalAdjointFrom a W lambda 1 0 ≠
        W 0 * prefixPascalAdjointFrom a W lambda 0 0 := by
  dsimp
  simp [prefixPascalAdjointFrom]

/-- Full finite-output correction between two consecutive source-facing
Pascal adjoints.  Tail/terminal constraints restore the old recurrence only
if they imply that this function vanishes. -/
def fixedShapeAdjacentCorrection
    {I K : Type*} [CommRing K]
    (outputs : Finset Nat) (W : I -> K) (lambda : Nat -> I -> K)
    (k : Nat) (i : I) : K :=
  fixedShapeAdjoint outputs W lambda (k + 1) i -
    W i * fixedShapeAdjoint outputs W lambda k i

theorem fixedShape_adjacent_eq_mul_iff_correction_zero
    {I K : Type*} [CommRing K]
    (outputs : Finset Nat) (W : I -> K) (lambda : Nat -> I -> K)
    (k : Nat) :
    (forall i, fixedShapeAdjoint outputs W lambda (k + 1) i =
      W i * fixedShapeAdjoint outputs W lambda k i) <->
    (forall i, fixedShapeAdjacentCorrection outputs W lambda k i = 0) := by
  simp only [fixedShapeAdjacentCorrection, sub_eq_zero]

/-- Exact sufficient interface for recovering one rational adjacent relation
from two extracted Pascal adjoints.  The new, non-source premise is precisely
the vanishing of the Pascal correction. -/
theorem adjacent_relation_of_pascal_duals_of_correction_zero
    {K : Type*} [Field K]
    (D : CompPoly.CPolynomial.NTT.Domain K)
    (outputs : Finset Nat) (E N : K[X])
    (W : D.Idx -> K) (lambda : Nat -> D.Idx -> K) (k : Nat)
    (H Hnext : K[X])
    (hW : forall i, E.eval (D.node i) * W i = N.eval (D.node i))
    (hH : forall i, fixedShapeAdjoint outputs W lambda k i =
      D.node i * H.eval (D.node i))
    (hHnext : forall i, fixedShapeAdjoint outputs W lambda (k + 1) i =
      D.node i * Hnext.eval (D.node i))
    (hcorrection : forall i,
      fixedShapeAdjacentCorrection outputs W lambda k i = 0) :
    forall i, (N * H).eval (D.node i) =
      (E * Hnext).eval (D.node i) := by
  have hadj : forall i,
      fixedShapeAdjoint outputs W lambda (k + 1) i =
        W i * fixedShapeAdjoint outputs W lambda k i :=
    (fixedShape_adjacent_eq_mul_iff_correction_zero
      outputs W lambda k).mpr hcorrection
  intro i
  simp only [eval_mul]
  apply mul_left_cancel₀
    (M69Full187PrefixDualSourceAdapter6900.NTT.node_ne_zero D i)
  calc
    D.node i * (N.eval (D.node i) * H.eval (D.node i)) =
        N.eval (D.node i) *
          (D.node i * H.eval (D.node i)) := by ring
    _ = N.eval (D.node i) *
          fixedShapeAdjoint outputs W lambda k i := by rw [← hH i]
    _ = (E.eval (D.node i) * W i) *
          fixedShapeAdjoint outputs W lambda k i := by rw [hW i]
    _ = E.eval (D.node i) *
          fixedShapeAdjoint outputs W lambda (k + 1) i := by
            rw [hadj i]
            ring
    _ = E.eval (D.node i) *
          (D.node i * Hnext.eval (D.node i)) := by rw [hHnext i]
    _ = D.node i *
          (E.eval (D.node i) * Hnext.eval (D.node i)) := by ring

#print axioms fixedShape_pairing_at_node
#print axioms fixedShape_pairing
#print axioms fixedShapeSourceAnnihilator_iff_adjoint_prefixes
#print axioms exists_fixedShape_pascal_duals
#print axioms exists_prefixPascalAdjointFrom_preimage
#print axioms first_two_pascal_adjoints_surjective
#print axioms first_pascal_adjacent_correction
#print axioms first_pascal_adjacent_iff_correction_zero
#print axioms first_pascal_adjacent_not_automatic
#print axioms fixedShape_adjacent_eq_mul_iff_correction_zero
#print axioms adjacent_relation_of_pascal_duals_of_correction_zero

end
end ProximityPrize.SubmissionLower.M69FixedShapePascalAdjointCountergate6900
