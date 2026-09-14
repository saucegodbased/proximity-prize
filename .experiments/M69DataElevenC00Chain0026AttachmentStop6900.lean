import DataElevenHighEClosedFrontier6900

/-!
# Exact DataEleven/C00 attachment gate for the m69 `(0,0,26)` chain

This file deliberately specializes all source indices.  The deficient output
contacts are `41,42`, the ordinary shared source contacts are `41,...,68`,
and the terminal contact is `94`.  The ordinary source at contact `k` has the
literal post-Hasse prefix

`(69*180413 - 131071*k) % 262144`,

while the terminal order-26 coefficient has prefix `127823-26=127797`.

The actual attachment stops before it can be stated canonically:
`DataElevenHighEClosedLeaf` contains the polynomial `C00` and its all-node
semilinear equation, but the imported source language contains no extraction
mapping that datum to the order-26 terminal coefficient `C26`.  The
`DirectC00...Candidate` definitions below record the stronger illustrative
choice that the terminal word is directly the C00 nodal word; they are not
asserted to be the intended Full187 extraction.  No leaf field supplies even
that stronger candidate, nor an m69 source array realizing the simultaneous
two-row map.
-/

namespace ProximityPrize.SubmissionLower.M69DataElevenC00Chain0026AttachmentStop6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open DataElevenHighEClosedFrontier6900

open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The actual C00 equation immediately forces C00 to vanish at a root of
the stored (unfactored) denominator. -/
theorem c00_vanishes_at_cross_E_root
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (i : Index)
    (hEroot : R.E.eval (IRSProfile.domain i) = 0) :
    R.C00.eval (IRSProfile.domain i) = 0 := by
  have hEmap : (R.E.map sigma).eval (IRSProfile.domain i) = 0 := by
    rw [GXSharedAffineRHS.eval_map_at_fixed sigma _ (sigma_domain i),
      hEroot, map_zero]
  simpa only [Polynomial.eval_mul, hEroot, hEmap, zero_mul, zero_add, add_zero]
    using R.source00 i

/-- The globally defined normalized physical ratio.  Its denominator is
root-free for the `E0,N0` selected from the actual high-E-closed leaf. -/
def normalizedW (E0 N0 : ExtensionField[X]) : Index → ExtensionField :=
  fun i => N0.eval (IRSProfile.domain i) / E0.eval (IRSProfile.domain i)

/-- The two literal deficient output contacts of the fixed chain. -/
def chainOutputContact : Fin 2 → Nat
  | 0 => 41
  | 1 => 42

/-- The 28 ordinary shared source contacts `41,...,68`. -/
def chainSourceContact (k : Fin 28) : Nat := 41 + k.1

/-- Literal weighted-X width of the `(r,s)=(0,0)` source at contact `k`. -/
def chainSourceWidth (k : Nat) : Nat :=
  69 * 180413 - 131071 * k

/-- The coefficient freedom left after the complete NTT Hasse depths have
been fixed. -/
def chainSourcePrefix (k : Fin 28) : Nat :=
  chainSourceWidth (chainSourceContact k) % 262144

/-- The direct Pascal contribution from all shared ordinary source contacts.
Each `P k` is intended to have degree strictly below `chainSourcePrefix k`. -/
def directSourceAt
    (W : Index → ExtensionField)
    (P : Fin 28 → ExtensionField[X])
    (row : Fin 2) (i : Index) : ExtensionField :=
  ∑ k : Fin 28,
    if chainOutputContact row ≤ chainSourceContact k then
      (Nat.choose (chainSourceContact k) (chainOutputContact row) :
          ExtensionField) *
        W i ^ (chainSourceContact k - chainOutputContact row) *
        (P k).eval (IRSProfile.domain i)
    else 0

/-- Literal contribution of the special terminal contact `94` and its
order-26 coefficient `C26`. -/
def terminalSourceAt
    (W : Index → ExtensionField) (C26 : ExtensionField[X])
    (row : Fin 2) (i : Index) : ExtensionField :=
  (Nat.choose 94 (chainOutputContact row) : ExtensionField) *
    W i ^ (94 - chainOutputContact row) *
    C26.eval (IRSProfile.domain i)

/-- Exact fixed-shape simultaneous source equation for the two C00 rows.
This is a concrete m69 proposition, not the conditional single-covector
power model. -/
def LiteralC00Chain0026SourceEquation
    (W : Index → ExtensionField) (C26 : ExtensionField[X])
    (P : Fin 28 → ExtensionField[X]) : Prop :=
  C26.natDegree < 127797 ∧
    (∀ k, (P k).natDegree < chainSourcePrefix k) ∧
    ∀ row i, directSourceAt W P row i + terminalSourceAt W C26 row i = 0

/-- An illustrative *stronger* direct-identification candidate: the actual
C00 nodal word itself lies in the strict terminal prefix.  The intended
Full187 `C_q` is an order-q extraction from a terminal coefficient polynomial,
so this definition is not canonized as the required bridge.  Its purpose is
to show that even the nearest direct interpretation is absent from the leaf. -/
def DirectC00TerminalPrefix26Candidate
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) : Prop :=
  ∃ C26 : ExtensionField[X],
    C26.natDegree < 127797 ∧
    ∀ i, C26.eval (IRSProfile.domain i) =
      leaf.toWeightedLeaf.cross.C00.eval (IRSProfile.domain i)

/-- Stronger direct-identification candidate followed by the exact source
equations.  This is useful as a typed STOP interface, but is not claimed to be
the missing canonical extraction from C00 to the Full187 terminal `C26`. -/
def DirectC00Chain0026AttachmentCandidate
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected)
    (E0 N0 : ExtensionField[X]) : Prop :=
  ∃ C26 : ExtensionField[X],
    C26.natDegree < 127797 ∧
    (∀ i, C26.eval (IRSProfile.domain i) =
      leaf.toWeightedLeaf.cross.C00.eval (IRSProfile.domain i)) ∧
    ∃ P : Fin 28 → ExtensionField[X],
      LiteralC00Chain0026SourceEquation (normalizedW E0 N0) C26 P

/-- Arithmetic receipt for the exact fixed chain. -/
theorem chain0026_literal_arithmetic :
    chainOutputContact 0 = 41 ∧
    chainOutputContact 1 = 42 ∧
    chainSourceContact 0 = 41 ∧
    chainSourceContact 27 = 68 ∧
    chainSourcePrefix 0 = 258842 ∧
    chainSourcePrefix 1 = 127771 ∧
    chainSourceWidth 94 = 127823 ∧
    chainSourceWidth 94 - 26 = 127797 := by
  norm_num [chainOutputContact, chainSourceContact, chainSourcePrefix,
    chainSourceWidth]

/-- Strongest short adapter obtainable from the actual leaf without adding a
Full187 source theorem.  It supplies a global normalized `W`, the exact
denominator identity, physical identification away from common-factor roots,
vanishing of C00 at common-factor roots, the actual C00 node equation, and
the best stored degree bound.  It does *not* produce
the direct attachment candidate above. -/
theorem high_E_closed_leaf_exposes_ratio_and_C00_boundary
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    ∃ B E0 N0 : ExtensionField[X],
      B ≠ 0 ∧ E0 ≠ 0 ∧ IsCoprime E0 N0 ∧
      leaf.toWeightedLeaf.cross.E = B * E0 ∧
      leaf.toWeightedLeaf.cross.N = B * N0 ∧
      (∀ i, E0.eval (IRSProfile.domain i) ≠ 0) ∧
      (∀ i, E0.eval (IRSProfile.domain i) * normalizedW E0 N0 i =
        N0.eval (IRSProfile.domain i)) ∧
      (∀ i, B.eval (IRSProfile.domain i) ≠ 0 →
        normalizedW E0 N0 i =
          leaf.toWeightedLeaf.cross.d.eval (IRSProfile.domain i) * U 0 i -
          leaf.toWeightedLeaf.cross.c.eval (IRSProfile.domain i) * U 1 i) ∧
      (∀ i, B.eval (IRSProfile.domain i) = 0 →
        leaf.toWeightedLeaf.cross.C00.eval (IRSProfile.domain i) = 0) ∧
      leaf.toWeightedLeaf.cross.C00.natDegree ≤ 156003 ∧
      (∀ i,
        (leaf.toWeightedLeaf.cross.E * leaf.toWeightedLeaf.cross.L *
            leaf.toWeightedLeaf.cross.c.map sigma).eval
              (IRSProfile.domain i) * U 0 i +
          (leaf.toWeightedLeaf.cross.E.map sigma *
              leaf.toWeightedLeaf.cross.M *
              leaf.toWeightedLeaf.cross.c).eval
                (IRSProfile.domain i) * sigma (U 0 i) +
          leaf.toWeightedLeaf.cross.C00.eval (IRSProfile.domain i) = 0) := by
  obtain ⟨B, E0, N0, _Q, hB, hE0, hRE, hRN, hcop, _hcopQ, _hQ,
      _hhom, _hmin, _hcap, hroot, _hcopadj, _hmixed, _Good, _scalar,
      _centre, _a, _b, _hsub, _hexception, _hretained, _hWlo0, _hWhi0,
      _hcentre, _hab, _hinj, _hQroot, _hscalar, _houtside, _hsmall, _hh,
      _hlow, _hWlo, _hexcess, _hsum, _heUpper, _hWupper, _hEsmall⟩ :=
    leaf.cross_no_adjacent_hard_corner
  let R := leaf.toWeightedLeaf.cross
  have hden : ∀ i, E0.eval (IRSProfile.domain i) * normalizedW E0 N0 i =
      N0.eval (IRSProfile.domain i) := by
    intro i
    exact mul_div_cancel₀ _ (hroot i)
  have hphysical : ∀ i, B.eval (IRSProfile.domain i) ≠ 0 →
      normalizedW E0 N0 i =
        R.d.eval (IRSProfile.domain i) * U 0 i -
          R.c.eval (IRSProfile.domain i) * U 1 i := by
    intro i hBi
    have hcross :
        (B * E0).eval (IRSProfile.domain i) *
            (R.d.eval (IRSProfile.domain i) * U 0 i -
              R.c.eval (IRSProfile.domain i) * U 1 i) =
          (B * N0).eval (IRSProfile.domain i) := by
      simpa only [R, hRE, hRN] using R.cross i
    have hcancel :
        E0.eval (IRSProfile.domain i) *
            (R.d.eval (IRSProfile.domain i) * U 0 i -
              R.c.eval (IRSProfile.domain i) * U 1 i) =
          N0.eval (IRSProfile.domain i) := by
      simp only [Polynomial.eval_mul] at hcross
      apply mul_left_cancel₀ hBi
      simpa only [mul_assoc] using hcross
    apply mul_left_cancel₀ (hroot i)
    rw [hden i]
    exact hcancel.symm
  have hBroot : ∀ i, B.eval (IRSProfile.domain i) = 0 →
      R.C00.eval (IRSProfile.domain i) = 0 := by
    intro i hBi
    apply c00_vanishes_at_cross_E_root R i
    rw [hRE, Polynomial.eval_mul, hBi, zero_mul]
  have hCdegree : R.C00.natDegree ≤ 156003 := by
    have h := R.C00_degree
    have hj := leaf.toWeightedLeaf.grade_le_24932
    omega
  refine ⟨B, E0, N0, hB, hE0, hcop, hRE, hRN, hroot,
    hden, ?_, ?_, ?_, ?_⟩
  · simpa only [R] using hphysical
  · simpa only [R] using hBroot
  · simpa only [R] using hCdegree
  · simpa only [mul_assoc] using leaf.toWeightedLeaf.cross.source00

/-- The leaf's stored degree estimate misses the literal terminal prefix by
28207 in strict-bound form.  This is why `C00_degree` cannot inhabit the first
conjunct of `LiteralC00Chain0026SourceEquation`. -/
theorem c00_stored_bound_does_not_reach_terminal_prefix_arithmetic :
    127797 < 156003 ∧ 156003 - 127796 = 28207 := by
  norm_num

/-- Concrete benchmark-node countergate: a degree-156003 upper bound alone
cannot imply membership in the strict 127797 terminal prefix.  The monomial
`X^127797` satisfies the stored numerical bound, and injectivity of all
262144 NTT nodes prevents it from agreeing there with any shorter
polynomial.  This does not assert that this monomial extends to a whole
DataEleven leaf; it isolates exactly why the `C00_degree` field is not the
missing producer. -/
theorem stored_degree_bound_alone_does_not_imply_terminal_prefix :
    let Cbad : ExtensionField[X] := Polynomial.X ^ 127797
    Cbad.natDegree ≤ 156003 ∧
      ¬ ∃ C26 : ExtensionField[X], C26.natDegree < 127797 ∧
        ∀ i, C26.eval (IRSProfile.domain i) =
          Cbad.eval (IRSProfile.domain i) := by
  dsimp only
  constructor
  · norm_num
  · rintro ⟨C26, hdegree, heval⟩
    have hzero : (Polynomial.X ^ 127797 : ExtensionField[X]) - C26 = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        ((Polynomial.X ^ 127797 : ExtensionField[X]) - C26)
        IRSProfile.domain.injective
      · intro i
        simp only [Polynomial.eval_sub, heval i, sub_self]
      · have hcard : Fintype.card Index = 262144 := by
          norm_num [Index, IRSProfile.Index]
        rw [hcard]
        exact (Polynomial.natDegree_sub_le _ _).trans_lt (by
          norm_num
          omega)
    have heq : (Polynomial.X ^ 127797 : ExtensionField[X]) = C26 :=
      sub_eq_zero.mp hzero
    have hdegrees := congrArg Polynomial.natDegree heq
    norm_num at hdegrees
    omega

#print axioms chain0026_literal_arithmetic
#print axioms c00_vanishes_at_cross_E_root
#print axioms high_E_closed_leaf_exposes_ratio_and_C00_boundary
#print axioms c00_stored_bound_does_not_reach_terminal_prefix_arithmetic
#print axioms stored_degree_bound_alone_does_not_imply_terminal_prefix

end
end ProximityPrize.SubmissionLower.M69DataElevenC00Chain0026AttachmentStop6900
