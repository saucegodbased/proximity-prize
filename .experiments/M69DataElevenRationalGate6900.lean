import DataElevenHighEClosedFrontier6900
import M69RationalTwoPowerGate6900

/-! Exact DataEleven parameters exposed to the m69 rational two-power gate. -/

namespace ProximityPrize.SubmissionLower.M69DataElevenRationalGate6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open ActualAdjacentFilteredHardCornerElimination6900
open DataElevenHighEClosedFrontier6900
open ActualPrimitiveContentNodeSet6900
open M69RationalTwoPowerGate6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- At a root of the unfactored cross denominator, all four actual source
right-hand sides vanish.  Thus common-factor roots do not carry arbitrary
target values; this is the exact fact hidden by an all-node cancellation of
`B`. -/
theorem aligned_cross_source_constants_vanish_at_E_root
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (i : Index)
    (hEroot : R.E.eval (IRSProfile.domain i) = 0) :
    R.C00.eval (IRSProfile.domain i) = 0 ∧
      R.C10.eval (IRSProfile.domain i) = 0 ∧
      R.C01.eval (IRSProfile.domain i) = 0 ∧
      R.C11.eval (IRSProfile.domain i) = 0 := by
  have hEmap : (R.E.map sigma).eval (IRSProfile.domain i) = 0 := by
    rw [GXSharedAffineRHS.eval_map_at_fixed sigma _ (sigma_domain i),
      hEroot, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Polynomial.eval_mul, hEroot, hEmap, zero_mul, zero_add, add_zero]
      using R.source00 i
  · simpa only [Polynomial.eval_mul, hEroot, hEmap, zero_mul, zero_add, add_zero]
      using R.source10 i
  · simpa only [Polynomial.eval_mul, hEroot, hEmap, zero_mul, zero_add, add_zero]
      using R.source01 i
  · simpa only [Polynomial.eval_mul, hEroot, hEmap, zero_mul, zero_add, add_zero]
      using R.source11 i

/-- Pointwise rank-one compatibility for the four source right-hand sides. -/
def AlignedSourceRankOneAt
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (i : Index) : Prop :=
  R.d.eval (IRSProfile.domain i) * R.C00.eval (IRSProfile.domain i) =
      R.c.eval (IRSProfile.domain i) * R.C10.eval (IRSProfile.domain i) ∧
    (R.d.map sigma).eval (IRSProfile.domain i) *
        R.C00.eval (IRSProfile.domain i) =
      (R.c.map sigma).eval (IRSProfile.domain i) *
        R.C01.eval (IRSProfile.domain i) ∧
    (R.d.map sigma).eval (IRSProfile.domain i) *
        R.C10.eval (IRSProfile.domain i) =
      (R.c.map sigma).eval (IRSProfile.domain i) *
        R.C11.eval (IRSProfile.domain i) ∧
    R.d.eval (IRSProfile.domain i) * R.C01.eval (IRSProfile.domain i) =
      R.c.eval (IRSProfile.domain i) * R.C11.eval (IRSProfile.domain i)

/-- At a node where the normalized wedge vanishes, the four actual source
right-hand sides have the four rank-one compatibility relations.  This is
the target-specific structure left after the numerator-zero counterexample
kills arbitrary-value surjectivity. -/
theorem aligned_cross_source_rank_one_at_wedge_zero
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (i : Index)
    (hwedge :
      R.d.eval (IRSProfile.domain i) * U 0 i -
        R.c.eval (IRSProfile.domain i) * U 1 i = 0) :
    AlignedSourceRankOneAt R i := by
  dsimp only [AlignedSourceRankOneAt]
  have hswedge :
      (R.d.map sigma).eval (IRSProfile.domain i) * sigma (U 0 i) -
        (R.c.map sigma).eval (IRSProfile.domain i) * sigma (U 1 i) = 0 := by
    have hs := congrArg sigma hwedge
    rw [map_sub, map_mul, map_mul, map_zero,
      ← GXSharedAffineRHS.eval_map_at_fixed sigma _ (sigma_domain i) R.d,
      ← GXSharedAffineRHS.eval_map_at_fixed sigma _ (sigma_domain i) R.c] at hs
    exact hs
  have h00 := R.source00 i
  have h10 := R.source10 i
  have h01 := R.source01 i
  have h11 := R.source11 i
  simp only [Polynomial.eval_mul] at h00 h10 h01 h11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination
      R.d.eval (IRSProfile.domain i) * h00 -
      R.c.eval (IRSProfile.domain i) * h10 -
      (R.E.eval (IRSProfile.domain i) * R.L.eval (IRSProfile.domain i) *
        (R.c.map sigma).eval (IRSProfile.domain i)) * hwedge
  · linear_combination
      (R.d.map sigma).eval (IRSProfile.domain i) * h00 -
      (R.c.map sigma).eval (IRSProfile.domain i) * h01 -
      ((R.E.map sigma).eval (IRSProfile.domain i) *
        R.M.eval (IRSProfile.domain i) * R.c.eval (IRSProfile.domain i)) * hswedge
  · linear_combination
      (R.d.map sigma).eval (IRSProfile.domain i) * h10 -
      (R.c.map sigma).eval (IRSProfile.domain i) * h11 -
      ((R.E.map sigma).eval (IRSProfile.domain i) *
        R.M.eval (IRSProfile.domain i) * R.d.eval (IRSProfile.domain i)) * hswedge
  · linear_combination
      R.d.eval (IRSProfile.domain i) * h01 -
      R.c.eval (IRSProfile.domain i) * h11 -
      (R.E.eval (IRSProfile.domain i) * R.L.eval (IRSProfile.domain i) *
        (R.d.map sigma).eval (IRSProfile.domain i)) * hwedge

/-- On the exact high-E-closed leaf, the normalized numerator is bounded by
`149776`, while the common-factor/content-root cost has the sharper exact
budget `rootCount + 2*t + q + ell <= 22883`.

The currently proved no-wrap square lemma applies only through numerator
degree `129449`; hence the interval `129450..149776` is a real remaining
obligation, not a rounded numerical margin. -/
theorem high_E_closed_leaf_m69_rational_parameters
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    ∃ B E0 N0 Q : ExtensionField[X],
      B ≠ 0 ∧ E0 ≠ 0 ∧
      leaf.toWeightedLeaf.cross.E = B * E0 ∧
      leaf.toWeightedLeaf.cross.N = B * N0 ∧
      IsCoprime E0 N0 ∧ N0 ≠ 0 ∧
      (∀ i, E0.eval (IRSProfile.domain i) ≠ 0) ∧
      max leaf.toWeightedLeaf.cross.c.natDegree
          leaf.toWeightedLeaf.cross.d.natDegree + Q.natDegree + 2049 ≤
        E0.natDegree ∧
      E0.natDegree < 18415 ∧
      N0.natDegree ≤ 149776 ∧
      B.natDegree + N0.natDegree +
        max leaf.toWeightedLeaf.cross.L.natDegree
          leaf.toWeightedLeaf.cross.M.natDegree ≤ 156003 ∧
      (B.natDegree + 2 * max leaf.toWeightedLeaf.cross.c.natDegree
          leaf.toWeightedLeaf.cross.d.natDegree +
        Q.natDegree +
        max leaf.toWeightedLeaf.cross.L.natDegree
          leaf.toWeightedLeaf.cross.M.natDegree ≤ 22883) ∧
      (N0.natDegree ≤ 129449 ∨
        (129450 ≤ N0.natDegree ∧ N0.natDegree ≤ 149776)) := by
  let R := leaf.toWeightedLeaf.cross
  obtain ⟨B, E0, N0, Q, hB, hE0, hRE, hRN, hproper, _hcopQ, _hQ,
    _hhom, _hmin, _hcap, hroot, _hcopadj, _hmixed, _Good, _scalar,
    _centre, _a, _b, _hsub, _hexception, _hretained, _hWlo0, _hWhi0,
    _hcentre, _hab, _hinj, _hQroot, _hscalar, _houtside, _hsmall, _hh,
    _hlow, _hWlo, hexcess, _hsum, _heUpper, _hWupper, hEsmall⟩ :=
      leaf.cross_no_adjacent_hard_corner
  have hgrade :
      B.natDegree + E0.natDegree +
          max R.c.natDegree R.d.natDegree +
          max R.L.natDegree R.M.natDegree =
        leaf.toWeightedLeaf.data.horizontal.grade := by
    have hg := R.grade
    rw [hRE, natDegree_mul hB hE0] at hg
    simpa only [R] using hg
  have hrootCost :
      B.natDegree + 2 * max R.c.natDegree R.d.natDegree + Q.natDegree +
          max R.L.natDegree R.M.natDegree ≤ 22883 := by
    have hcost := common_factor_root_cost_arithmetic
      B.natDegree E0.natDegree
      (max R.c.natDegree R.d.natDegree) Q.natDegree
      (max R.L.natDegree R.M.natDegree)
      leaf.toWeightedLeaf.data.horizontal.grade hgrade
      leaf.toWeightedLeaf.grade_le_24932 hexcess
    exact hcost
  have hN0degree :
      N0.natDegree ≤
        131071 + E0.natDegree + max R.c.natDegree R.d.natDegree := by
    by_cases hN0 : N0 = 0
    · simp [hN0]
    · have hNdegree := R.N_degree
      rw [hRN, natDegree_mul hB hN0, hRE, natDegree_mul hB hE0] at hNdegree
      omega
  have hEpositive : 0 < E0.natDegree := by omega
  have hN0ne : N0 ≠ 0 := by
    intro hzero
    apply Polynomial.not_isUnit_of_natDegree_pos E0 hEpositive
    exact isCoprime_zero_right.mp (by simpa only [hzero] using hproper)
  have hN0cap : N0.natDegree ≤ 149776 := by
    have htotal : E0.natDegree + Q.natDegree +
        max R.c.natDegree R.d.natDegree < 18706 := _hlow
    omega
  have hcombinedRootDegree :
      B.natDegree + N0.natDegree +
          max R.L.natDegree R.M.natDegree ≤ 156003 := by
    calc
      B.natDegree + N0.natDegree + max R.L.natDegree R.M.natDegree
          ≤ B.natDegree +
              (131071 + E0.natDegree + max R.c.natDegree R.d.natDegree) +
              max R.L.natDegree R.M.natDegree := by omega
      _ = 131071 + leaf.toWeightedLeaf.data.horizontal.grade := by omega
      _ ≤ 131071 + 24932 :=
        Nat.add_le_add_left leaf.toWeightedLeaf.grade_le_24932 131071
      _ = 156003 := by norm_num
  refine ⟨B, E0, N0, Q, hB, hE0, hRE, hRN, hproper, hN0ne, hroot,
    hexcess, hEsmall, hN0cap, ?_, ?_, ?_⟩
  · simpa only [R] using hcombinedRootDegree
  · simpa only [R] using hrootCost
  · omega

/-- Exact nodal split supplied by the actual DataEleven equations.  At a
`B`-root all four source constants vanish.  Away from `B`, an `N0`-root
forces the variable-direction wedge to vanish and hence forces the four
source constants into their rank-one locus.  There is presently no cardinal
bound on this second set. -/
theorem high_E_closed_leaf_m69_nodal_target_split
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    ∃ B E0 N0 : ExtensionField[X],
      B ≠ 0 ∧ E0 ≠ 0 ∧ N0 ≠ 0 ∧ IsCoprime E0 N0 ∧
      leaf.toWeightedLeaf.cross.E = B * E0 ∧
      leaf.toWeightedLeaf.cross.N = B * N0 ∧
      (∀ i, E0.eval (IRSProfile.domain i) ≠ 0) ∧
      (∀ i, B.eval (IRSProfile.domain i) = 0 →
        leaf.toWeightedLeaf.cross.C00.eval (IRSProfile.domain i) = 0 ∧
        leaf.toWeightedLeaf.cross.C10.eval (IRSProfile.domain i) = 0 ∧
        leaf.toWeightedLeaf.cross.C01.eval (IRSProfile.domain i) = 0 ∧
        leaf.toWeightedLeaf.cross.C11.eval (IRSProfile.domain i) = 0) ∧
      (∀ i, B.eval (IRSProfile.domain i) ≠ 0 →
        N0.eval (IRSProfile.domain i) = 0 →
        leaf.toWeightedLeaf.cross.d.eval (IRSProfile.domain i) * U 0 i -
            leaf.toWeightedLeaf.cross.c.eval (IRSProfile.domain i) * U 1 i = 0 ∧
          AlignedSourceRankOneAt leaf.toWeightedLeaf.cross i) := by
  obtain ⟨B, E0, N0, _Q, hB, hE0, hRE, hRN, hcop, hN0, hroot,
    _hexcess, _hEsmall, _hNcap, _hcombined, _hrootCost, _hsplit⟩ :=
      high_E_closed_leaf_m69_rational_parameters leaf
  let R := leaf.toWeightedLeaf.cross
  refine ⟨B, E0, N0, hB, hE0, hN0, hcop, hRE, hRN, hroot, ?_, ?_⟩
  · intro i hBi
    apply aligned_cross_source_constants_vanish_at_E_root R i
    rw [hRE, Polynomial.eval_mul, hBi, zero_mul]
  · intro i hBi hNi
    have hfactored :
        (B * E0).eval (IRSProfile.domain i) *
            (R.d.eval (IRSProfile.domain i) * U 0 i -
              R.c.eval (IRSProfile.domain i) * U 1 i) =
          (B * N0).eval (IRSProfile.domain i) := by
      simpa only [R, hRE, hRN] using R.cross i
    have hnormalized := normalized_cross_at_nonroot B E0 N0
      (IRSProfile.domain i)
      (R.d.eval (IRSProfile.domain i) * U 0 i -
        R.c.eval (IRSProfile.domain i) * U 1 i) hBi hfactored
    have hwedge :
        R.d.eval (IRSProfile.domain i) * U 0 i -
          R.c.eval (IRSProfile.domain i) * U 1 i = 0 := by
      rw [hNi] at hnormalized
      exact (mul_eq_zero.mp hnormalized).resolve_left (hroot i)
    exact ⟨hwedge, aligned_cross_source_rank_one_at_wedge_zero R i hwedge⟩

/-- The existing selected-quotient exporter works on this precise live set.
Its omitted-coordinate cost is the content degree, at most `24932`. -/
theorem high_E_closed_leaf_existing_live_exact_card
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    ((Finset.univ : Finset Index) \
        contentNodes leaf.toWeightedLeaf.conic).card =
      262144 - leaf.toWeightedLeaf.conic.content.natDegree := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,
    PrimitiveConicData.contentNodes_card_eq_natDegree
      leaf.toWeightedLeaf.data.toDataTen.toDataNine leaf.toWeightedLeaf.conic]
  norm_num [Index, IRSProfile.Index]

theorem high_E_closed_leaf_existing_live_omitted_le_24932
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    (contentNodes leaf.toWeightedLeaf.conic).card ≤ 24932 := by
  exact (PrimitiveConicData.contentNodes_card_le_grade
    leaf.toWeightedLeaf.data.toDataTen.toDataNine leaf.toWeightedLeaf.conic).trans
      leaf.toWeightedLeaf.grade_le_24932

/-- Even after the existing content puncture, at least `237212` coordinates
remain.  In particular the `127730`-zero hostile set fits entirely inside the
live target unless an additional leaf-specific incidence theorem forbids it. -/
theorem high_E_closed_leaf_existing_live_card_at_least_237212
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    237212 ≤
      ((Finset.univ : Finset Index) \
        contentNodes leaf.toWeightedLeaf.conic).card := by
  rw [high_E_closed_leaf_existing_live_exact_card leaf]
  have h := high_E_closed_leaf_existing_live_omitted_le_24932 leaf
  rw [PrimitiveConicData.contentNodes_card_eq_natDegree
    leaf.toWeightedLeaf.data.toDataTen.toDataNine leaf.toWeightedLeaf.conic] at h
  omega

#print axioms aligned_cross_source_constants_vanish_at_E_root
#print axioms aligned_cross_source_rank_one_at_wedge_zero
#print axioms high_E_closed_leaf_m69_rational_parameters
#print axioms high_E_closed_leaf_m69_nodal_target_split
#print axioms high_E_closed_leaf_existing_live_exact_card
#print axioms high_E_closed_leaf_existing_live_omitted_le_24932
#print axioms high_E_closed_leaf_existing_live_card_at_least_237212

end
end ProximityPrize.SubmissionLower.M69DataElevenRationalGate6900
