import DataElevenCanonicalWedgeWrapCore6900

/-!
# Canonical row wrap forced by the nonpolynomial DataEleven cross

Let `V0,V1` be the canonical all-node interpolants of the two received rows.
For an aligned cross, the polynomial

`E * (d * V0 - c * V1) - N`

vanishes on all `262144` benchmark nodes.  It cannot be zero in the
nonpolynomial branch `¬ E ∣ N`; hence its degree reaches the cyclic wrap
threshold.  The exact grade identity then forces one canonical received row
very near the top of the NTT coefficient range.

This is a same-witness consequence of the existing DataEleven leaf.  It does
not assert a new source theorem or alter the scalar-rank argument.
-/

namespace ProximityPrize.SubmissionLower.DataElevenCanonicalWedgeWrap6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open DataElevenWeightedLowPoleIntersection6900
open DataElevenHighEClosedFrontier6900
open DataElevenCanonicalInterpolant6900

attribute [local irreducible] canonicalReceivedInterpolant

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Exact-grade form of the row-degree consequence.  Retaining
`max (deg L) (deg M)` is stronger than discarding the last summand of
`deg E + max(deg c, deg d) + max(deg L, deg M) = j`.
-/
theorem aligned_cross_one_interpolating_row_near_top
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (hnonpolynomial : ¬ R.E ∣ R.N)
    (hgrade : j ≤ 24932) (V0 V1 : ExtensionField[X])
    (hV0 : ∀ i, V0.eval (IRSProfile.domain i) = U 0 i)
    (hV1 : ∀ i, V1.eval (IRSProfile.domain i) = U 1 i) :
    237212 + max R.L.natDegree R.M.natDegree ≤
      max V0.natDegree V1.natDegree := by
  let t := max R.c.natDegree R.d.natDegree
  let ell := max R.L.natDegree R.M.natDegree
  have hNsmall := aligned_cross_N_natDegree_lt R hgrade
  have hwrap := aligned_cross_interpolant_wedge_wrap R hnonpolynomial
    V0 V1 hV0 hV1 hNsmall
  have hwedge :
      (R.d * V0 - R.c * V1).natDegree ≤
      t + max V0.natDegree V1.natDegree := by
    simpa only [t] using
      polynomial_wedge_natDegree_le R.c R.d V0 V1
  have hgradeEq : R.E.natDegree + t + ell = j := by
    simpa only [t, ell] using R.grade
  exact canonical_wedge_grade_arithmetic R.E.natDegree t ell
    (max V0.natDegree V1.natDegree)
    (R.d * V0 - R.c * V1).natDegree
    j hgradeEq hgrade hwrap hwedge

/-- Same-witness specialization on the terminal high-E-closed DataEleven
leaf.  No existential cross is selected here: this uses the cross stored in
the supplied leaf and its stored `cross_nonpolynomial` proof.
-/
theorem high_E_closed_leaf_one_interpolating_row_near_top
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected)
    (V0 V1 : ExtensionField[X])
    (hV0 : ∀ i, V0.eval (IRSProfile.domain i) = U 0 i)
    (hV1 : ∀ i, V1.eval (IRSProfile.domain i) = U 1 i) :
    237212 +
        max leaf.toWeightedLeaf.cross.L.natDegree
          leaf.toWeightedLeaf.cross.M.natDegree ≤
      max V0.natDegree V1.natDegree := by
  exact aligned_cross_one_interpolating_row_near_top
    leaf.toWeightedLeaf.cross
    leaf.toWeightedLeaf.cross_nonpolynomial
    leaf.toWeightedLeaf.grade_le_24932
    V0 V1 hV0 hV1

/-- Canonical Lagrange specialization of the preceding same-witness leaf
theorem. -/
theorem high_E_closed_leaf_one_canonical_row_near_top
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    237212 +
        max leaf.toWeightedLeaf.cross.L.natDegree
          leaf.toWeightedLeaf.cross.M.natDegree ≤
      max
        (canonicalReceivedInterpolant (U 0)).natDegree
        (canonicalReceivedInterpolant (U 1)).natDegree := by
  exact high_E_closed_leaf_one_interpolating_row_near_top leaf
    (canonicalReceivedInterpolant (U 0))
    (canonicalReceivedInterpolant (U 1))
    (canonicalReceivedInterpolant_eval (U 0))
    (canonicalReceivedInterpolant_eval (U 1))

/-- In particular, the smallest two-high monomial control used against the
universal direct Full187 envelope cannot inhabit this exact DataEleven leaf.
-/
theorem high_E_closed_leaf_not_both_interpolants_degree_le_133121
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected)
    (V0 V1 : ExtensionField[X])
    (hV0 : ∀ i, V0.eval (IRSProfile.domain i) = U 0 i)
    (hV1 : ∀ i, V1.eval (IRSProfile.domain i) = U 1 i) :
    ¬ (V0.natDegree ≤ 133121 ∧ V1.natDegree ≤ 133121) := by
  intro hlow
  have hnear := high_E_closed_leaf_one_interpolating_row_near_top
    leaf V0 V1 hV0 hV1
  have hmax : max V0.natDegree V1.natDegree ≤ 133121 :=
    max_le hlow.1 hlow.2
  omega

theorem high_E_closed_leaf_not_both_canonical_rows_degree_le_133121
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : DataElevenHighEClosedLeaf U Gamma agreement selected) :
    ¬ ((canonicalReceivedInterpolant (U 0)).natDegree ≤ 133121 ∧
      (canonicalReceivedInterpolant (U 1)).natDegree ≤ 133121) := by
  exact high_E_closed_leaf_not_both_interpolants_degree_le_133121 leaf
    (canonicalReceivedInterpolant (U 0))
    (canonicalReceivedInterpolant (U 1))
    (canonicalReceivedInterpolant_eval (U 0))
    (canonicalReceivedInterpolant_eval (U 1))

#print axioms aligned_cross_canonical_wedge_wrap
#print axioms aligned_cross_one_interpolating_row_near_top
#print axioms high_E_closed_leaf_one_interpolating_row_near_top
#print axioms high_E_closed_leaf_one_canonical_row_near_top
#print axioms high_E_closed_leaf_not_both_interpolants_degree_le_133121
#print axioms high_E_closed_leaf_not_both_canonical_rows_degree_le_133121

end
end ProximityPrize.SubmissionLower.DataElevenCanonicalWedgeWrap6900
