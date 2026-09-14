import DataElevenCanonicalInterpolant6900

/-! Kernel-small core lemmas for the canonical DataEleven wedge wrap. -/

namespace ProximityPrize.SubmissionLower.DataElevenCanonicalWedgeWrap6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open DataElevenCanonicalInterpolant6900

attribute [local irreducible] canonicalReceivedInterpolant

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem aligned_cross_interpolant_wedge_wrap
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (hnonpolynomial : ¬ R.E ∣ R.N)
    (V0 V1 : ExtensionField[X])
    (hV0 : ∀ i, V0.eval (IRSProfile.domain i) = U 0 i)
    (hV1 : ∀ i, V1.eval (IRSProfile.domain i) = U 1 i)
    (hNsmall : R.N.natDegree < 262144) :
    262144 ≤ R.E.natDegree +
      (R.d * V0 - R.c * V1).natDegree := by
  let wedge : ExtensionField[X] := R.d * V0 - R.c * V1
  let F := R.E * wedge - R.N
  have hFeval : ∀ i : Index, F.eval (IRSProfile.domain i) = 0 := by
    intro i
    dsimp only [F, wedge]
    rw [eval_sub, eval_mul, eval_sub, eval_mul, eval_mul,
      hV0 i, hV1 i]
    exact sub_eq_zero.mpr (R.cross i)
  have hFne : F ≠ 0 := by
    intro hFzero
    apply hnonpolynomial
    refine ⟨wedge, ?_⟩
    have heq : R.E * wedge = R.N := by
      exact sub_eq_zero.mp (by simpa only [F] using hFzero)
    exact heq.symm
  have hFdegree : 262144 ≤ F.natDegree := by
    by_contra hnot
    apply hFne
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      F IRSProfile.domain.injective hFeval
    have hcard : Fintype.card Index = 262144 := by
      norm_num [Index, IRSProfile.Index]
    have hlt : F.natDegree < 262144 := Nat.lt_of_not_ge hnot
    simpa only [hcard] using hlt
  have hFupper : F.natDegree ≤
      max (R.E.natDegree + wedge.natDegree) R.N.natDegree := by
    have hmul : (R.E * wedge).natDegree ≤
        R.E.natDegree + wedge.natDegree := natDegree_mul_le
    exact (natDegree_sub_le _ _).trans
      (max_le (hmul.trans (le_max_left _ _)) (le_max_right _ _))
  have hmax : 262144 ≤
      max (R.E.natDegree + wedge.natDegree) R.N.natDegree :=
    hFdegree.trans hFupper
  have hwrap : 262144 ≤ R.E.natDegree + wedge.natDegree :=
    (le_max_iff.mp hmax).resolve_right (Nat.not_le_of_lt hNsmall)
  simpa only [wedge] using hwrap

theorem aligned_cross_canonical_wedge_wrap
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (hnonpolynomial : ¬ R.E ∣ R.N)
    (hNsmall : R.N.natDegree < 262144) :
    262144 ≤ R.E.natDegree +
      (R.d * canonicalReceivedInterpolant (U 0) -
        R.c * canonicalReceivedInterpolant (U 1)).natDegree := by
  exact aligned_cross_interpolant_wedge_wrap R hnonpolynomial
    (canonicalReceivedInterpolant (U 0))
    (canonicalReceivedInterpolant (U 1))
    (canonicalReceivedInterpolant_eval (U 0))
    (canonicalReceivedInterpolant_eval (U 1)) hNsmall

theorem aligned_cross_N_natDegree_lt
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    (R : AlignedCrossData U j) (hgrade : j ≤ 24932) :
    R.N.natDegree < 262144 := by
  have hN := R.N_degree
  have hg := R.grade
  omega

theorem polynomial_wedge_natDegree_le
    (c d V0 V1 : ExtensionField[X]) :
    (d * V0 - c * V1).natDegree ≤
      max c.natDegree d.natDegree + max V0.natDegree V1.natDegree := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans
      (Nat.add_le_add (le_max_right _ _) (le_max_left _ _))
  · exact natDegree_mul_le.trans
      (Nat.add_le_add (le_max_left _ _) (le_max_right _ _))

theorem canonical_wedge_grade_arithmetic
    (e t ell v w j : Nat)
    (hgradeEq : e + t + ell = j) (hgrade : j ≤ 24932)
    (hwrap : 262144 ≤ e + w) (hwedge : w ≤ t + v) :
    237212 + ell ≤ v := by
  omega

#print axioms aligned_cross_interpolant_wedge_wrap
#print axioms aligned_cross_canonical_wedge_wrap

end
end ProximityPrize.SubmissionLower.DataElevenCanonicalWedgeWrap6900
