import WeightedTrianglePrefixFormulaW1332216900

/-! Closed evaluation of the relaxed active-fibre count. -/
namespace ProximityPrize.SubmissionLower.WeightedRelaxedFibreFormulaW1332216900

open scoped BigOperators
open WeightedSourceDerivativeBands6900
open WeightedRelaxedFibreCoreW1332216900
open WeightedTrianglePrefixFormulaW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000

theorem ceilWidth_relaxed_formula (C q s E n : Nat)
    (hspos : 0<s) (hsW : s<133221) (hE : 2*E<133221)
    (hnE : n≤E) (hC : C=q*133221+s) :
    ceilWidth 133221 (C-133219*n)=
      (if n≤q then q+1-n else 0)+
        (if n≤q+1 ∧ 133221<s+2*n then 1 else 0) := by
  unfold ceilWidth
  by_cases hnq : n≤q
  · have hcost : 133219*n≤C := by omega
    have hx : C-133219*n=(q-n)*133221+(s+2*n) := by
      have hsub := Nat.sub_add_cancel hcost
      have hqn := Nat.sub_add_cancel hnq
      omega
    rw [if_pos hnq,hx]
    by_cases hwrap : 133221<s+2*n
    · rw [if_pos ⟨by omega,hwrap⟩]
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    · rw [if_neg (by simpa only [not_and_or] using Or.inr hwrap)]
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
  · have hqn : q<n := Nat.lt_of_not_ge hnq
    rw [if_neg hnq]
    by_cases hn1 : n≤q+1
    · have heq : n=q+1 := by omega
      subst n
      by_cases hwrap : 133221<s+2*(q+1)
      · rw [if_pos ⟨le_rfl,hwrap⟩]
        have hcost : 133219*(q+1)≤C := by
          rw [hC]
          omega
        have hx : C-133219*(q+1)=s+2*(q+1)-133221 := by
          have hsub := Nat.sub_add_cancel hcost
          omega
        rw [hx]
        apply Nat.div_eq_of_lt_le
        · omega
        · omega
      · rw [if_neg (by simpa only [not_and_or] using Or.inr hwrap)]
        have hzero : C≤133219*(q+1) := by rw [hC]; omega
        rw [Nat.sub_eq_zero_of_le hzero]
    · rw [if_neg (by omega)]
      have hzero : C≤133219*n := by
        rw [hC]
        omega
      rw [Nat.sub_eq_zero_of_le hzero]

theorem sum_if_le_eq_prefix (f : Nat→Nat) (E q : Nat) :
    (∑ n ∈ Finset.range (E+1),if n≤q then f n else 0)=
      ∑ n ∈ Finset.range (min E q+1),f n := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  · intro n hn
    rfl

theorem sum_if_between_eq_prefix_sub (f : Nat→Nat) (E q h : Nat) (hh : 0<h) :
    (∑ n ∈ Finset.range (E+1),if n≤q ∧ h≤n then f n else 0)=
      (∑ n ∈ Finset.range (min E q+1),f n)-
        ∑ n ∈ Finset.range (min (min E q) (h-1)+1),f n := by
  let H:=min E q
  let L:=min H (h-1)
  have hLH : L≤H := min_le_left _ _
  have hsub : Finset.range (L+1)⊆Finset.range (H+1) := Finset.range_mono (by omega)
  have hsdiff := Finset.sum_sdiff (f:=f) hsub
  have hfilter :
      (Finset.range (E+1)).filter (fun n => n≤q ∧ h≤n)=
        Finset.range (H+1)\Finset.range (L+1) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_sdiff]
    dsimp [H,L]
    omega
  rw [← Finset.sum_filter,hfilter]
  dsimp [H,L]
  exact Nat.eq_sub_of_add_eq hsdiff

def relaxedClosedQ (C W E : Nat) : ℚ :=
  let q:=C/W
  let s:=C%W
  let h:=(W-s)/2+1
  (q+1)*triangleCardQ E q-triangleWeightQ E q+
    triangleCardQ E (q+1)-triangleCardQ E (min (q+1) (h-1))

theorem triangleRelaxedCount_cast_closed (C E : Nat)
    (hrem : 0<C%133221) (hE : 2*E<133221) :
    (triangleRelaxedCount C 133221 E:ℚ)=relaxedClosedQ C 133221 E := by
  let q:=C/133221
  let s:=C%133221
  let h:=(133221-s)/2+1
  have hsW : s<133221 := Nat.mod_lt C (by norm_num)
  have hC : C=q*133221+s := by
    dsimp [q,s]
    have hd := Nat.div_add_mod C 133221
    omega
  have hthreshold (n : Nat) : 133221<s+2*n ↔ h≤n := by
    dsimp [h,s]
    omega
  unfold triangleRelaxedCount
  have hpoint (n : Nat) (hn : n∈Finset.range (E+1)) :
      ceilWidth 133221 (C-133219*n)=
        (if n≤q then q+1-n else 0)+
          (if n≤q+1 ∧ h≤n then 1 else 0) := by
    rw [ceilWidth_relaxed_formula C q s E n hrem hsW hE
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) hC]
    simp only [hthreshold n]
  have hdecomp :
    (∑ n ∈ Finset.range (E+1),
      triangleMultiplicity E n*ceilWidth 133221 (C-133219*n)) =
      (∑ n ∈ Finset.range (E+1),
        if n≤q then triangleMultiplicity E n*(q+1-n) else 0)+
      (∑ n ∈ Finset.range (E+1),
        if n≤q+1 ∧ h≤n then triangleMultiplicity E n else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hpoint n hn]
    split_ifs <;> ring
  have hprefix :
      (∑ n ∈ Finset.range (E+1),
        if n≤q then triangleMultiplicity E n*(q+1-n) else 0)+
      (∑ n ∈ Finset.range (E+1),
        if n≤q+1 ∧ h≤n then triangleMultiplicity E n else 0) =
      (triangleCardPrefix E q)*(q+1)-triangleWeightPrefix E q+
        (triangleCardPrefix E (q+1)-
          triangleCardPrefix E (min (q+1) (h-1))) := by
    rw [sum_if_le_eq_prefix,sum_if_between_eq_prefix_sub]
    · unfold triangleCardPrefix triangleWeightPrefix
      have hmain :
          (∑ n ∈ Finset.range (min E q+1),
            triangleMultiplicity E n*(q+1-n))=
          ∑ n ∈ Finset.range (min E q+1),
            (triangleMultiplicity E n*(q+1)-triangleMultiplicity E n*n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnq : n≤q := by
          have := Finset.mem_range.mp hn
          omega
        exact Nat.mul_sub_left_distrib _ _ _
      rw [hmain,Finset.sum_tsub_distrib,Finset.sum_mul]
      · congr 2
        · apply Finset.sum_congr
          · ext n
            simp only [Finset.mem_range]
            omega
          · intro n hn
            rfl
      · intro n hn
        have hnq : n≤q := by
          have := Finset.mem_range.mp hn
          omega
        exact Nat.mul_le_mul_left _ (hnq.trans (Nat.le_succ q))
    · dsimp [h]
      omega
  have hnat := hdecomp.trans hprefix
  rw [hnat]
  have hweight : triangleWeightPrefix E q≤triangleCardPrefix E q*(q+1) := by
    unfold triangleWeightPrefix triangleCardPrefix
    calc
      (∑ n ∈ Finset.range (min E q+1), triangleMultiplicity E n*n)
          ≤ ∑ n ∈ Finset.range (min E q+1),
              triangleMultiplicity E n*(q+1) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnq : n≤q := by
              have := Finset.mem_range.mp hn
              omega
            exact Nat.mul_le_mul_left _ (hnq.trans (Nat.le_succ q))
      _ = (∑ n ∈ Finset.range (min E q+1), triangleMultiplicity E n)*(q+1) := by
            rw [Finset.sum_mul]
  have hcard : triangleCardPrefix E (min (q+1) (h-1))≤
      triangleCardPrefix E (q+1) := by
    unfold triangleCardPrefix
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.range_mono
      omega
    · intro n hn hnot
      exact Nat.zero_le _
  rw [Nat.cast_add,Nat.cast_sub hweight,Nat.cast_sub hcard,Nat.cast_mul]
  rw [triangleCardPrefix_cast,triangleWeightPrefix_cast,
    triangleCardPrefix_cast,triangleCardPrefix_cast]
  unfold relaxedClosedQ
  dsimp [q,s,h]
  push_cast
  ring

end ProximityPrize.SubmissionLower.WeightedRelaxedFibreFormulaW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedRelaxedFibreFormulaW1332216900.ceilWidth_relaxed_formula
#print axioms ProximityPrize.SubmissionLower.WeightedRelaxedFibreFormulaW1332216900.triangleRelaxedCount_cast_closed
