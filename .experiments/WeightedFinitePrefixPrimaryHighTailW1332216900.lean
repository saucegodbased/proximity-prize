import WeightedFinitePrefixHelperRankW1332196900

/-! Separately compiled finite-high-tail arithmetic for the W=133221 primary
source.  All large finite sums are reduced through symbolic quadratic/cubic
sum formulas, not evaluator expansion. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryHighTailW1332216900

open scoped BigOperators
open WeightedQuadricHighTruncation6900
open WeightedQuadricHighRankSum6900
open WeightedFinitePrefixHelperRankW1332196900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000

/-- A finite high tail as a sum of stride-three tetrahedral numerators. -/
theorem highTailRank_six_eq_stride
    (m k n : Nat) (hmk : m≤k+1)
    (hactive : ∀ i<n,3*i<m) (hzero : m≤3*n) :
    6*highTailRank m k=
      ∑ i ∈ Finset.range n,(m-3*i)*(m-3*i+1)*(m-3*i+2) := by
  let f : Nat→Nat := fun i =>
    ∑ j ∈ Finset.range (k+1), tailTerm m i j
  have hrow_active (i : Nat) (hi : i<n) :
      3*f i=(m-3*i)*(m-3*i+1)*(m-3*i+2) := by
    have him : 3*i<m := hactive i hi
    have hsmall : m-3*i≤k+1 := (Nat.sub_le _ _).trans hmk
    have hrestrict :
        (∑ j ∈ Finset.range (m-3*i),tailTerm m i j)=f i := by
      dsimp only [f]
      apply Finset.sum_subset (Finset.range_mono hsmall)
      intro j hj hnot
      have hjlarge : m-3*i≤j := by
        by_contra hn
        exact hnot (Finset.mem_range.mpr (by omega))
      have hz : m-(3*i+j)=0 := Nat.sub_eq_zero_of_le (by omega)
      simp [tailTerm,hz]
    have hsmallform :
        (∑ j ∈ Finset.range (m-3*i),tailTerm m i j)=
          ∑ j ∈ Finset.range (m-3*i),(m-3*i-j)*(m-3*i-j+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold tailTerm
      have heq : m-(3*i+j)=m-3*i-j := by omega
      rw [heq]
    rw [← hrestrict,hsmallform,descending_pair_sum_three]
  have hrow_zero (i : Nat) (hi : n ≤ i) : f i=0 := by
    dsimp only [f]
    apply Finset.sum_eq_zero
    intro j hj
    have hz : m-(3*i+j)=0 := Nat.sub_eq_zero_of_le (by omega)
    simp [tailTerm,hz]
  have htruncate :
      (∑ i ∈ Finset.range n,f i)=∑ i ∈ Finset.range (k+1),f i := by
    have hnk : n≤k+1 := by
      by_contra hn
      have hkn : k+1<n := Nat.lt_of_not_ge hn
      have ha := hactive (k+1) hkn
      omega
    apply Finset.sum_subset (Finset.range_mono hnk)
    intro i hi hnot
    have hni : n ≤ i := Nat.le_of_not_gt
      (fun hil => hnot (Finset.mem_range.mpr hil))
    exact hrow_zero i hni
  have htwice := highTailRank_twice m k
  have hrect := rectangle_sum_eq_ranges_nat k (tailTerm m)
  have htwo : 2*highTailRank m k=∑ i ∈ Finset.range (k+1),f i :=
    htwice.trans (by simpa [f,tailTerm] using hrect)
  calc
    6*highTailRank m k=3*(2*highTailRank m k) := by ring
    _=3*(∑ i ∈ Finset.range n,f i) := by rw [htwo,← htruncate]
    _=∑ i ∈ Finset.range n,3*f i := Finset.mul_sum ..
    _=_ := Finset.sum_congr rfl fun i hi => hrow_active i (Finset.mem_range.mp hi)

theorem descending_pair_prefix_three (L q : Nat) (hq : q≤L) :
    3*(∑ j ∈ Finset.range q,(L-j)*(L-j+1))=
      L*(L+1)*(L+2)-(L-q)*(L-q+1)*(L-q+2) := by
  have hall := descending_pair_sum_three L
  have htail := descending_pair_sum_three (L-q)
  have hsplit :
      (∑ j ∈ Finset.range L,(L-j)*(L-j+1))=
        (∑ j ∈ Finset.range q,(L-j)*(L-j+1))+
          ∑ j ∈ Finset.range (L-q),((L-q)-j)*((L-q)-j+1) := by
    calc
      _=∑ j ∈ Finset.range (q+(L-q)),(L-j)*(L-j+1) := by
        rw [show q+(L-q)=L by omega]
      _=_ := by
        rw [Finset.sum_range_add]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have heq : L-(q+j)=L-q-j := by omega
        rw [heq]
  omega

/-- Closed finite-rectangle tail formula when every row remains active. -/
theorem highTailRank_six_eq_full_rectangle
    (m k : Nat) (hfull : 4*k+1≤m) :
    6*highTailRank m k=
      ∑ i ∈ Finset.range (k+1),
        ((m-3*i)*(m-3*i+1)*(m-3*i+2)-
          (m-3*i-(k+1))*(m-3*i-(k+1)+1)*(m-3*i-(k+1)+2)) := by
  let f : Nat→Nat := fun i =>
    ∑ j ∈ Finset.range (k+1),tailTerm m i j
  have hrow (i : Nat) (hi : i<k+1) :
      3*f i=(m-3*i)*(m-3*i+1)*(m-3*i+2)-
        (m-3*i-(k+1))*(m-3*i-(k+1)+1)*(m-3*i-(k+1)+2) := by
    have hq : k+1≤m-3*i := by omega
    have hform := descending_pair_prefix_three (m-3*i) (k+1) hq
    have heq : f i=∑ j ∈ Finset.range (k+1),
        (m-3*i-j)*(m-3*i-j+1) := by
      dsimp only [f]
      apply Finset.sum_congr rfl
      intro j hj
      unfold tailTerm
      have heqbase : m-(3*i+j)=m-3*i-j := by omega
      rw [heqbase]
    rw [heq]
    exact hform
  have htwice := highTailRank_twice m k
  have hrect := rectangle_sum_eq_ranges_nat k (tailTerm m)
  have htwo : 2*highTailRank m k=∑ i ∈ Finset.range (k+1),f i :=
    htwice.trans (by simpa [f,tailTerm] using hrect)
  calc
    6*highTailRank m k=3*(2*highTailRank m k) := by ring
    _=3*(∑ i ∈ Finset.range (k+1),f i) := by rw [htwo]
    _=∑ i ∈ Finset.range (k+1),3*f i := Finset.mul_sum ..
    _=_ := Finset.sum_congr rfl fun i hi => hrow i (Finset.mem_range.mp hi)

theorem highTailRank_533_118 : highTailRank 533 118=710216633 := by
  have h := highTailRank_six_eq_full_rectangle 533 118 (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range (118+1),
        ((533-3*i)*(533-3*i+1)*(533-3*i+2)-
          (533-3*i-(118+1))*(533-3*i-(118+1)+1)*
            (533-3*i-(118+1)+2)))=4261299798 := by
    have hcast :
        ((∑ i ∈ Finset.range (118+1),
          ((533-3*i)*(533-3*i+1)*(533-3*i+2)-
            (533-3*i-(118+1))*(533-3*i-(118+1)+1)*
              (533-3*i-(118+1)+2)) : Nat) : ℚ)=
          ∑ i ∈ Finset.range (118+1),
            (80799810+(-1016379)*(i:ℚ)+3213*(i:ℚ)^2) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤533 := by omega
      have htail : 118+1≤533-3*i := by omega
      have hprod :
          (533-3*i-(118+1))*(533-3*i-(118+1)+1)*
              (533-3*i-(118+1)+2) ≤
            (533-3*i)*(533-3*i+1)*(533-3*i+2) := by
        have hbase : 533-3*i-(118+1) ≤ 533-3*i := Nat.sub_le _ _
        exact Nat.mul_le_mul
          (Nat.mul_le_mul hbase (Nat.add_le_add_right hbase 1))
          (Nat.add_le_add_right hbase 2)
      rw [Nat.cast_sub hprod]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      rw [Nat.cast_sub hthree,Nat.cast_sub htail,Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (118+1),
          (80799810+(-1016379)*(i:ℚ)+3213*(i:ℚ)^2))=(4261299798:ℚ) := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  omega

theorem highTailRank_47_118 : highTailRank 47 118=83164 := by
  have h := highTailRank_six_eq_stride 47 118 16 (by norm_num)
    (fun i hi => by omega) (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range 16,(47-3*i)*(47-3*i+1)*(47-3*i+2))=498984 := by
    have hcast :
        ((∑ i ∈ Finset.range 16,
          (47-3*i)*(47-3*i+1)*(47-3*i+2) : Nat) : ℚ)=
          ∑ i ∈ Finset.range (15+1),
            (110544+(-20733)*(i:ℚ)+1296*(i:ℚ)^2+(-27)*(i:ℚ)^3) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤47 := by omega
      rw [Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (15+1),
          (110544+(-20733)*(i:ℚ)+1296*(i:ℚ)^2+(-27)*(i:ℚ)^3))=(498984:ℚ) := by
      rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  omega

end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryHighTailW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryHighTailW1332216900.highTailRank_six_eq_stride
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryHighTailW1332216900.highTailRank_six_eq_full_rectangle
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryHighTailW1332216900.highTailRank_533_118
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryHighTailW1332216900.highTailRank_47_118
