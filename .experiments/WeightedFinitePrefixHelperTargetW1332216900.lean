import WeightedFinitePrefixHelperRankW1332196900

/-!
Finite-prefix target-rank specialization for the W=133221 helper.

The helper still has `m = 9*k`, so the existing closed low/full-high formulas
apply.  Its literal source cutoff is `M = 15259`; consequently only `10252`
of the `11268` high layers are present.  The omitted tail is evaluated below
without `decide` or `native_decide`.
-/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperTargetW1332216900

open scoped BigOperators
open WeightedQuadricContactTarget6900
open WeightedQuadricHighTruncation6900
open WeightedQuadricHighRankSum6900
open Order2LowFlagRankSum6900
open WeightedFinitePrefixHelperRankW1332196900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
noncomputable section

variable (K : Type*) [Field K]

def helperTailLevel (i : Nat) : Nat := 1016-3*i

def helperTailTerm (i j : Nat) : Nat :=
  (1016-(3*i+j))*(1016-(3*i+j)+1)

theorem helper_tail_row (i : Nat) (hi : i<339) :
    (∑ j ∈ Finset.range (helperTailLevel i), helperTailTerm i j)=
      helperTailLevel i*(helperTailLevel i+1)*(helperTailLevel i+2)/3 := by
  have hformula := descending_pair_sum_three (helperTailLevel i)
  have hterms :
      (∑ j ∈ Finset.range (helperTailLevel i), helperTailTerm i j)=
        ∑ j ∈ Finset.range (helperTailLevel i),
          (helperTailLevel i-j)*(helperTailLevel i-j+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    unfold helperTailTerm helperTailLevel
    congr 1 <;> omega
  rw [hterms]
  exact Nat.eq_div_of_mul_eq_right (by norm_num) hformula

theorem helper_tail_rows_numeric :
    (∑ i ∈ Finset.range 339,
      helperTailLevel i*(helperTailLevel i+1)*(helperTailLevel i+2)/3)=
        29890894470 := by
  norm_num [helperTailLevel,Finset.sum_range_succ]

theorem omitted_helper_high_tail_rank_lower :
    14945447235≤highTailRank 1016 2504 := by
  have hrows :
      (∑ i ∈ Finset.range 339, ∑ j ∈ Finset.range (helperTailLevel i),
        helperTailTerm i j)=29890894470 := by
    calc
      _ = ∑ i ∈ Finset.range 339,
          helperTailLevel i*(helperTailLevel i+1)*(helperTailLevel i+2)/3 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact helper_tail_row i (Finset.mem_range.mp hi)
      _ = _ := helper_tail_rows_numeric
  have houter :
      (∑ i ∈ Finset.range 339, ∑ j ∈ Finset.range (helperTailLevel i),
          helperTailTerm i j)≤
        ∑ i ∈ Finset.range 2505, ∑ j ∈ Finset.range 2505,
          helperTailTerm i j := by
    apply (sum_range_mono_nat
      (fun i => ∑ j ∈ Finset.range (helperTailLevel i), helperTailTerm i j)
      339 2505 (by norm_num)).trans
    apply Finset.sum_le_sum
    intro i hi
    apply sum_range_mono_nat
    have hi' := Finset.mem_range.mp hi
    unfold helperTailLevel
    omega
  have htwice := highTailRank_twice 1016 2504
  have hrect := rectangle_sum_eq_ranges_nat 2504
    (fun i j => helperTailTerm i j)
  have htwiceRange :
      2*highTailRank 1016 2504=
        ∑ i ∈ Finset.range 2505, ∑ j ∈ Finset.range 2505,
          helperTailTerm i j := by
    rw [htwice]
    simpa [helperTailTerm] using hrect
  rw [hrows] at houter
  rw [← htwiceRange] at houter
  omega

/-- Exact finite-prefix local-rank upper bound used by the W=133221 helper. -/
theorem helper_totalTarget_rank_le (htwo : (2:K)≠0) :
    Module.finrank K (totalTarget K 11268 15259 1252)≤260685624246315 := by
  have hp := totalTarget_finrank_le_exact_prefix K htwo 11268 15259 1252
    (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at hp
  have ht := highTailRank_prefix_add_shifted_tail 11268 10252 2504 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at ht
  have href :
      (∑ s ∈ Finset.range 10252, highRankBound 11268 (s+5008) 2504)+
          14945447235≤highTailRank 11268 2504 := by
    rw [ht]
    exact Nat.add_le_add_left omitted_helper_high_tail_rank_lower _
  have hlow := Order2LowFlagRankSum6900.lowUnionRank_nine_four_six 1252
  rw [WeightedFinitePrefixHelperRankW1332196900.lowUnionRank_eq_lowRankSum] at hlow
  have hhigh := highTailRank_nine_four_six 1252
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reducePow] at hlow hhigh
  have hsum :
      lowRankSum 11268 1252+highTailRank 11268 2504=260700569693550 := by
    omega
  have hrplus :
      Module.finrank K (totalTarget K 11268 15259 1252)+14945447235≤
        lowRankSum 11268 1252+highTailRank 11268 2504 := by
    calc
      _ ≤ (lowRankSum 11268 1252+
          ∑ s ∈ Finset.range 10252, highRankBound 11268 (s+5008) 2504)+
            14945447235 := Nat.add_le_add_right hp _
      _ = lowRankSum 11268 1252+
          ((∑ s ∈ Finset.range 10252, highRankBound 11268 (s+5008) 2504)+
            14945447235) := Nat.add_assoc _ _ _
      _ ≤ _ := Nat.add_le_add_left href _
  rw [hsum] at hrplus
  omega

end
end ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperTargetW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperTargetW1332216900.omitted_helper_high_tail_rank_lower
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperTargetW1332216900.helper_totalTarget_rank_le
