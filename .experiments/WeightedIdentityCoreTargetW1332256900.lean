import WeightedFinitePrefixPrimaryLowRankW1332246900
import WeightedFinitePrefixPrimaryHighTailW1332246900

/-!
# Exact local target rank for the W=133225 identity-core helper

The helper profile is `(m, B, W, k)=(550, 99227150, 133225, 61)`.
This file evaluates its literal finite-prefix contact target without `decide`
or `native_decide`.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityCoreTargetW1332256900

open scoped BigOperators
open Order2LowFlagRankSum6900
open WeightedQuadricContactTarget6900
open WeightedQuadricHighTruncation6900
open WeightedQuadricHighRankSum6900
open WeightedFinitePrefixHelperRankW1332196900
open WeightedFinitePrefixPrimaryLowRankW1332246900
open WeightedFinitePrefixPrimaryHighTailW1332246900
open NatPolynomialSumW1332246900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2400
noncomputable section

private theorem solve_low_count (n : Nat) (h : 2*n=620248) : n=310124 := by
  omega

private theorem solve_upper_count (n : Nat)
    (h : 2*n+605242=3676470) : n=1535614 := by
  omega

private theorem solve_low_union (n : Nat)
    (h : 6*n=4173213618) : n=695535603 := by
  omega

private theorem solve_low_rhs (n : Nat)
    (h : 3*n=1860744) : n=620248 := by
  omega

private theorem solve_adjacent_rhs (n : Nat)
    (h : 3*n=1815726) : n=605242 := by
  omega

private theorem solve_affine_rhs (n : Nat)
    (h : 2*n=7352940) : n=3676470 := by
  omega

/-- Total derivative-weight monomial count across the `k=61` low block. -/
theorem weightedMonomialCount_sum_61 :
    (∑ d ∈ Finset.range 244, weightedMonomialCount d 244)=1845738 := by
  have hlow :
      2*(∑ d ∈ Finset.range 122, weightedMonomialCount d 244)=
        ∑ d ∈ Finset.range 122, (d+1)*(d+2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact weightedMonomialCount_low_twice 61 d
      (by have := Finset.mem_range.mp hd; omega)
  have hupp :
      2*(∑ j ∈ Finset.range 122, weightedMonomialCount (122+j) 244)+
          (∑ j ∈ Finset.range 122, j*(j+1))=
        ∑ j ∈ Finset.range 122, (123*124+246*j) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      weightedMonomialCount_upper_twice 61 j
        (by have := Finset.mem_range.mp hj; omega)
  have hsplit :
      (∑ d ∈ Finset.range 244, weightedMonomialCount d 244)=
        (∑ d ∈ Finset.range 122, weightedMonomialCount d 244)+
          ∑ j ∈ Finset.range 122, weightedMonomialCount (122+j) 244 := by
    conv_lhs => rw [show 244=122+122 by norm_num,Finset.sum_range_add]
  have hlow_rhs :
      (∑ d ∈ Finset.range 122,(d+1)*(d+2))=620248 := by
    have h := shifted_pair_sum_three 122
    rw [show 122*(122+1)*(122+2)=1860744 by norm_num] at h
    exact solve_low_rhs _ h
  have hj_rhs :
      (∑ j ∈ Finset.range 122,j*(j+1))=605242 := by
    have h := adjacent_pair_sum_three 121
    rw [show 121*(121+1)*(121+2)=1815726 by norm_num] at h
    exact solve_adjacent_rhs _ h
  have hupp_rhs :
      (∑ j ∈ Finset.range 122,(123*124+246*j))=3676470 := by
    have h := affine_sum_two 121 15252 246
    rw [show 2*(121+1)*15252+246*121*(121+1)=7352940 by norm_num] at h
    exact solve_affine_rhs _ h
  rw [hlow_rhs] at hlow
  have hlow_value :
      (∑ d ∈ Finset.range 122,weightedMonomialCount d 244)=310124 :=
    solve_low_count _ hlow
  rw [hj_rhs,hupp_rhs] at hupp
  have hupp_value :
      (∑ j ∈ Finset.range 122,weightedMonomialCount (122+j) 244)=1535614 :=
    solve_upper_count _ hupp
  rw [hsplit,hlow_value,hupp_value]

/-- Exact low target rank.  Here `550=9*61+1`. -/
theorem lowRankSum_550_61 : lowRankSum 550 61=697381341 := by
  have hshift := lowRankSum_shift 61 1
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at hshift
  have hold := Order2LowFlagRankSum6900.lowUnionRank_nine_four_six 61
  rw [show 61*(2*61+1)^2*(74*61+8)=4173213618 by norm_num] at hold
  have hold_value : Order2LowFlagRankSum6900.lowUnionRank 61=695535603 :=
    solve_low_union _ hold
  have hbase : lowRankSum 549 61=
      Order2LowFlagRankSum6900.lowUnionRank 61 := by rfl
  rw [hshift,hbase,hold_value,weightedMonomialCount_sum_61]

/-- Complete high tail at `(m,k)=(550,122)`. -/
theorem highTailRank_550_122 : highTailRank 550 122=805987389 := by
  have h := highTailRank_six_eq_full_rectangle 550 122 (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range (122+1),
        ((550-3*i)*(550-3*i+1)*(550-3*i+2)-
          (550-3*i-(122+1))*(550-3*i-(122+1)+1)*
            (550-3*i-(122+1)+2)))=4835924334 := by
    have hcast :
        (((∑ i ∈ Finset.range (122+1),
          ((550-3*i)*(550-3*i+1)*(550-3*i+2)-
            (550-3*i-(122+1))*(550-3*i-(122+1)+1)*
              (550-3*i-(122+1)+2))):Nat):ℚ)=
          ∑ i ∈ Finset.range (122+1),
            (88881276+(-1083753)*(i:ℚ)+3321*(i:ℚ)^2) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤550 := by omega
      have htail : 122+1≤550-3*i := by omega
      have hprod :
          (550-3*i-(122+1))*(550-3*i-(122+1)+1)*
              (550-3*i-(122+1)+2) ≤
            (550-3*i)*(550-3*i+1)*(550-3*i+2) := by
        have hbase : 550-3*i-(122+1) ≤ 550-3*i := Nat.sub_le _ _
        exact Nat.mul_le_mul
          (Nat.mul_le_mul hbase (Nat.add_le_add_right hbase 1))
          (Nat.add_le_add_right hbase 2)
      rw [Nat.cast_sub hprod]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      rw [Nat.cast_sub hthree,Nat.cast_sub htail,Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (122+1),
          (88881276+(-1083753)*(i:ℚ)+3321*(i:ℚ)^2))=
            (4835924334:ℚ) := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  omega

/-- The 49 unreachable high levels omitted by the literal `M=744` cutoff. -/
theorem highTailRank_49_122 : highTailRank 49 122=97461 := by
  have h := highTailRank_six_eq_stride 49 122 17 (by norm_num)
    (fun i hi => by omega) (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range 17,(49-3*i)*(49-3*i+1)*(49-3*i+2))=
        584766 := by
    have hcast :
        (((∑ i ∈ Finset.range 17,
          (49-3*i)*(49-3*i+1)*(49-3*i+2)):Nat):ℚ)=
          ∑ i ∈ Finset.range (16+1),
            (124950+(-22497)*(i:ℚ)+1350*(i:ℚ)^2+(-27)*(i:ℚ)^3) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤49 := by omega
      rw [Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (16+1),
          (124950+(-22497)*(i:ℚ)+1350*(i:ℚ)^2+(-27)*(i:ℚ)^3))=
            (584766:ℚ) := by
      rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  omega

/-- Exact literal high prefix, through source total degree `M=744`. -/
theorem finiteHighPrefix_550_501_122 :
    (∑ s ∈ Finset.range 501,highRankBound 550 (s+244) 122)=805889928 := by
  have h := highTailRank_prefix_add_shifted_tail 550 501 122 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  rw [highTailRank_550_122,highTailRank_49_122] at h
  omega

/-- Exact local-rank upper bound used by the identity-core helper. -/
theorem helper_totalTarget_rank_le (K : Type*) [Field K] (htwo : (2:K)≠0) :
    Module.finrank K (totalTarget K 550 744 61)≤1503271269 := by
  have h := totalTarget_finrank_le_exact_prefix K htwo 550 744 61 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [lowRankSum_550_61,finiteHighPrefix_550_501_122] at h
  exact h

#print axioms weightedMonomialCount_sum_61
#print axioms lowRankSum_550_61
#print axioms highTailRank_550_122
#print axioms highTailRank_49_122
#print axioms finiteHighPrefix_550_501_122
#print axioms helper_totalTarget_rank_le

end
end ProximityPrize.SubmissionLower.WeightedIdentityCoreTargetW1332256900
