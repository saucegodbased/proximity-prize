import WeightedIdentityCoreTargetW1332256900

/-!
# Exact local target ranks for the cutoff-two W=133225 sources

The primary profile is `(m,M,k)=(546,739,61)` and the helper profile is
`(11810,15993,1312)`.  Every large finite sum below is reduced through the
closed polynomial-sum lemmas; no evaluator decision procedure is used.
-/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2TargetW1332256900

open scoped BigOperators
open Order2FiniteFlagUnion6900
open Order2LowFlagRankSum6900
open WeightedQuadricContactTarget6900
open WeightedQuadricHighTruncation6900
open WeightedQuadricHighRankSum6900
open WeightedFinitePrefixHelperRankW1332196900
open WeightedFinitePrefixPrimaryLowRankW1332246900
open WeightedFinitePrefixPrimaryHighTailW1332246900
open WeightedIdentityCoreTargetW1332256900
open NatPolynomialSumW1332246900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
noncomputable section

private theorem solve_div3_6029296000 (n : Nat)
    (h : 3*n=18087888000) : n=6029296000 := by omega
private theorem solve_div3_6022408000 (n : Nat)
    (h : 3*n=18067224000) : n=6022408000 := by omega
private theorem solve_div2_36155112000 (n : Nat)
    (h : 2*n=72310224000) : n=36155112000 := by omega
private theorem solve_div2_3014648000 (n : Nat)
    (h : 2*n=6029296000) : n=3014648000 := by omega
private theorem solve_upper_15066352000 (n : Nat)
    (h : 2*n+6022408000=36155112000) : n=15066352000 := by omega
private theorem solve_div6_146299398000000 (n : Nat)
    (h : 6*n=877796388000000) : n=146299398000000 := by omega
private theorem solve_div6_787560267 (n : Nat)
    (h : 6*n=4725361602) : n=787560267 := by omega
private theorem solve_div6_105264 (n : Nat)
    (h : 6*n=631584) : n=105264 := by omega
private theorem solve_div6_168160854421875 (n : Nat)
    (h : 6*n=1008965126531250) : n=168160854421875 := by omega
private theorem solve_div6_17968360855 (n : Nat)
    (h : 6*n=107810165130) : n=17968360855 := by omega

/-- Removing `c` contact layers in the unclipped low block removes exactly
`c` copies of the derivative-weight monomial count. -/
theorem weightedFlagUnionRank_downshift (k c d : Nat)
    (hc : c≤k) (hd : d<4*k) :
    weightedFlagUnionRank (9*k) d (4*k)=
      weightedFlagUnionRank (9*k-c) d (4*k)+
        c*weightedMonomialCount d (4*k) := by
  rw [weightedFlagUnionRank_unclipped (9*k) d (4*k) (by omega),
    weightedFlagUnionRank_unclipped (9*k-c) d (4*k) (by omega)]
  have heq : 9*k-d=(9*k-c-d)+c := by omega
  rw [heq]
  ring

theorem lowRankSum_downshift (k c : Nat) (hc : c≤k) :
    lowRankSum (9*k) k=lowRankSum (9*k-c) k+
      c*(∑ d ∈ Finset.range (4*k),weightedMonomialCount d (4*k)) := by
  unfold lowRankSum
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact weightedFlagUnionRank_downshift k c d
    hc (Finset.mem_range.mp hd)

/-- Exact primary low rank at `(m,k)=(546,61)`. -/
theorem lowRankSum_546_61 : lowRankSum 546 61=689998389 := by
  have h := lowRankSum_downshift 61 3 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  have hbase : lowRankSum 549 61=
      Order2LowFlagRankSum6900.lowUnionRank 61 := by rfl
  have hold := Order2LowFlagRankSum6900.lowUnionRank_nine_four_six 61
  have holdv : Order2LowFlagRankSum6900.lowUnionRank 61=695535603 := by
    rw [show 61*(2*61+1)^2*(74*61+8)=4173213618 by norm_num] at hold
    omega
  rw [hbase,holdv,weightedMonomialCount_sum_61] at h
  omega

def monomialBlockQ (k j : Nat) : ℚ :=
  ((j+1)*(j+2)+
    ((2*k+1)*(2*k+2)+(4*k+2)*j-j*(j+1)))/2

/-- The two symmetric derivative-degree halves, paired before summation. -/
theorem weightedMonomialCount_pair_cast (k j : Nat) (hj : j<2*k) :
    ((weightedMonomialCount j (4*k)+
      weightedMonomialCount (2*k+j) (4*k):Nat):ℚ)=monomialBlockQ k j := by
  have hlo := weightedMonomialCount_low_twice k j (by omega)
  have hhi := weightedMonomialCount_upper_twice k j (by omega)
  have hloQ : 2*(weightedMonomialCount j (4*k):ℚ)=(j+1)*(j+2) := by
    exact_mod_cast hlo
  have hhiQ :
      2*(weightedMonomialCount (2*k+j) (4*k):ℚ)+(j:ℚ)*(j+1)=
        (2*k+1)*(2*k+2)+(4*k+2)*j := by
    exact_mod_cast hhi
  unfold monomialBlockQ
  push_cast
  linarith

theorem weightedMonomialCount_split (k : Nat) :
    (∑ d ∈ Finset.range (4*k),weightedMonomialCount d (4*k))=
      (∑ d ∈ Finset.range (2*k),weightedMonomialCount d (4*k))+
        ∑ j ∈ Finset.range (2*k),weightedMonomialCount (2*k+j) (4*k) := by
  conv_lhs => rw [show 4*k=2*k+2*k by omega,Finset.sum_range_add]
  rw [show 2*k+2*k=4*k by omega]

/-- Total derivative-weight monomial count in the `k=1312` low block. -/
theorem weightedMonomialCount_sum_1312 :
    (∑ d ∈ Finset.range 5248,weightedMonomialCount d 5248)=18081000000 := by
  have hcast :
      (((∑ d ∈ Finset.range 5248,weightedMonomialCount d 5248):Nat):ℚ)=
        ∑ j ∈ Finset.range 2624,monomialBlockQ 1312 j := by
    have hs := weightedMonomialCount_split 1312
    norm_num only [Nat.reduceMul,Nat.reduceAdd] at hs
    rw [hs]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hp := weightedMonomialCount_pair_cast 1312 j (Finset.mem_range.mp hj)
    norm_num only [Nat.reduceMul,Nat.reduceAdd] at hp
    push_cast at hp
    exact hp
  have heval :
      (∑ j ∈ Finset.range 2624,monomialBlockQ 1312 j)=
        (18081000000:ℚ) := by
    calc
      _ = ∑ j ∈ Finset.range (2623+1),
          (3446626+2626*(j:ℚ)+0*(j:ℚ)^2) := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold monomialBlockQ
        push_cast
        ring
      _ = _ := by
        rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum]
        norm_num
  generalize hS : (∑ d ∈ Finset.range 5248,
    weightedMonomialCount d 5248) = S at hcast ⊢
  exact_mod_cast hcast.trans heval

/-- Exact helper low rank; `11810=9*1312+2`. -/
theorem lowRankSum_11810_1312 : lowRankSum 11810 1312=146335560000000 := by
  have hshift := lowRankSum_shift 1312 2
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at hshift
  have hsum := weightedMonomialCount_sum_1312
  generalize hS : (∑ d ∈ Finset.range 5248,
    weightedMonomialCount d 5248) = S at hshift hsum
  rw [hsum] at hshift
  have hold := Order2LowFlagRankSum6900.lowUnionRank_nine_four_six 1312
  rw [show 1312*(2*1312+1)^2*(74*1312+8)=877796388000000 by norm_num] at hold
  have holdv : Order2LowFlagRankSum6900.lowUnionRank 1312=146299398000000 := by
    exact solve_div6_146299398000000 _ hold
  have hbase : lowRankSum 11808 1312=
      Order2LowFlagRankSum6900.lowUnionRank 1312 := by rfl
  rw [hshift,hbase,holdv]

/-- Complete primary high tail. -/
theorem highTailRank_546_122 : highTailRank 546 122=787560267 := by
  have h := highTailRank_six_eq_full_rectangle 546 122 (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range (122+1),
        ((546-3*i)*(546-3*i+1)*(546-3*i+2)-
          (546-3*i-(122+1))*(546-3*i-(122+1)+1)*
            (546-3*i-(122+1)+2)))=4725361602 := by
    have hcast :
        (((∑ i ∈ Finset.range (122+1),
          ((546-3*i)*(546-3*i+1)*(546-3*i+2)-
            (546-3*i-(122+1))*(546-3*i-(122+1)+1)*
              (546-3*i-(122+1)+2))):Nat):ℚ)=
          ∑ i ∈ Finset.range (122+1),
            (87442176+(-1074897)*(i:ℚ)+3321*(i:ℚ)^2) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤546 := by omega
      have htail : 122+1≤546-3*i := by omega
      have hprod :
          (546-3*i-(122+1))*(546-3*i-(122+1)+1)*
              (546-3*i-(122+1)+2) ≤
            (546-3*i)*(546-3*i+1)*(546-3*i+2) := by
        have hb : 546-3*i-(122+1)≤546-3*i := Nat.sub_le _ _
        exact Nat.mul_le_mul (Nat.mul_le_mul hb (Nat.add_le_add_right hb 1))
          (Nat.add_le_add_right hb 2)
      rw [Nat.cast_sub hprod]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      rw [Nat.cast_sub hthree,Nat.cast_sub htail,Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (122+1),
          (87442176+(-1074897)*(i:ℚ)+3321*(i:ℚ)^2))=(4725361602:ℚ) := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  exact solve_div6_787560267 _ h

theorem highTailRank_50_122 : highTailRank 50 122=105264 := by
  have h := highTailRank_six_eq_stride 50 122 17 (by norm_num)
    (fun i hi => by omega) (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range 17,(50-3*i)*(50-3*i+1)*(50-3*i+2))=631584 := by
    have hcast :
        (((∑ i ∈ Finset.range 17,
          (50-3*i)*(50-3*i+1)*(50-3*i+2)):Nat):ℚ)=
          ∑ i ∈ Finset.range (16+1),
            (132600+(-23406)*(i:ℚ)+1377*(i:ℚ)^2+(-27)*(i:ℚ)^3) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hthree : 3*i≤50 := by have := Finset.mem_range.mp hi; omega
      rw [Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (16+1),
          (132600+(-23406)*(i:ℚ)+1377*(i:ℚ)^2+(-27)*(i:ℚ)^3))=(631584:ℚ) := by
      rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  exact solve_div6_105264 _ h

theorem primaryFiniteHighPrefix :
    (∑ s ∈ Finset.range 496,highRankBound 546 (s+244) 122)=787455003 := by
  have h := highTailRank_prefix_add_shifted_tail 546 496 122 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  rw [highTailRank_546_122,highTailRank_50_122] at h
  omega

theorem primary_totalTarget_rank_le (K : Type*) [Field K] (htwo : (2:K)≠0) :
    Module.finrank K (totalTarget K 546 739 61)≤1477453392 := by
  have h := totalTarget_finrank_le_exact_prefix K htwo 546 739 61 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [lowRankSum_546_61,primaryFiniteHighPrefix] at h
  exact h

/-- Complete helper high tail. -/
theorem highTailRank_11810_2624 :
    highTailRank 11810 2624=168160854421875 := by
  have h := highTailRank_six_eq_full_rectangle 11810 2624 (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range (2624+1),
        ((11810-3*i)*(11810-3*i+1)*(11810-3*i+2)-
          (11810-3*i-(2624+1))*(11810-3*i-(2624+1)+1)*
            (11810-3*i-(2624+1)+2)))=1008965126531250 := by
    have hcast :
        (((∑ i ∈ Finset.range (2624+1),
          ((11810-3*i)*(11810-3*i+1)*(11810-3*i+2)-
            (11810-3*i-(2624+1))*(11810-3*i-(2624+1)+1)*
              (11810-3*i-(2624+1)+2))):Nat):ℚ)=
          ∑ i ∈ Finset.range (2624+1),
            (872492675250+(-496054125)*(i:ℚ)+70875*(i:ℚ)^2) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤11810 := by omega
      have htail : 2624+1≤11810-3*i := by omega
      have hprod :
          (11810-3*i-(2624+1))*(11810-3*i-(2624+1)+1)*
              (11810-3*i-(2624+1)+2)≤
            (11810-3*i)*(11810-3*i+1)*(11810-3*i+2) := by
        have hb : 11810-3*i-(2624+1)≤11810-3*i := Nat.sub_le _ _
        exact Nat.mul_le_mul (Nat.mul_le_mul hb (Nat.add_le_add_right hb 1))
          (Nat.add_le_add_right hb 2)
      rw [Nat.cast_sub hprod]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      rw [Nat.cast_sub hthree,Nat.cast_sub htail,Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (2624+1),
          (872492675250+(-496054125)*(i:ℚ)+70875*(i:ℚ)^2))=
            (1008965126531250:ℚ) := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  exact solve_div6_168160854421875 _ h

theorem highTailRank_1064_2624 : highTailRank 1064 2624=17968360855 := by
  have h := highTailRank_six_eq_stride 1064 2624 355 (by norm_num)
    (fun i hi => by omega) (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range 355,
        (1064-3*i)*(1064-3*i+1)*(1064-3*i+2))=107810165130 := by
    have hcast :
        (((∑ i ∈ Finset.range 355,
          (1064-3*i)*(1064-3*i+1)*(1064-3*i+2)):Nat):ℚ)=
          ∑ i ∈ Finset.range (354+1),
            (1207948560+(-10208022)*(i:ℚ)+28755*(i:ℚ)^2+
              (-27)*(i:ℚ)^3) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hthree : 3*i≤1064 := by have := Finset.mem_range.mp hi; omega
      rw [Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (354+1),
          (1207948560+(-10208022)*(i:ℚ)+28755*(i:ℚ)^2+
            (-27)*(i:ℚ)^3))=(107810165130:ℚ) := by
      rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  exact solve_div6_17968360855 _ h

theorem helperFiniteHighPrefix :
    (∑ s ∈ Finset.range 10746,highRankBound 11810 (s+5248) 2624)=
      168142886061020 := by
  have h := highTailRank_prefix_add_shifted_tail 11810 10746 2624 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  rw [highTailRank_11810_2624,highTailRank_1064_2624] at h
  omega

theorem helper_totalTarget_rank_le (K : Type*) [Field K] (htwo : (2:K)≠0) :
    Module.finrank K (totalTarget K 11810 15993 1312)≤314478446061020 := by
  have h := totalTarget_finrank_le_exact_prefix K htwo 11810 15993 1312
    (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [lowRankSum_11810_1312,helperFiniteHighPrefix] at h
  exact h

end
end ProximityPrize.SubmissionLower.WeightedCutoff2TargetW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2TargetW1332256900.primary_totalTarget_rank_le
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2TargetW1332256900.helper_totalTarget_rank_le
