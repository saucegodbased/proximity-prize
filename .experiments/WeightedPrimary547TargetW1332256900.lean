import WeightedCutoff2TargetW1332256900

/-! Exact target-rank receipt for the hard-branch primary source
`(m,M,k)=(547,740,61)` at W=133225. -/
namespace ProximityPrize.SubmissionLower.WeightedPrimary547TargetW1332256900

open scoped BigOperators
open Order2LowFlagRankSum6900
open WeightedQuadricContactTarget6900
open WeightedQuadricHighTruncation6900
open WeightedQuadricHighRankSum6900
open WeightedFinitePrefixHelperRankW1332196900
open WeightedFinitePrefixPrimaryLowRankW1332246900
open WeightedFinitePrefixPrimaryHighTailW1332246900
open WeightedIdentityCoreTargetW1332256900
open WeightedCutoff2TargetW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
noncomputable section

theorem lowRankSum_547_61 : lowRankSum 547 61=691844127 := by
  have h := lowRankSum_downshift 61 2 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  have hbase : lowRankSum 549 61=
      Order2LowFlagRankSum6900.lowUnionRank 61 := by rfl
  have hold := Order2LowFlagRankSum6900.lowUnionRank_nine_four_six 61
  have holdv : Order2LowFlagRankSum6900.lowUnionRank 61=695535603 := by
    rw [show 61*(2*61+1)^2*(74*61+8)=4173213618 by norm_num] at hold
    omega
  rw [hbase,holdv,weightedMonomialCount_sum_61] at h
  omega

theorem highTailRank_547_122 : highTailRank 547 122=792144354 := by
  have h := highTailRank_six_eq_full_rectangle 547 122 (by norm_num)
  have hsum :
      (∑ i ∈ Finset.range (122+1),
        ((547-3*i)*(547-3*i+1)*(547-3*i+2)-
          (547-3*i-(122+1))*(547-3*i-(122+1)+1)*
            (547-3*i-(122+1)+2)))=4752866124 := by
    have hcast :
        (((∑ i ∈ Finset.range (122+1),
          ((547-3*i)*(547-3*i+1)*(547-3*i+2)-
            (547-3*i-(122+1))*(547-3*i-(122+1)+1)*
              (547-3*i-(122+1)+2))):Nat):ℚ)=
          ∑ i ∈ Finset.range (122+1),
            (87800844+(-1077111)*(i:ℚ)+3321*(i:ℚ)^2) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hthree : 3*i≤547 := by omega
      have htail : 122+1≤547-3*i := by omega
      have hprod :
          (547-3*i-(122+1))*(547-3*i-(122+1)+1)*
              (547-3*i-(122+1)+2)≤
            (547-3*i)*(547-3*i+1)*(547-3*i+2) := by
        have hb : 547-3*i-(122+1)≤547-3*i := Nat.sub_le _ _
        exact Nat.mul_le_mul (Nat.mul_le_mul hb (Nat.add_le_add_right hb 1))
          (Nat.add_le_add_right hb 2)
      rw [Nat.cast_sub hprod]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      rw [Nat.cast_sub hthree,Nat.cast_sub htail,Nat.cast_sub hthree]
      push_cast
      ring
    have hrat :
        (∑ i ∈ Finset.range (122+1),
          (87800844+(-1077111)*(i:ℚ)+3321*(i:ℚ)^2))=
            (4752866124:ℚ) := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum]
      norm_num
    exact_mod_cast hcast.trans hrat
  rw [hsum] at h
  omega

theorem finiteHighPrefix_547_497_122 :
    (∑ s ∈ Finset.range 497,highRankBound 547 (s+244) 122)=792039090 := by
  have h := highTailRank_prefix_add_shifted_tail 547 497 122 (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceSub] at h
  rw [highTailRank_547_122,
    WeightedCutoff2TargetW1332256900.highTailRank_50_122] at h
  omega

theorem primary_totalTarget_rank_le (K : Type*) [Field K]
    (htwo : (2:K)≠0) :
    Module.finrank K (totalTarget K 547 740 61)≤1483883217 := by
  have h := totalTarget_finrank_le_exact_prefix K htwo 547 740 61
    (by norm_num)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [lowRankSum_547_61,finiteHighPrefix_547_497_122] at h
  exact h

end
end ProximityPrize.SubmissionLower.WeightedPrimary547TargetW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedPrimary547TargetW1332256900.primary_totalTarget_rank_le
