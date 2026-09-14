import WeightedFinitePrefixPrimaryLowShiftW1332216900

/-! Memory-bounded proof of the exact low target rank for the non-`9*k`
primary contact order.  The shift from 531 to 533 is pointwise and generic. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowRankW1332216900

open scoped BigOperators
open Order2SourceBasisScaffold
open Order2FiniteFlagUnion6900
open Order2LowFlagRankSum6900
open WeightedQuadricContactTarget6900
open WeightedFinitePrefixPrimaryLowShiftW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

/-- In the unclipped low block, adding `c` to contact order adds exactly `c`
copies of the derivative-weight monomial count. -/
theorem weightedFlagUnionRank_shift (k c d : Nat) (hd : d<4*k) :
    weightedFlagUnionRank (9*k+c) d (4*k)=
      weightedFlagUnionRank (9*k) d (4*k)+
        c*weightedMonomialCount d (4*k) := by
  rw [weightedFlagUnionRank_unclipped (9*k+c) d (4*k) (by omega),
    weightedFlagUnionRank_unclipped (9*k) d (4*k) (by omega)]
  have heq : 9*k+c-d=(9*k-d)+c := by omega
  rw [heq]
  ring

theorem lowRankSum_shift (k c : Nat) :
    lowRankSum (9*k+c) k=lowRankSum (9*k) k+
      c*(∑ d ∈ Finset.range (4*k),weightedMonomialCount d (4*k)) := by
  unfold lowRankSum
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact weightedFlagUnionRank_shift k c d (Finset.mem_range.mp hd)

private theorem solve_low_union (n : Nat)
    (h : 6*n=3654472626) : n=609078771 := by
  omega

/-- Exact low rank at `(m,k)=(533,59)`.  Notice that `533=9*59+2`, not
`9*59`; this theorem accounts for the extra two copies explicitly. -/
theorem lowRankSum_533_59 : lowRankSum 533 59=612420767 := by
  have hshift := lowRankSum_shift 59 2
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at hshift
  have hold := Order2LowFlagRankSum6900.lowUnionRank_nine_four_six 59
  rw [show 59*(2*59+1)^2*(74*59+8)=3654472626 by norm_num] at hold
  have hold_value : Order2LowFlagRankSum6900.lowUnionRank 59=609078771 :=
    solve_low_union _ hold
  have hbase : lowRankSum 531 59=
      Order2LowFlagRankSum6900.lowUnionRank 59 := by rfl
  rw [hshift,hbase,hold_value,weightedMonomialCount_sum_59]

end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowRankW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowRankW1332216900.weightedFlagUnionRank_shift
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowRankW1332216900.lowRankSum_shift
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowRankW1332216900.lowRankSum_533_59
