import NatPolynomialSumW1332216900

/-! Small, separately compiled receipt for the non-`9*k` low-rank shift used
at primary contact order 533 and derivative parameter 59. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowShiftW1332216900

open scoped BigOperators
open Order2SourceBasisScaffold
open Order2LowFlagRankSum6900
open WeightedQuadricContactTarget6900
open WeightedQuadricHighRankSum6900
open NatPolynomialSumW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000

private theorem solve_low_count (n : Nat) (h : 2*n=561680) : n=280840 := by
  omega

private theorem solve_upper_count (n : Nat)
    (h : 2*n+547638=3327954) : n=1390158 := by
  omega

private theorem solve_low_union (n : Nat)
    (h : 6*n=3654472626) : n=609078771 := by
  omega

private theorem solve_low_rhs (n : Nat)
    (h : 3*n=1685040) : n=561680 := by
  omega

private theorem solve_adjacent_rhs (n : Nat)
    (h : 3*n=1642914) : n=547638 := by
  omega

private theorem solve_affine_rhs (n : Nat)
    (h : 2*n=6655908) : n=3327954 := by
  omega

/-- Total number of derivative-weight monomials across the low block. -/
theorem weightedMonomialCount_sum_59 :
    (∑ d ∈ Finset.range 236,weightedMonomialCount d 236)=1670998 := by
  have hlow :
      2*(∑ d ∈ Finset.range 118,weightedMonomialCount d 236)=
        ∑ d ∈ Finset.range 118,(d+1)*(d+2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact weightedMonomialCount_low_twice 59 d
      (by have := Finset.mem_range.mp hd; omega)
  have hupp :
      2*(∑ j ∈ Finset.range 118,weightedMonomialCount (118+j) 236)+
          (∑ j ∈ Finset.range 118,j*(j+1))=
        ∑ j ∈ Finset.range 118,(119*120+238*j) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      weightedMonomialCount_upper_twice 59 j
        (by have := Finset.mem_range.mp hj; omega)
  have hsplit :
      (∑ d ∈ Finset.range 236,weightedMonomialCount d 236)=
        (∑ d ∈ Finset.range 118,weightedMonomialCount d 236)+
          ∑ j ∈ Finset.range 118,weightedMonomialCount (118+j) 236 := by
    conv_lhs => rw [show 236=118+118 by norm_num,Finset.sum_range_add]
  have hlow_rhs :
      (∑ d ∈ Finset.range 118,(d+1)*(d+2))=561680 := by
    have h := shifted_pair_sum_three 118
    rw [show 118*(118+1)*(118+2)=1685040 by norm_num] at h
    exact solve_low_rhs _ h
  have hj_rhs :
      (∑ j ∈ Finset.range 118,j*(j+1))=547638 := by
    have h := adjacent_pair_sum_three 117
    rw [show 117*(117+1)*(117+2)=1642914 by norm_num] at h
    exact solve_adjacent_rhs _ h
  have hupp_rhs :
      (∑ j ∈ Finset.range 118,(119*120+238*j))=3327954 := by
    have h := affine_sum_two 117 14280 238
    rw [show 2*(117+1)*14280+238*117*(117+1)=6655908 by norm_num] at h
    exact solve_affine_rhs _ h
  rw [hlow_rhs] at hlow
  have hlow_value :
      (∑ d ∈ Finset.range 118,weightedMonomialCount d 236)=280840 :=
    solve_low_count _ hlow
  rw [hj_rhs,hupp_rhs] at hupp
  have hupp_value :
      (∑ j ∈ Finset.range 118,weightedMonomialCount (118+j) 236)=1390158 :=
    solve_upper_count _ hupp
  rw [hsplit,hlow_value,hupp_value]

end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowShiftW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryLowShiftW1332216900.weightedMonomialCount_sum_59
