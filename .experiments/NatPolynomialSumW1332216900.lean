import WeightedFinitePrefixHelperRankW1332196900

namespace ProximityPrize.SubmissionLower.NatPolynomialSumW1332216900

open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000

theorem shifted_pair_sum_three (n : Nat) :
    3*(∑ i ∈ Finset.range n,(i+1)*(i+2))=n*(n+1)*(n+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    ring

theorem adjacent_pair_sum_three (n : Nat) :
    3*(∑ i ∈ Finset.range (n+1),i*(i+1))=n*(n+1)*(n+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    ring

theorem affine_sum_two (n A B : Nat) :
    2*(∑ i ∈ Finset.range (n+1),(A+B*i))=
      2*(n+1)*A+B*n*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    ring

end ProximityPrize.SubmissionLower.NatPolynomialSumW1332216900

#print axioms ProximityPrize.SubmissionLower.NatPolynomialSumW1332216900.shifted_pair_sum_three
#print axioms ProximityPrize.SubmissionLower.NatPolynomialSumW1332216900.adjacent_pair_sum_three
#print axioms ProximityPrize.SubmissionLower.NatPolynomialSumW1332216900.affine_sum_two
