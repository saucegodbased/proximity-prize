import WeightedPrimary547TargetW1332256900
import WeightedFinitePrefixPrimaryColumnsW1332246900

/-! Symbolic source-column receipt for the hard W=133225 primary source
`(m,B,D)=(547,98685911,244)`. -/
namespace ProximityPrize.SubmissionLower.WeightedPrimary547ColumnsW1332256900

open scoped BigOperators
open WeightedSourceIndex6900
open WeightedFinitePrefixPrimaryPairSumW1332246900
open WeightedFinitePrefixPrimaryColumnsW1332246900
open WeightedFinitePrefixHelperRankW1332196900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000

def primaryPairPolynomialSum : Nat :=
  genericPairPolynomialSum 98685911 133225 244

theorem primary_pair_cost_le (t r : Nat) (ht : t ≤122)
    (hr : r ≤244-2*t) :
    133224*r+133223*t ≤98685911 := by omega

theorem primaryPairWidth_cast (t r : Nat) (ht : t ≤122)
    (hr : r ≤244-2*t) :
    (WeightedSourceIndex6900.pairWidth 98685911 133225 r t : ℚ) =
      98685911-133224*r-133223*t := by
  unfold WeightedSourceIndex6900.pairWidth
  rw [Nat.cast_sub (primary_pair_cost_le t r ht hr)]
  push_cast
  ring

theorem rational_primary_pair_inner (t : Nat) (ht : t ≤122) :
    3*(∑ r ∈ Finset.range (244-2*t+1),
      (((98685911:ℚ)-133224*r-133223*t)^2+
        133225*((98685911:ℚ)-133224*r-133223*t))) =
      5067745244466755760+(-42434589427019511)*(t:ℚ)+
        13044256129749*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3 := by
  have hsafe : 2*t ≤ 244 := by omega
  calc
    _ = 3*(∑ r ∈ Finset.range (244-2*t+1),
      (((98685911-133223*(t:ℚ))^2+133225*(98685911-133223*t))+
        (-266448*(98685911-133223*t)-17748767400)*(r:ℚ)+
          17748634176*(r:ℚ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum, Nat.cast_sub hsafe]
      push_cast
      ring

theorem primaryPairPolynomialSum_eq :
    primaryPairPolynomialSum = 103646808093005864410 := by
  have hcast : (primaryPairPolynomialSum:ℚ) =
      ∑ t ∈ Finset.range 123, ∑ r ∈ Finset.range (244-2*t+1),
        (((98685911:ℚ)-133224*r-133223*t)^2+
          133225*((98685911:ℚ)-133224*r-133223*t)) := by
    unfold primaryPairPolynomialSum genericPairPolynomialSum
    rw [show 244/2+1=123 by norm_num]
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro r hr
    rw [primaryPairWidth_cast t r
      (by have := Finset.mem_range.mp ht; omega)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
  have h3 := congrArg (fun z : ℚ => 3*z) hcast
  have hsum :
      3*(∑ t ∈ Finset.range 123, ∑ r ∈ Finset.range (244-2*t+1),
        (((98685911:ℚ)-133224*r-133223*t)^2+
          133225*((98685911:ℚ)-133224*r-133223*t))) =
        (3*103646808093005864410:ℚ) := by
    calc
      _ = ∑ t ∈ Finset.range 123,
        (5067745244466755760+(-42434589427019511)*(t:ℚ)+
          13044256129749*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        exact rational_primary_pair_inner t
          (by have := Finset.mem_range.mp ht; omega)
      _ = _ := by
        rw [show 123=122+1 by norm_num,
          WeightedQuadricSourcePairSum6900.rat_cubic_sum]
        norm_num
  rw [hsum] at h3
  have hq : (primaryPairPolynomialSum:ℚ)=103646808093005864410 := by
    linarith
  generalize hS : primaryPairPolynomialSum = S at hq ⊢
  exact_mod_cast hq

theorem primary_columns_lower :
    388991586012407 ≤ columns 98685911 133225 244 := by
  have hbase : primaryPairPolynomialSum ≤
      (2*133225)*columns 98685911 133225 244 := by
    exact pairPolynomialSum_le_columns 98685911 133225 244 (by norm_num)
  rw [primaryPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266450*388991586012407 ≤103646808093005864410 := by norm_num
  have hc : 266450*388991586012407 ≤
      266450*columns 98685911 133225 244 := hn.trans hbase
  exact cancel_nat_mul_le 266450 388991586012407
    (columns 98685911 133225 244) (by norm_num) hc

end ProximityPrize.SubmissionLower.WeightedPrimary547ColumnsW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedPrimary547ColumnsW1332256900.primary_columns_lower
