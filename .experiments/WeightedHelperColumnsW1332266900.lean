import WeightedFinitePrefixPrimaryColumnsW1332246900

/-! Exact symbolic helper-column receipt for W=133226. -/
namespace ProximityPrize.SubmissionLower.WeightedHelperColumnsW1332266900

open scoped BigOperators
open WeightedSourceIndex6900
open WeightedFinitePrefixPrimaryPairSumW1332246900
open WeightedFinitePrefixPrimaryColumnsW1332246900
open WeightedFinitePrefixHelperRankW1332196900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000

def helperPairPolynomialSum : Nat :=
  genericPairPolynomialSum 2130677530 133226 5248

theorem helper_pair_cost_le (t r : Nat) (ht : t≤2624)
    (hr : r≤5248-2*t) :
    133225*r+133224*t≤2130677530 := by omega

theorem helperPairWidth_cast (t r : Nat) (ht : t≤2624)
    (hr : r≤5248-2*t) :
    (WeightedSourceIndex6900.pairWidth 2130677530 133226 r t:ℚ)=
      2130677530-133225*r-133224*t := by
  unfold WeightedSourceIndex6900.pairWidth
  rw [Nat.cast_sub (helper_pair_cost_le t r ht hr)]
  push_cast
  ring

theorem rational_helper_pair_inner (t : Nat) (ht : t≤2624) :
    3*(∑ r ∈ Finset.range (5248-2*t+1),
      (((2130677530:ℚ)-133225*r-133224*t)^2+
        133226*((2130677530:ℚ)-133225*r-133224*t)))=
      50599655995582600391160+
        (-19768693388608004263)*(t:ℚ)+
        279470564216706*(t:ℚ)^2+(-35497801256)*(t:ℚ)^3 := by
  have hsafe : 2*t≤5248 := by omega
  calc
    _=3*(∑ r ∈ Finset.range (5248-2*t+1),
      (((2130677530-133224*(t:ℚ))^2+
          133226*(2130677530-133224*t))+
        (-266450*(2130677530-133224*t)-17749033850)*(r:ℚ)+
          17748900625*(r:ℚ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _=_ := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum,Nat.cast_sub hsafe]
      push_cast
      ring

theorem helperPairPolynomialSum_eq :
    helperPairPolynomialSum=22001240322655446270845000 := by
  have hcast : (helperPairPolynomialSum:ℚ)=
      ∑ t ∈ Finset.range 2625,∑ r ∈ Finset.range (5248-2*t+1),
        (((2130677530:ℚ)-133225*r-133224*t)^2+
          133226*((2130677530:ℚ)-133225*r-133224*t)) := by
    unfold helperPairPolynomialSum genericPairPolynomialSum
    rw [show 5248/2+1=2625 by norm_num]
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro r hr
    rw [helperPairWidth_cast t r
      (by have := Finset.mem_range.mp ht; omega)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
  have h3 := congrArg (fun z : ℚ=>3*z) hcast
  have hsum :
      3*(∑ t ∈ Finset.range 2625,∑ r ∈ Finset.range (5248-2*t+1),
        (((2130677530:ℚ)-133225*r-133224*t)^2+
          133226*((2130677530:ℚ)-133225*r-133224*t)))=
        (3*22001240322655446270845000:ℚ) := by
    calc
      _=∑ t ∈ Finset.range 2625,
        (50599655995582600391160+
          (-19768693388608004263)*(t:ℚ)+
          279470564216706*(t:ℚ)^2+(-35497801256)*(t:ℚ)^3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        exact rational_helper_pair_inner t
          (by have := Finset.mem_range.mp ht; omega)
      _=_ := by
        rw [show 2625=2624+1 by norm_num,
          WeightedQuadricSourcePairSum6900.rat_cubic_sum]
        norm_num
  rw [hsum] at h3
  have hq : (helperPairPolynomialSum:ℚ)=
      22001240322655446270845000 := by linarith
  generalize hS : helperPairPolynomialSum = S at hq ⊢
  exact_mod_cast hq

theorem helper_columns_lower :
    82571120962332601259≤columns 2130677530 133226 5248 := by
  have hbase : helperPairPolynomialSum≤
      (2*133226)*columns 2130677530 133226 5248 := by
    exact pairPolynomialSum_le_columns 2130677530 133226 5248 (by norm_num)
  rw [helperPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266452*82571120962332601259≤
      22001240322655446270845000 := by norm_num
  have hc : 266452*82571120962332601259≤
      266452*columns 2130677530 133226 5248 := hn.trans hbase
  exact cancel_nat_mul_le 266452 82571120962332601259
    (columns 2130677530 133226 5248) (by norm_num) hc

#print axioms helperPairPolynomialSum_eq
#print axioms helper_columns_lower

end ProximityPrize.SubmissionLower.WeightedHelperColumnsW1332266900
