import WeightedIdentityCoreTargetW1332256900
import WeightedFinitePrefixPrimaryColumnsW1332246900

/-!
# Source-column receipt for the W=133225 identity-core helper

The exact quadratic pair numerator is evaluated symbolically.  Its quotient
by `2*133225` gives the conservative column lower bound used by the kernel
interface; no large finite computation is evaluated by the kernel.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityCoreColumnsW1332256900

open scoped BigOperators
open WeightedSourceIndex6900
open WeightedFinitePrefixHelperRankW1332196900
open WeightedFinitePrefixPrimaryPairSumW1332246900
open WeightedFinitePrefixPrimaryColumnsW1332246900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2400

def helperPairWidth (t r : Nat) : Nat :=
  99227150-(133224*r+133223*t)

def helperPairPolynomialSum : Nat :=
  genericPairPolynomialSum 99227150 133225 244

theorem helper_pair_cost_le (t r : Nat) (ht : t≤122) (hr : r≤244-2*t) :
    133224*r+133223*t≤99227150 := by
  omega

theorem helperPairWidth_cast (t r : Nat) (ht : t≤122) (hr : r≤244-2*t) :
    (helperPairWidth t r:ℚ)=99227150-133224*r-133223*t := by
  unfold helperPairWidth
  rw [Nat.cast_sub (helper_pair_cost_le t r ht hr)]
  push_cast
  ring

theorem rational_helper_pair_inner (t : Nat) (ht : t≤122) :
    3*(∑ r ∈ Finset.range (244-2*t+1),
      (((99227150:ℚ)-133224*r-133223*t)^2+
        133225*((99227150:ℚ)-133224*r-133223*t)))=
      5133598674760909710-42972167654207601*t+
        13044249634881*(t:ℚ)^2-35497268358*(t:ℚ)^3 := by
  have hsafe : 2*t≤244 := by omega
  calc
    _=3*(∑ r ∈ Finset.range (244-2*t+1),
      (((99227150-133223*(t:ℚ))^2+133225*(99227150-133223*t))+
        (-266448*(99227150-133223*t)-17748767400)*(r:ℚ)+
          17748634176*(r:ℚ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _=_ := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum,Nat.cast_sub hsafe]
      push_cast
      ring

theorem helperPairPolynomialSum_eq :
    helperPairPolynomialSum=105002314262302799050 := by
  have hcast : (helperPairPolynomialSum:ℚ)=
      ∑ t ∈ Finset.range 123,∑ r ∈ Finset.range (244-2*t+1),
        (((99227150:ℚ)-133224*r-133223*t)^2+
          133225*((99227150:ℚ)-133224*r-133223*t)) := by
    unfold helperPairPolynomialSum genericPairPolynomialSum
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro r hr
    rw [show WeightedSourceIndex6900.pairWidth 99227150 133225 r t =
        helperPairWidth t r by rfl]
    rw [helperPairWidth_cast t r
      (by have := Finset.mem_range.mp ht; omega)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
  have hrat := congrArg (fun z : ℚ=>3*z) hcast
  have hsum :
      3*(∑ t ∈ Finset.range 123,∑ r ∈ Finset.range (244-2*t+1),
        (((99227150:ℚ)-133224*r-133223*t)^2+
          133225*((99227150:ℚ)-133224*r-133223*t)))=
        (3*105002314262302799050:ℚ) := by
    calc
      _=∑ t ∈ Finset.range 123,
        (5133598674760909710+(-42972167654207601)*(t:ℚ)+
          13044249634881*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        convert rational_helper_pair_inner t
          (by have := Finset.mem_range.mp ht; omega) using 1 <;> ring
      _=_ := by
        rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
        norm_num
  rw [hsum] at hrat
  exact_mod_cast (mul_left_cancel₀ (by norm_num : (3:ℚ)≠0) hrat)

/-- Conservative integer column receipt.  The exact columns are larger by
`155096052`, but this weaker receipt already closes both helper bands. -/
theorem helper_columns_lower :
    394078867563530≤columns 99227150 133225 244 := by
  have hbase : helperPairPolynomialSum≤
      (2*133225)*columns 99227150 133225 244 := by
    exact pairPolynomialSum_le_columns 99227150 133225 244 (by norm_num)
  rw [helperPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266450*394078867563530≤105002314262302799050 := by norm_num
  have hc : 266450*394078867563530≤
      266450*columns 99227150 133225 244 := hn.trans hbase
  exact cancel_nat_mul_le 266450 394078867563530
    (columns 99227150 133225 244) (by norm_num) hc

#print axioms rational_helper_pair_inner
#print axioms helperPairPolynomialSum_eq
#print axioms helper_columns_lower

end ProximityPrize.SubmissionLower.WeightedIdentityCoreColumnsW1332256900
