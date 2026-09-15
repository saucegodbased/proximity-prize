import WeightedFinitePrefixPrimaryColumnsW1332246900

/-! Symbolic pair-sum column receipts for the cutoff-two W=133225 sources. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2ColumnsW1332256900

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
  genericPairPolynomialSum 98505498 133225 244

def helperPairPolynomialSum : Nat :=
  genericPairPolynomialSum 2130677530 133225 5248

theorem primary_pair_cost_le (t r : Nat) (ht : t≤122)
    (hr : r≤244-2*t) :
    133224*r+133223*t≤98505498 := by omega

theorem primaryPairWidth_cast (t r : Nat) (ht : t≤122)
    (hr : r≤244-2*t) :
    (WeightedSourceIndex6900.pairWidth 98505498 133225 r t:ℚ)=
      98505498-133224*r-133223*t := by
  unfold WeightedSourceIndex6900.pairWidth
  rw [Nat.cast_sub (primary_pair_cost_le t r ht hr)]
  push_cast
  ring

theorem rational_primary_pair_inner (t : Nat) (ht : t≤122) :
    3*(∑ r ∈ Finset.range (244-2*t+1),
      (((98505498:ℚ)-133224*r-133223*t)^2+
        133225*((98505498:ℚ)-133224*r-133223*t)))=
      5045889794656043970+(-42256177857037137)*(t:ℚ)+
        13044258294705*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3 := by
  have hsafe : 2*t≤244 := by omega
  calc
    _=3*(∑ r ∈ Finset.range (244-2*t+1),
      (((98505498-133223*(t:ℚ))^2+133225*(98505498-133223*t))+
        (-266448*(98505498-133223*t)-17748767400)*(r:ℚ)+
          17748634176*(r:ℚ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _=_ := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum,Nat.cast_sub hsafe]
      push_cast
      ring

theorem primaryPairPolynomialSum_eq :
    primaryPairPolynomialSum=103196942429481253134 := by
  have hcast : (primaryPairPolynomialSum:ℚ)=
      ∑ t ∈ Finset.range 123,∑ r ∈ Finset.range (244-2*t+1),
        (((98505498:ℚ)-133224*r-133223*t)^2+
          133225*((98505498:ℚ)-133224*r-133223*t)) := by
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
  have h3 := congrArg (fun z : ℚ=>3*z) hcast
  have hsum :
      3*(∑ t ∈ Finset.range 123,∑ r ∈ Finset.range (244-2*t+1),
        (((98505498:ℚ)-133224*r-133223*t)^2+
          133225*((98505498:ℚ)-133224*r-133223*t)))=
        (3*103196942429481253134:ℚ) := by
    calc
      _=∑ t ∈ Finset.range 123,
        (5045889794656043970+(-42256177857037137)*(t:ℚ)+
          13044258294705*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        exact rational_primary_pair_inner t
          (by have := Finset.mem_range.mp ht; omega)
      _=_ := by
        rw [show 123=122+1 by norm_num,
          WeightedQuadricSourcePairSum6900.rat_cubic_sum]
        norm_num
  rw [hsum] at h3
  have hq : (primaryPairPolynomialSum:ℚ)=103196942429481253134 := by
    linarith
  generalize hS : primaryPairPolynomialSum = S at hq ⊢
  exact_mod_cast hq

theorem helper_pair_cost_le (t r : Nat) (ht : t≤2624)
    (hr : r≤5248-2*t) :
    133224*r+133223*t≤2130677530 := by omega

theorem helperPairWidth_cast (t r : Nat) (ht : t≤2624)
    (hr : r≤5248-2*t) :
    (WeightedSourceIndex6900.pairWidth 2130677530 133225 r t:ℚ)=
      2130677530-133224*r-133223*t := by
  unfold WeightedSourceIndex6900.pairWidth
  rw [Nat.cast_sub (helper_pair_cost_le t r ht hr)]
  push_cast
  ring

theorem rational_helper_pair_inner (t : Nat) (ht : t≤2624) :
    3*(∑ r ∈ Finset.range (5248-2*t+1),
      (((2130677530:ℚ)-133224*r-133223*t)^2+
        133225*((2130677530:ℚ)-133224*r-133223*t)))=
      50599793529813059713002+(-19768738451296530621)*(t:ℚ)+
        279466368412821*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3 := by
  have hsafe : 2*t≤5248 := by omega
  calc
    _=3*(∑ r ∈ Finset.range (5248-2*t+1),
      (((2130677530-133223*(t:ℚ))^2+
          133225*(2130677530-133223*t))+
        (-266448*(2130677530-133223*t)-17748767400)*(r:ℚ)+
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
    helperPairPolynomialSum=22001302612301476616132750 := by
  have hcast : (helperPairPolynomialSum:ℚ)=
      ∑ t ∈ Finset.range 2625,∑ r ∈ Finset.range (5248-2*t+1),
        (((2130677530:ℚ)-133224*r-133223*t)^2+
          133225*((2130677530:ℚ)-133224*r-133223*t)) := by
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
        (((2130677530:ℚ)-133224*r-133223*t)^2+
          133225*((2130677530:ℚ)-133224*r-133223*t)))=
        (3*22001302612301476616132750:ℚ) := by
    calc
      _=∑ t ∈ Finset.range 2625,
        (50599793529813059713002+(-19768738451296530621)*(t:ℚ)+
          279466368412821*(t:ℚ)^2+(-35497268358)*(t:ℚ)^3) := by
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
  have hq : (helperPairPolynomialSum:ℚ)=22001302612301476616132750 := by
    linarith
  generalize hS : helperPairPolynomialSum = S at hq ⊢
  exact_mod_cast hq

theorem primary_columns_lower :
    387303217975159≤columns 98505498 133225 244 := by
  have hbase : primaryPairPolynomialSum≤
      (2*133225)*columns 98505498 133225 244 := by
    exact pairPolynomialSum_le_columns 98505498 133225 244 (by norm_num)
  rw [primaryPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266450*387303217975159≤103196942429481253134 := by norm_num
  have hc : 266450*387303217975159≤
      266450*columns 98505498 133225 244 := hn.trans hbase
  exact cancel_nat_mul_le 266450 387303217975159
    (columns 98505498 133225 244) (by norm_num) hc

theorem helper_columns_lower :
    82571974525432451177≤columns 2130677530 133225 5248 := by
  have hbase : helperPairPolynomialSum≤
      (2*133225)*columns 2130677530 133225 5248 := by
    exact pairPolynomialSum_le_columns 2130677530 133225 5248 (by norm_num)
  rw [helperPairPolynomialSum_eq] at hbase
  norm_num only [Nat.reduceMul] at hbase
  have hn : 266450*82571974525432451177≤22001302612301476616132750 := by norm_num
  have hc : 266450*82571974525432451177≤
      266450*columns 2130677530 133225 5248 := hn.trans hbase
  exact cancel_nat_mul_le 266450 82571974525432451177
    (columns 2130677530 133225 5248) (by norm_num) hc

end ProximityPrize.SubmissionLower.WeightedCutoff2ColumnsW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ColumnsW1332256900.primary_columns_lower
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2ColumnsW1332256900.helper_columns_lower
