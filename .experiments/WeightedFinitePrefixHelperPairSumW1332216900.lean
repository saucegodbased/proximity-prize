import WeightedFinitePrefixPrimaryPairSumW1332216900

/-! Exact symbolic source-column pair sum for the W=133221 helper. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperPairSumW1332216900

open scoped BigOperators
open WeightedFinitePrefixPrimaryPairSumW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500

def helperPairWidth (k t r : Nat) : Nat :=
  9*k*180413-(133220*r+133219*t)

def helperPairPolynomialSum (k : Nat) : Nat :=
  genericPairPolynomialSum (9*k*180413) 133221 (4*k)

def helperSourceNumeratorThree (k : Nat) : Nat :=
  k*(2*k+1)*(11124206260194*k^2+6717998017329*k+577948667673)

theorem helper_pair_cost_le (k t r : Nat) (ht : t≤2*k)
    (hr : r≤4*k-2*t) :
    133220*r+133219*t≤9*k*180413 := by omega

theorem helperPairWidth_cast (k t r : Nat) (ht : t≤2*k)
    (hr : r≤4*k-2*t) :
    (helperPairWidth k t r:ℚ)=9*(k:ℚ)*180413-133220*r-133219*t := by
  unfold helperPairWidth
  rw [Nat.cast_sub (helper_pair_cost_le k t r ht hr)]
  push_cast
  ring

theorem rational_helper_pair_inner (k t : Nat) (ht : t≤2*k) :
    3*(∑ r ∈ Finset.range (4*k-2*t+1),
      ((9*(k:ℚ)*180413-133220*r-133219*t)^2+
        133221*(9*k*180413-133220*r-133219*t))) =
      22390371351148*k^3+7909386975591*k^2+577948534451*k+
        (-11479114195326*k^2-1297867873788*k-17747168737)*t+
        (212954533488*k+53241905877)*(t:ℚ)^2-
        35495136806*(t:ℚ)^3 := by
  have hsafe : 2*t≤4*k := by omega
  calc
    _ = 3*(∑ r ∈ Finset.range (4*k-2*t+1),
      (((9*(k:ℚ)*180413-133219*t)^2+
          133221*(9*k*180413-133219*t))+
        (-266440*(9*k*180413-133219*t)-17747701620)*(r:ℚ)+
          17747568400*(r:ℚ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum,Nat.cast_sub hsafe]
      push_cast
      ring

theorem rational_helper_pair_sum (k : Nat) :
    3*(∑ t ∈ Finset.range (2*k+1), ∑ r ∈ Finset.range (4*k-2*t+1),
      ((9*(k:ℚ)*180413-133220*r-133219*t)^2+
        133221*(9*k*180413-133220*r-133219*t))) =
      (k:ℚ)*(2*k+1)*
        (11124206260194*k^2+6717998017329*k+577948667673) := by
  calc
    _ = ∑ t ∈ Finset.range (2*k+1),
      (22390371351148*(k:ℚ)^3+7909386975591*k^2+577948534451*k+
        (-11479114195326*k^2-1297867873788*k-17747168737)*t+
        (212954533488*k+53241905877)*(t:ℚ)^2+
        (-35495136806)*(t:ℚ)^3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have h := rational_helper_pair_inner k t
        (Nat.le_of_lt_succ (Finset.mem_range.mp ht))
      convert h using 1 <;> ring
    _ = _ := by
      rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
      push_cast
      ring

theorem helperPairPolynomialSum_three (k : Nat) :
    3*helperPairPolynomialSum k=helperSourceNumeratorThree k := by
  have hcast : (helperPairPolynomialSum k:ℚ)=
      ∑ t ∈ Finset.range (2*k+1), ∑ r ∈ Finset.range (4*k-2*t+1),
        ((9*(k:ℚ)*180413-133220*r-133219*t)^2+
          133221*(9*k*180413-133220*r-133219*t)) := by
    unfold helperPairPolynomialSum genericPairPolynomialSum
    rw [show 4*k/2=2*k by omega]
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro r hr
    rw [show WeightedSourceIndex6900.pairWidth (9*k*180413) 133221 r t =
        helperPairWidth k t r by rfl]
    rw [helperPairWidth_cast k t r
      (Nat.le_of_lt_succ (Finset.mem_range.mp ht))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
  have hrat := congrArg (fun z : ℚ => 3*z) hcast
  rw [rational_helper_pair_sum] at hrat
  unfold helperSourceNumeratorThree
  exact_mod_cast hrat

theorem helperPairPolynomialSum_eq :
    helperPairPolynomialSum 1252=18238030713311927937794940 := by
  have h := helperPairPolynomialSum_three 1252
  norm_num [helperSourceNumeratorThree] at h ⊢
  omega

end ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperPairSumW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperPairSumW1332216900.helperPairPolynomialSum_three
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixHelperPairSumW1332216900.helperPairPolynomialSum_eq
