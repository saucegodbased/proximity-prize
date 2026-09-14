import WeightedFinitePrefixHelperRankW1332196900

/-! Exact symbolic source-column pair sum for W=133221. -/
namespace ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryPairSumW1332216900

open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

def genericPairPolynomialSum (B W D : Nat) : Nat :=
  ∑ t ∈ Finset.range (D/2+1),∑ r ∈ Finset.range (D-2*t+1),
    ((WeightedSourceIndex6900.pairWidth B W r t)^2+
      W*WeightedSourceIndex6900.pairWidth B W r t)

abbrev primaryPairWidth (t r : Nat) : Nat :=
  WeightedSourceIndex6900.pairWidth 96160129 133221 r t

abbrev primaryPairPolynomialSum : Nat :=
  genericPairPolynomialSum 96160129 133221 236

theorem primary_pair_cost_le (t r : Nat) (ht : t≤118) (hr : r≤236-2*t) :
    133220*r+133219*t≤96160129 := by omega

theorem primaryPairWidth_cast (t r : Nat) (ht : t≤118) (hr : r≤236-2*t) :
    (primaryPairWidth t r:ℚ)=96160129-133220*r-133219*t := by
  unfold primaryPairWidth WeightedSourceIndex6900.pairWidth
  rw [Nat.cast_sub (primary_pair_cost_le t r ht hr)]
  push_cast
  ring

theorem rational_primary_pair_inner (t : Nat) (ht : t≤118) :
    3*(∑ r ∈ Finset.range (236-2*t+1),
      (((96160129:ℚ)-133220*r-133219*t)^2+
        133221*((96160129:ℚ)-133220*r-133219*t)))=
      4667293775392622610-40383194050782211*t+
        12617555051757*(t:ℚ)^2-35495136806*(t:ℚ)^3 := by
  have hsafe : 2*t≤236 := by omega
  calc
    _=3*(∑ r ∈ Finset.range (236-2*t+1),
      (((96160129-133219*(t:ℚ))^2+133221*(96160129-133219*t))+
        (-266440*(96160129-133219*t)-17747701620)*(r:ℚ)+
          17747568400*(r:ℚ)^2)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _=_ := by
      rw [WeightedQuadricHighRankSum6900.rat_quadratic_sum,Nat.cast_sub hsafe]
      push_cast
      ring

theorem primaryPairPolynomialSum_eq :
    primaryPairPolynomialSum=92375427127187459192 := by
  have hcast : (primaryPairPolynomialSum:ℚ)=
      ∑ t ∈ Finset.range 119,∑ r ∈ Finset.range (236-2*t+1),
        (((96160129:ℚ)-133220*r-133219*t)^2+
          133221*((96160129:ℚ)-133220*r-133219*t)) := by
    unfold primaryPairPolynomialSum genericPairPolynomialSum
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro r hr
    rw [primaryPairWidth_cast t r
      (by have := Finset.mem_range.mp ht; omega)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
  have hrat := congrArg (fun z : ℚ=>3*z) hcast
  have hsum :
      3*(∑ t ∈ Finset.range 119,∑ r ∈ Finset.range (236-2*t+1),
        (((96160129:ℚ)-133220*r-133219*t)^2+
          133221*((96160129:ℚ)-133220*r-133219*t)))=
        (3*92375427127187459192:ℚ) := by
    calc
      _=∑ t ∈ Finset.range 119,
        (4667293775392622610-40383194050782211*t+
          12617555051757*(t:ℚ)^2-35495136806*(t:ℚ)^3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        exact rational_primary_pair_inner t
          (by have := Finset.mem_range.mp ht; omega)
      _=∑ t ∈ Finset.range (118+1),
          (4667293775392622610+(-40383194050782211)*(t:ℚ)+
            12617555051757*(t:ℚ)^2+(-35495136806)*(t:ℚ)^3) := by
        norm_num only [Nat.reduceAdd]
      _=_ := by
        rw [WeightedQuadricSourcePairSum6900.rat_cubic_sum]
        norm_num
  rw [hsum] at hrat
  exact_mod_cast (mul_left_cancel₀ (by norm_num : (3:ℚ)≠0) hrat)

end ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryPairSumW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryPairSumW1332216900.rational_primary_pair_inner
#print axioms ProximityPrize.SubmissionLower.WeightedFinitePrefixPrimaryPairSumW1332216900.primaryPairPolynomialSum_eq
