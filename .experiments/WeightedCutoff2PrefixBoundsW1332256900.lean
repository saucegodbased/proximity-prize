import WeightedCutoff2ContinuousArithmeticW1332256900

/-! Low-memory prefix bounds assembled from the continuous and terminal receipts. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2PrefixBoundsW1332256900

open scoped BigOperators
open WeightedCutoff2ContinuousArithmeticW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

theorem j_scaled_le (j : Nat) :
    133225*jRelaxedCount j≤continuousNumerator (jC j) 133225 (jE j) :=
  triangleRelaxedCount_scaled_le (jC j) 133225 (jE j)

theorem d_scaled_le (j : Nat) :
    133225*dRelaxedCount j≤continuousNumerator (dC j) 133225 (dE j) :=
  triangleRelaxedCount_scaled_le (dC j) 133225 (dE j)

theorem mul_sum_le_sum {I : Type*} [DecidableEq I] (s : Finset I)
    (c : Nat) (f g : I→Nat) (h : ∀ i∈s,c*f i≤g i) :
    c*(∑ i∈s,f i)≤∑ i∈s,g i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum h

theorem sum_mul_eq_mul_sum {I : Type*} [DecidableEq I] (s : Finset I)
    (c : Nat) (f : I→Nat) : (∑ i∈s,c*f i)=c*(∑ i∈s,f i) :=
  (Finset.mul_sum s f c).symm

theorem j_first_scaled_le :
    133225*(∑ j ∈ Finset.range 51,jRelaxedCount j)≤
      ∑ j ∈ Finset.range 51,
        continuousNumerator (jC j) 133225 (jE j) :=
  mul_sum_le_sum (Finset.range 51) 133225 jRelaxedCount
    (fun j => continuousNumerator (jC j) 133225 (jE j))
    (fun j hj => j_scaled_le j)

theorem j_first_scaled_value :
    133225*(∑ j ∈ Finset.range 51,jRelaxedCount j)≤
      363070291485498774 :=
  j_first_scaled_le.trans_eq jContinuous_total


theorem j_prefix_split :
    (∑ j ∈ Finset.range (51+24),jRelaxedCount j)=
      (∑ j ∈ Finset.range 51,jRelaxedCount j)+
        ∑ i ∈ Finset.range 24,jRelaxedCount (51+i) := by
  exact Finset.sum_range_add jRelaxedCount 51 24


theorem j_terminal_value :
    (∑ i ∈ Finset.range 24,jRelaxedCount (51+i))=113412219235 := by
  simpa only [jRelaxedCount] using jRelaxed_terminal

theorem j_prefix_scaled_le :
    133225*(∑ j ∈ Finset.range (51+24),jRelaxedCount j)≤
      378179634393081649 := by
  calc
    _ = 133225*((∑ j ∈ Finset.range 51,jRelaxedCount j)+
          ∑ i ∈ Finset.range 24,jRelaxedCount (51+i)) :=
      congrArg (fun x : Nat => 133225*x) j_prefix_split
    _ = 133225*(∑ j ∈ Finset.range 51,jRelaxedCount j)+
          133225*(∑ i ∈ Finset.range 24,jRelaxedCount (51+i)) :=
      Nat.mul_add 133225 _ _
    _ = 133225*(∑ j ∈ Finset.range 51,jRelaxedCount j)+
          133225*113412219235 :=
      congrArg (fun x : Nat =>
        133225*(∑ j ∈ Finset.range 51,jRelaxedCount j)+133225*x)
        j_terminal_value
    _ ≤ 363070291485498774+133225*113412219235 :=
      Nat.add_le_add_right j_first_scaled_value _
    _ = _ := by norm_num


theorem j_relaxed_prefix_le :
    (∑ j ∈ Finset.range (51+24),jRelaxedCount j)≤2838653664050 := by
  by_contra hn
  have hlt : 2838653664050<
      ∑ j ∈ Finset.range (51+24),jRelaxedCount j := Nat.lt_of_not_ge hn
  have hmul : 133225*2838653664051≤
      133225*(∑ j ∈ Finset.range (51+24),jRelaxedCount j) :=
    Nat.mul_le_mul_left 133225 (Nat.succ_le_iff.mpr hlt)
  have hconst : 378179634393081649<133225*2838653664051 := by norm_num
  exact (Nat.not_lt_of_ge (hmul.trans j_prefix_scaled_le)) hconst


theorem d_relaxed_prefix_le :
    (∑ j ∈ Finset.range 93,dRelaxedCount j)≤2831401397270 := by
  have hscaled :
      133225*(∑ j ∈ Finset.range 93,dRelaxedCount j)≤
        377213451151410342 :=
    (mul_sum_le_sum (Finset.range 93) 133225 dRelaxedCount
      (fun j => continuousNumerator (dC j) 133225 (dE j))
      (fun j hj => d_scaled_le j)).trans_eq dContinuous_total
  by_contra hn
  have hlt : 2831401397270<
      ∑ j ∈ Finset.range 93,dRelaxedCount j := Nat.lt_of_not_ge hn
  have hmul : 133225*2831401397271≤
      133225*(∑ j ∈ Finset.range 93,dRelaxedCount j) :=
    Nat.mul_le_mul_left 133225 (Nat.succ_le_iff.mpr hlt)
  have hconst : 377213451151410342<133225*2831401397271 := by norm_num
  exact (Nat.not_lt_of_ge (hmul.trans hscaled)) hconst

end ProximityPrize.SubmissionLower.WeightedCutoff2PrefixBoundsW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2PrefixBoundsW1332256900.j_relaxed_prefix_le
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2PrefixBoundsW1332256900.d_relaxed_prefix_le
