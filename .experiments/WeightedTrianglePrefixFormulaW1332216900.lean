import WeightedRelaxedFibreCoreW1332216900
import WeightedQuadricHighRankSum6900

/-! Closed rational formulas for the triangular multiplicity prefixes. -/
namespace ProximityPrize.SubmissionLower.WeightedTrianglePrefixFormulaW1332216900

open scoped BigOperators
open WeightedQuadricHighRankSum6900
open WeightedRelaxedFibreCoreW1332216900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

def lowerCardQ (h : Nat) : ℚ := (h+1)*(h+2)/2
def lowerWeightQ (h : Nat) : ℚ := h*(h+1)*(h+2)/3

def upperCardQ (E h : Nat) : ℚ :=
  let a:=E/2
  let d:=h-a-1
  let c:=E+1-(a+1)
  lowerCardQ a+(d+1)*(c:ℚ)-d*(d+1)/2

def upperWeightQ (E h : Nat) : ℚ :=
  let a:=E/2
  let d:=h-a-1
  let c:=E+1-(a+1)
  lowerWeightQ a+(d+1)*(c:ℚ)*(a+1)+
    ((c:ℚ)-(a+1))*(d*(d+1)/2)-d*(d+1)*(2*d+1)/6

def triangleCardPrefix (E h : Nat) : Nat :=
  ∑ n ∈ Finset.range (min E h+1),triangleMultiplicity E n

def triangleWeightPrefix (E h : Nat) : Nat :=
  ∑ n ∈ Finset.range (min E h+1),triangleMultiplicity E n*n

def triangleCardQ (E h : Nat) : ℚ :=
  let u:=min E h
  if u≤E/2 then lowerCardQ u else upperCardQ E u

def triangleWeightQ (E h : Nat) : ℚ :=
  let u:=min E h
  if u≤E/2 then lowerWeightQ u else upperWeightQ E u

theorem triangleMultiplicity_lower (E n : Nat) (hn : n≤E/2) :
    triangleMultiplicity E n=n+1 := by
  unfold triangleMultiplicity
  rw [Nat.min_eq_left]
  have htwo : 2*n≤E :=
    (Nat.mul_le_mul_left 2 hn).trans (Nat.mul_div_le E 2)
  omega

theorem triangleMultiplicity_upper (E n : Nat) (hnlo : E/2<n) (hnhi : n≤E) :
    triangleMultiplicity E n=E-n+1 := by
  unfold triangleMultiplicity
  rw [Nat.min_eq_right]
  have htwo : E<2*n := by
    have h := Nat.lt_mul_of_div_lt hnlo (by norm_num : 0<2)
    simpa only [Nat.mul_comm] using h
  omega

theorem triangle_card_prefix_lower (E h : Nat) (hh : h≤E/2) :
    ((∑ n ∈ Finset.range (h+1),triangleMultiplicity E n : Nat):ℚ)=lowerCardQ h := by
  calc
    _ = ∑ n ∈ Finset.range (h+1),((n+1:Nat):ℚ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : n≤E/2 :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hh
      rw [triangleMultiplicity_lower E n hnle]
      norm_num
    _ = ∑ n ∈ Finset.range (h+1),(1+(n:ℚ)+0*(n:ℚ)^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      ring
    _ = _ := by
      have hs := WeightedQuadricHighRankSum6900.rat_quadratic_sum h 1 1 0
      simp only [one_mul,zero_mul,add_zero] at hs
      simp only [zero_mul,add_zero]
      rw [hs]
      unfold lowerCardQ
      field_simp
      ring

theorem triangle_weight_prefix_lower (E h : Nat) (hh : h≤E/2) :
    ((∑ n ∈ Finset.range (h+1),
      triangleMultiplicity E n*n : Nat):ℚ)=lowerWeightQ h := by
  calc
    _ = ∑ n ∈ Finset.range (h+1),(((n+1)*n:Nat):ℚ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : n≤E/2 :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hh
      rw [triangleMultiplicity_lower E n hnle]
      norm_num
    _ = ∑ n ∈ Finset.range (h+1),(0+(n:ℚ)+1*(n:ℚ)^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      ring
    _ = _ := by
      have hs := WeightedQuadricHighRankSum6900.rat_quadratic_sum h 0 1 1
      simp only [one_mul,zero_mul,zero_add] at hs
      simp only [zero_add,one_mul]
      rw [hs]
      unfold lowerWeightQ
      field_simp
      ring

theorem triangle_card_prefix_upper (E h : Nat) (hhlo : E/2<h) (hhhi : h≤E) :
    ((∑ n ∈ Finset.range (h+1),triangleMultiplicity E n : Nat):ℚ)=upperCardQ E h := by
  let a:=E/2
  have ha : a<h := hhlo
  have hsplit : h+1=(a+1)+(h-a) := by dsimp [a]; omega
  rw [hsplit,Finset.sum_range_add]
  push_cast
  have hlower := triangle_card_prefix_lower E a (by simp [a])
  push_cast at hlower
  rw [hlower]
  have htail :
      (∑ i ∈ Finset.range (h-a),
        ((triangleMultiplicity E (a+1+i):Nat):ℚ))=
      ∑ i ∈ Finset.range (h-a),((E-(a+1+i)+1:Nat):ℚ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hilo : E/2<a+1+i := by dsimp [a]; omega
    have hihi : a+1+i≤E := by
      have hi' := Finset.mem_range.mp hi
      have hai : a+1+i≤h := by omega
      exact hai.trans hhhi
    rw [triangleMultiplicity_upper E (a+1+i) hilo hihi]
  rw [htail]
  have hcast :
      (∑ i ∈ Finset.range (h-a),((E-(a+1+i)+1:Nat):ℚ))=
      ∑ i ∈ Finset.range (h-a),(((E+1-(a+1):Nat):ℚ)-(i:ℚ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : a+1+i≤E := by
      have hai : a+1+i≤h := by omega
      exact hai.trans hhhi
    have heq : E-(a+1+i)+1=(E+1-(a+1))-i := by omega
    rw [heq,Nat.cast_sub (by omega)]
  rw [hcast]
  have hn : h-a=(h-a-1)+1 := by omega
  have hhaNat : h=a+(h-a-1)+1 := by omega
  have hha : (h:ℚ)=(a:ℚ)+(h-a-1:Nat)+1 := by exact_mod_cast hhaNat
  rw [hn]
  have hpoly := WeightedQuadricHighRankSum6900.rat_quadratic_sum
    (h-a-1) ((E+1-(a+1):Nat):ℚ) (-1) 0
  have hsum :
      (∑ i ∈ Finset.range (h-a-1+1),
        (((E+1-(a+1):Nat):ℚ)-(i:ℚ)))=
      (((h-a-1:Nat):ℚ)+1)*((E+1-(a+1):Nat):ℚ)+
        (-1)*(((h-a-1:Nat):ℚ)*((h-a-1:Nat)+1)/2)+
        0*(((h-a-1:Nat):ℚ)*((h-a-1:Nat)+1)*
          (2*(h-a-1:Nat)+1)/6) := by
    calc
      _ = ∑ i ∈ Finset.range (h-a-1+1),
          (((E+1-(a+1):Nat):ℚ)+(-1)*(i:ℚ)+0*(i:ℚ)^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := hpoly
  rw [hsum]
  unfold upperCardQ
  dsimp [a]
  push_cast
  field_simp
  nlinarith [hha]

theorem triangle_weight_prefix_upper (E h : Nat) (hhlo : E/2<h) (hhhi : h≤E) :
    ((∑ n ∈ Finset.range (h+1),triangleMultiplicity E n*n : Nat):ℚ)=
      upperWeightQ E h := by
  let a:=E/2
  have ha : a<h := hhlo
  have hsplit : h+1=(a+1)+(h-a) := by dsimp [a]; omega
  rw [hsplit,Finset.sum_range_add]
  push_cast
  have hlower := triangle_weight_prefix_lower E a (by simp [a])
  push_cast at hlower
  rw [hlower]
  have htail :
      (∑ i ∈ Finset.range (h-a),
        (triangleMultiplicity E (a+1+i):ℚ)*((a+1+i:Nat):ℚ))=
      ∑ i ∈ Finset.range (h-a),
        ((E-(a+1+i)+1:Nat):ℚ)*((a+1+i:Nat):ℚ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hilo : E/2<a+1+i := by dsimp [a]; omega
    have hihi : a+1+i≤E := by
      have hi' := Finset.mem_range.mp hi
      have hai : a+1+i≤h := by omega
      exact hai.trans hhhi
    rw [triangleMultiplicity_upper E (a+1+i) hilo hihi]
  have htail' :
      (∑ i ∈ Finset.range (h-a),
        (triangleMultiplicity E (a+1+i):ℚ)*((a:ℚ)+1+i))=
      ∑ i ∈ Finset.range (h-a),
        ((E-(a+1+i)+1:Nat):ℚ)*((a:ℚ)+1+i) := by
    simpa only [Nat.cast_add,Nat.cast_one] using htail
  rw [htail']
  have hcast :
      (∑ i ∈ Finset.range (h-a),
        ((E-(a+1+i)+1:Nat):ℚ)*((a:ℚ)+1+i))=
      ∑ i ∈ Finset.range (h-a),
        ((((E+1-(a+1):Nat):ℚ)-(i:ℚ))*((a:ℚ)+1)+(i:ℚ)*
          (((E+1-(a+1):Nat):ℚ)-(i:ℚ))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : a+1+i≤E := by
      have hai : a+1+i≤h := by omega
      exact hai.trans hhhi
    have heq : E-(a+1+i)+1=(E+1-(a+1))-i := by omega
    rw [heq,Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]
  have hn : h-a=(h-a-1)+1 := by omega
  have hhaNat : h=a+(h-a-1)+1 := by omega
  have hha : (h:ℚ)=(a:ℚ)+(h-a-1:Nat)+1 := by exact_mod_cast hhaNat
  rw [hn]
  have hpoly := WeightedQuadricHighRankSum6900.rat_quadratic_sum
    (h-a-1)
    (((E+1-(a+1):Nat):ℚ)*((a:ℚ)+1))
    (((E+1-(a+1):Nat):ℚ)-((a:ℚ)+1)) (-1)
  have hsum :
      (∑ i ∈ Finset.range (h-a-1+1),
        ((((E+1-(a+1):Nat):ℚ)-(i:ℚ))*((a:ℚ)+1)+(i:ℚ)*
          (((E+1-(a+1):Nat):ℚ)-(i:ℚ))))=
      (((h-a-1:Nat):ℚ)+1)*
          (((E+1-(a+1):Nat):ℚ)*((a:ℚ)+1))+
        (((E+1-(a+1):Nat):ℚ)-((a:ℚ)+1))*
          (((h-a-1:Nat):ℚ)*((h-a-1:Nat)+1)/2)+
        (-1)*(((h-a-1:Nat):ℚ)*((h-a-1:Nat)+1)*
          (2*(h-a-1:Nat)+1)/6) := by
    calc
      _ = ∑ i ∈ Finset.range (h-a-1+1),
          (((E+1-(a+1):Nat):ℚ)*((a:ℚ)+1)+
            (((E+1-(a+1):Nat):ℚ)-((a:ℚ)+1))*(i:ℚ)+
              (-1)*(i:ℚ)^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := hpoly
  rw [hsum]
  unfold upperWeightQ
  dsimp [a]
  field_simp
  nlinarith [hha]

theorem triangleCardPrefix_cast (E h : Nat) :
    (triangleCardPrefix E h:ℚ)=triangleCardQ E h := by
  unfold triangleCardPrefix triangleCardQ
  let u:=min E h
  have hu : u≤E := min_le_left _ _
  by_cases hlo : u≤E/2
  · rw [if_pos hlo]
    exact triangle_card_prefix_lower E u hlo
  · rw [if_neg hlo]
    exact triangle_card_prefix_upper E u (by omega) hu

theorem triangleWeightPrefix_cast (E h : Nat) :
    (triangleWeightPrefix E h:ℚ)=triangleWeightQ E h := by
  unfold triangleWeightPrefix triangleWeightQ
  let u:=min E h
  have hu : u≤E := min_le_left _ _
  by_cases hlo : u≤E/2
  · rw [if_pos hlo]
    exact triangle_weight_prefix_lower E u hlo
  · rw [if_neg hlo]
    exact triangle_weight_prefix_upper E u (by omega) hu

end ProximityPrize.SubmissionLower.WeightedTrianglePrefixFormulaW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedTrianglePrefixFormulaW1332216900.triangle_card_prefix_upper
#print axioms ProximityPrize.SubmissionLower.WeightedTrianglePrefixFormulaW1332216900.triangle_weight_prefix_upper
#print axioms ProximityPrize.SubmissionLower.WeightedTrianglePrefixFormulaW1332216900.triangleCardPrefix_cast
