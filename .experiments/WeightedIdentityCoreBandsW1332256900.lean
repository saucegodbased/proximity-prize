import WeightedIdentityCoreColumnsW1332256900
import WeightedRelaxedFibreFormulaW1332246900
import WeightedActualProductBandGate6900
import WeightedHelperBandsArithmeticW1332246900

/-!
# Formal product-band gates for the W=133225 identity-core helper

Only three J211 stages and four D55 stages are nonzero at the small
`(m,k)=(550,61)` profile.  The proof evaluates their relaxed triangular
fibre counts symbolically, never by `decide` or `native_decide`.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityCoreBandsW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedSourceIndex6900
open WeightedSourceColumnBands6900
open WeightedSourceDerivativeBands6900
open WeightedStageFibreBoundProbe6900
open WeightedSourceBoxQuotient6900
open WeightedHelperBandsArithmeticW1332246900
open WeightedRelaxedFibreCoreW1332246900
open WeightedRelaxedFibreFormulaW1332246900
open WeightedTrianglePrefixFormulaW1332246900
open WeightedActualProductBandGate6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
noncomputable section

/-- No-wrap evaluation of one relaxed fibre width.  All seven live stages
below satisfy the stronger hypothesis `s+2*E≤W`. -/
theorem ceilWidth_no_wrap_133225 (C q s E n : Nat)
    (hs : 0<s) (hrem : s+2*E≤133225) (hnE : n≤E)
    (hC : C=q*133225+s) :
    ceilWidth 133225 (C-133223*n)=if n≤q then q+1-n else 0 := by
  unfold ceilWidth
  by_cases hnq : n≤q
  · rw [if_pos hnq]
    have hcost : 133223*n≤C := by rw [hC]; omega
    have hx : C-133223*n=(q-n)*133225+(s+2*n) := by
      have hsub := Nat.sub_add_cancel hcost
      have hqn := Nat.sub_add_cancel hnq
      omega
    rw [hx]
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  · rw [if_neg hnq]
    have hzero : C≤133223*n := by rw [hC]; omega
    rw [Nat.sub_eq_zero_of_le hzero]

/-- Closed no-wrap relaxed triangle in terms of the already-formalized
triangular cardinality and first-moment prefixes. -/
theorem triangleRelaxedCount_no_wrap_133225 (C q s E : Nat)
    (hs : 0<s) (hrem : s+2*E≤133225) (hC : C=q*133225+s) :
    triangleRelaxedCount C 133225 E=
      triangleCardPrefix E q*(q+1)-triangleWeightPrefix E q := by
  unfold triangleRelaxedCount
  have hrewrite :
      (∑ n ∈ Finset.range (E+1),
        triangleMultiplicity E n*ceilWidth 133225 (C-133223*n))=
      ∑ n ∈ Finset.range (E+1),
        if n≤q then triangleMultiplicity E n*(q+1-n) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ceilWidth_no_wrap_133225 C q s E n hs hrem
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) hC]
    split_ifs <;> simp
  rw [hrewrite,sum_if_le_eq_prefix]
  unfold triangleCardPrefix triangleWeightPrefix
  have hpoint (n : Nat) (hn : n∈Finset.range (min E q+1)) :
      triangleMultiplicity E n*(q+1-n)=
        triangleMultiplicity E n*(q+1)-triangleMultiplicity E n*n := by
    rw [Nat.mul_sub_left_distrib]
  calc
    _=∑ n ∈ Finset.range (min E q+1),
        (triangleMultiplicity E n*(q+1)-triangleMultiplicity E n*n) :=
      Finset.sum_congr rfl hpoint
    _=(∑ n ∈ Finset.range (min E q+1),triangleMultiplicity E n*(q+1))-
        ∑ n ∈ Finset.range (min E q+1),triangleMultiplicity E n*n := by
      rw [Finset.sum_tsub_distrib]
      intro n hn
      have hnq : n≤q := by have := Finset.mem_range.mp hn; omega
      exact Nat.mul_le_mul_left _ (hnq.trans (Nat.le_succ q))
    _=_ := by rw [Finset.sum_mul]

private theorem triangle_prefix_values_188_716 :
    triangleCardPrefix 188 716=9025 ∧ triangleWeightPrefix 188 716=848350 := by
  have hc := triangleCardPrefix_cast 188 716
  have hw := triangleWeightPrefix_cast 188 716
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

private theorem triangle_prefix_values_132_688 :
    triangleCardPrefix 132 688=4489 ∧ triangleWeightPrefix 132 688=296274 := by
  have hc := triangleCardPrefix_cast 132 688
  have hw := triangleWeightPrefix_cast 132 688
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

private theorem triangle_prefix_values_76_660 :
    triangleCardPrefix 76 660=1521 ∧ triangleWeightPrefix 76 660=57798 := by
  have hc := triangleCardPrefix_cast 76 660
  have hw := triangleWeightPrefix_cast 76 660
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

private theorem triangle_prefix_values_20_631 :
    triangleCardPrefix 20 631=121 ∧ triangleWeightPrefix 20 631=1210 := by
  have hc := triangleCardPrefix_cast 20 631
  have hw := triangleWeightPrefix_cast 20 631
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

private theorem triangle_prefix_values_242_532 :
    triangleCardPrefix 242 532=14884 ∧ triangleWeightPrefix 242 532=1800964 := by
  have hc := triangleCardPrefix_cast 242 532
  have hw := triangleWeightPrefix_cast 242 532
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

private theorem triangle_prefix_values_240_320 :
    triangleCardPrefix 240 320=14641 ∧ triangleWeightPrefix 240 320=1756920 := by
  have hc := triangleCardPrefix_cast 240 320
  have hw := triangleWeightPrefix_cast 240 320
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

private theorem triangle_prefix_values_238_108 :
    triangleCardPrefix 238 108=5995 ∧ triangleWeightPrefix 238 108=431640 := by
  have hc := triangleCardPrefix_cast 238 108
  have hw := triangleWeightPrefix_cast 238 108
  norm_num [triangleCardQ,triangleWeightQ,upperCardQ,upperWeightQ,
    lowerCardQ,lowerWeightQ] at hc hw
  constructor
  · exact_mod_cast hc
  · exact_mod_cast hw

theorem d55_relaxed_0 : triangleRelaxedCount 95496906 133225 188=5622575 := by
  rw [triangleRelaxedCount_no_wrap_133225 95496906 716 107806 188
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_188_716.1,triangle_prefix_values_188_716.2]

theorem d55_relaxed_1 : triangleRelaxedCount 91719472 133225 132=2796647 := by
  rw [triangleRelaxedCount_no_wrap_133225 91719472 688 60672 132
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_132_688.1,triangle_prefix_values_132_688.2]

theorem d55_relaxed_2 : triangleRelaxedCount 87942038 133225 76=947583 := by
  rw [triangleRelaxedCount_no_wrap_133225 87942038 660 13538 76
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_76_660.1,triangle_prefix_values_76_660.2]

theorem d55_relaxed_3 : triangleRelaxedCount 84164604 133225 20=75262 := by
  rw [triangleRelaxedCount_no_wrap_133225 84164604 631 99629 20
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_20_631.1,triangle_prefix_values_20_631.2]

theorem j211_relaxed_0 : triangleRelaxedCount 70983874 133225 242=6132208 := by
  rw [triangleRelaxedCount_no_wrap_133225 70983874 532 108174 242
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_242_532.1,triangle_prefix_values_242_532.2]

theorem j211_relaxed_1 : triangleRelaxedCount 42693408 133225 240=2942841 := by
  rw [triangleRelaxedCount_no_wrap_133225 42693408 320 61408 240
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_240_320.1,triangle_prefix_values_240_320.2]

theorem j211_relaxed_2 : triangleRelaxedCount 14402942 133225 238=221815 := by
  rw [triangleRelaxedCount_no_wrap_133225 14402942 108 14642 238
    (by norm_num) (by norm_num) (by norm_num)]
  rw [triangle_prefix_values_238_108.1,triangle_prefix_values_238_108.2]

def helperProductBandSum {K : Type*} [Field K] (P : Poly4 K) (fuel : Nat) : Nat :=
  ∑ j ∈ Finset.range fuel,
    stageBand 99227150 133225 244 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j

def d55RelaxedStage : Nat→Nat
  | 0 => 5622575
  | 1 => 2796647
  | 2 => 947583
  | 3 => 75262
  | _ => 0

def j211RelaxedStage : Nat→Nat
  | 0 => 6132208
  | 1 => 2942841
  | 2 => 221815
  | _ => 0

private theorem columns_zero (W D : Nat) : columns 0 W D=0 := by
  unfold columns WeightedSourceColumnWidths6900.widthSum
  simp [WeightedSourceIndex6900.pairWidth]

private theorem d55_stage_zero {K : Type*} [Field K] (P : Poly4 K)
    (hrho : 56≤derivativeDegree P) (j : Nat) (hj : 4≤j) :
    stageBand 99227150 133225 244 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j=0 := by
  unfold stageBand
  rw [if_neg]
  intro hfeasible
  have hj5 : 5≤j+1 := by omega
  have hlarge : 5*56≤(j+1)*derivativeDegree P :=
    Nat.mul_le_mul hj5 hrho
  omega

private theorem j211_stage_zero {K : Type*} [Field K] (P : Poly4 K)
    (hP : P≠0) (hjet : 212≤jetDegree P) (j : Nat) (hj : 3≤j) :
    stageBand 99227150 133225 244 (mainDegree 133225 P)
      (derivativeDegree P) 47190 j=0 := by
  have hg : 28243276≤mainDegree 133225 P := by
    exact (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
  unfold stageBand
  split_ifs
  · have hj4 : 4≤j+1 := by omega
    have hlarge : 4*28243276≤(j+1)*mainDegree 133225 P :=
      Nat.mul_le_mul hj4 hg
    have hbudget : 99227150≤(j+1)*mainDegree 133225 P := by omega
    simp [Nat.sub_eq_zero_of_le hbudget,columns_zero]
  · rfl

private theorem relaxed_stage_le (B W D g g₀ rho rho₀ delta j C E : Nat)
    (hW : 2≤W) (hC : B-(j+1)*g₀-j*delta=C)
    (hE : D-(j+1)*rho₀=E) (hg : g₀≤g) (hrho : rho₀≤rho) :
    stageBand B W D g rho delta j≤delta*triangleRelaxedCount C W E := by
  have hs := stageBand_le_profile B W D g g₀ rho rho₀ delta j
    (by omega) hg hrho
  rw [hC,hE] at hs
  exact hs.trans (Nat.mul_le_mul_left delta
    ((activeFibreCount_le_relaxedPairCount C W E hW).trans_eq
      (relaxedPairCount_eq_triangle C W E)))

theorem d55_product_band_le {K : Type*} [Field K]
    (P : Poly4 K) (hP : P≠0) (hrho : 56≤derivativeDegree P) (fuel : Nat) :
    helperProductBandSum P fuel≤445571141730 := by
  have hjet : 28≤jetDegree P := by
    have h := derivativeDegree_le_twice_jetDegree P
    omega
  have hg : 3730244≤mainDegree 133225 P := by
    exact (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
  have hprefix : helperProductBandSum P fuel≤
      ∑ j ∈ Finset.range 4,
        stageBand 99227150 133225 244 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := by
    unfold helperProductBandSum
    exact sum_range_le_fixed_prefix_of_zero _ fuel 4
      (fun j hj => d55_stage_zero P hrho j hj)
  calc
    _≤∑ j ∈ Finset.range 4,
        stageBand 99227150 133225 244 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := hprefix
    _≤∑ j ∈ Finset.range 4, 47190*d55RelaxedStage j := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      interval_cases j
      · simpa only [d55RelaxedStage,d55_relaxed_0] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 3730244 (derivativeDegree P) 56 47190
          0 95496906 188 (by norm_num) (by norm_num) (by norm_num) hg hrho)
      · simpa only [d55RelaxedStage,d55_relaxed_1] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 3730244 (derivativeDegree P) 56 47190
          1 91719472 132 (by norm_num) (by norm_num) (by norm_num) hg hrho)
      · simpa only [d55RelaxedStage,d55_relaxed_2] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 3730244 (derivativeDegree P) 56 47190
          2 87942038 76 (by norm_num) (by norm_num) (by norm_num) hg hrho)
      · simpa only [d55RelaxedStage,d55_relaxed_3] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 3730244 (derivativeDegree P) 56 47190
          3 84164604 20 (by norm_num) (by norm_num) (by norm_num) hg hrho)
    _=_ := by norm_num [Finset.sum_range_succ,d55RelaxedStage]

theorem j211_product_band_le {K : Type*} [Field K]
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P)
    (hjet : 212≤jetDegree P) (fuel : Nat) :
    helperProductBandSum P fuel≤438719012160 := by
  have hg : 28243276≤mainDegree 133225 P := by
    exact (Nat.mul_le_mul_left (133225-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree 133225 P hP)
  have hprefix : helperProductBandSum P fuel≤
      ∑ j ∈ Finset.range 3,
        stageBand 99227150 133225 244 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := by
    unfold helperProductBandSum
    exact sum_range_le_fixed_prefix_of_zero _ fuel 3
      (fun j hj => j211_stage_zero P hP hjet j hj)
  calc
    _≤∑ j ∈ Finset.range 3,
        stageBand 99227150 133225 244 (mainDegree 133225 P)
          (derivativeDegree P) 47190 j := hprefix
    _≤∑ j ∈ Finset.range 3, 47190*j211RelaxedStage j := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      interval_cases j
      · simpa only [j211RelaxedStage,j211_relaxed_0] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 28243276 (derivativeDegree P) 2 47190
          0 70983874 242 (by norm_num) (by norm_num) (by norm_num) hg hrho)
      · simpa only [j211RelaxedStage,j211_relaxed_1] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 28243276 (derivativeDegree P) 2 47190
          1 42693408 240 (by norm_num) (by norm_num) (by norm_num) hg hrho)
      · simpa only [j211RelaxedStage,j211_relaxed_2] using
          (relaxed_stage_le 99227150 133225 244
          (mainDegree 133225 P) 28243276 (derivativeDegree P) 2 47190
          2 14402942 238 (by norm_num) (by norm_num) (by norm_num) hg hrho)
    _=_ := by norm_num [Finset.sum_range_succ,j211RelaxedStage]

theorem expensive_product_band_lt_budget {K : Type*} [Field K]
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P) (fuel : Nat)
    (hprofile : 212≤jetDegree P ∨ 56≤derivativeDegree P) :
    helperProductBandSum P fuel<445782504611 := by
  rcases hprofile with hjet | hder
  · exact (j211_product_band_le P hP hrho hjet fuel).trans_lt (by norm_num)
  · exact (d55_product_band_le P hP hder fuel).trans_lt (by norm_num)

theorem conservative_band_margins :
    445782504611-438719012160=7063492451 ∧
      445782504611-445571141730=211362881 := by norm_num

#print axioms ceilWidth_no_wrap_133225
#print axioms triangleRelaxedCount_no_wrap_133225
#print axioms d55_product_band_le
#print axioms j211_product_band_le
#print axioms expensive_product_band_lt_budget

end
end ProximityPrize.SubmissionLower.WeightedIdentityCoreBandsW1332256900
