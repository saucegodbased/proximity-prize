import WeightedRelaxedFibreFormulaW1332256900
import WeightedQuadricSourcePairSum6900

/-! Fast continuous and terminal arithmetic receipts for the cutoff-two helper. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2ContinuousArithmeticW1332256900
open scoped BigOperators
open ProximityPrize.SubmissionLower.WeightedSourceDerivativeBands6900
open ProximityPrize.SubmissionLower.WeightedRelaxedFibreCoreW1332246900
open ProximityPrize.SubmissionLower.WeightedTrianglePrefixFormulaW1332246900
open ProximityPrize.SubmissionLower.WeightedQuadricHighRankSum6900
open ProximityPrize.SubmissionLower.WeightedQuadricSourcePairSum6900
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500

theorem fullCard_even (a : Nat) :
    triangleCardQ (2*a) (2*a)=(a+1)^2 := by
  cases a with
  | zero => norm_num [triangleCardQ,upperCardQ,lowerCardQ]
  | succ a =>
      simp [triangleCardQ,upperCardQ,lowerCardQ]
      push_cast
      ring

theorem fullWeight_even (a : Nat) :
    triangleWeightQ (2*a) (2*a)=a*(a+1)^2 := by
  cases a with
  | zero => norm_num [triangleWeightQ,upperWeightQ,lowerWeightQ]
  | succ a =>
      simp [triangleWeightQ,upperWeightQ,lowerWeightQ]
      push_cast
      ring

def continuousNumerator (C W E : Nat) : Nat :=
  ∑ n ∈ Finset.range (E+1),
    triangleMultiplicity E n*(C-(W-2)*n+W-1)

theorem ceilWidth_scaled_le (W C : Nat) :
    W*ceilWidth W C≤C+W-1 := by
  unfold ceilWidth
  simpa only [Nat.mul_comm] using Nat.div_mul_le_self (C+W-1) W

theorem triangleRelaxedCount_scaled_le (C W E : Nat) :
    W*triangleRelaxedCount C W E≤continuousNumerator C W E := by
  unfold triangleRelaxedCount continuousNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  calc
    W*(triangleMultiplicity E n*ceilWidth W (C-(W-2)*n)) =
        triangleMultiplicity E n*(W*ceilWidth W (C-(W-2)*n)) := by ring
    _ ≤ triangleMultiplicity E n*((C-(W-2)*n)+W-1) :=
      Nat.mul_le_mul_left _ (ceilWidth_scaled_le W (C-(W-2)*n))

theorem continuousNumerator_cast_full (C W E : Nat) (hW : 2≤W)
    (hcost : (W-2)*E≤C) :
    (continuousNumerator C W E:ℚ)=
      (C+W-1)*triangleCardQ E E-
        (W-2)*triangleWeightQ E E := by
  have hcard := triangleCardPrefix_cast E E
  have hweight := triangleWeightPrefix_cast E E
  unfold triangleCardPrefix at hcard
  unfold triangleWeightPrefix at hweight
  simp only [Nat.min_self] at hcard hweight
  push_cast at hcard hweight
  unfold continuousNumerator
  push_cast
  calc
    (∑ n ∈ Finset.range (E+1),
        (triangleMultiplicity E n:ℚ)*↑(C-(W-2)*n+W-1)) =
      ∑ n ∈ Finset.range (E+1),
        (triangleMultiplicity E n:ℚ)*
          ((C+W-1:ℚ)-(W-2)*n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnE : n≤E := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        have hcn : (W-2)*n≤C := (Nat.mul_le_mul_left (W-2) hnE).trans hcost
        have hx : C-(W-2)*n+W-1=C+W-1-(W-2)*n := by omega
        rw [hx,Nat.cast_sub]
        · rw [Nat.cast_sub (by omega : 1≤C+W),Nat.cast_mul,
            Nat.cast_sub hW]
          push_cast
          rfl
        · omega
    _ = ∑ n ∈ Finset.range (E+1),
        ((C+W-1:ℚ)*(triangleMultiplicity E n:ℚ)-
          (W-2:ℚ)*((triangleMultiplicity E n*n:Nat):ℚ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      ring
    _ = (C+W-1)*(∑ n ∈ Finset.range (E+1),
          (triangleMultiplicity E n:ℚ))-
        (W-2)*(∑ n ∈ Finset.range (E+1),
          ((triangleMultiplicity E n*n:Nat):ℚ)) := by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ = _ := by push_cast; rw [hcard,hweight]

def jC (j : Nat) : Nat := 2102434254-28290466*j
def jE (j : Nat) : Nat := 5246-2*j

theorem jContinuous_cast (j : Nat) (hj : j<51) :
    (continuousNumerator (jC j) 133225 (jE j):ℚ)=
      12070914809319424+(-203073597563520)*(j:ℚ)+
        149522334813*(j:ℚ)^2+(-28157243)*(j:ℚ)^3 := by
  rw [continuousNumerator_cast_full]
  · have hE : jE j=2*(2623-j) := by unfold jE; omega
    rw [hE,fullCard_even,fullWeight_even]
    unfold jC
    rw [Nat.cast_sub (by omega : 28290466*j≤2102434254)]
    push_cast
    rw [Nat.cast_sub (by omega : j≤2623)]
    push_cast
    ring
  · norm_num
  · unfold jC jE
    omega

theorem jContinuous_total :
    (∑ j ∈ Finset.range 51,continuousNumerator (jC j) 133225 (jE j))=
      363070291485498774 := by
  have hcast :
      (((∑ j ∈ Finset.range 51,
        continuousNumerator (jC j) 133225 (jE j)):Nat):ℚ)=
        ∑ j ∈ Finset.range 51,
          (12070914809319424+(-203073597563520)*(j:ℚ)+
            149522334813*(j:ℚ)^2+(-28157243)*(j:ℚ)^3) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    exact jContinuous_cast j (Finset.mem_range.mp hj)
  have heval :
      (∑ j ∈ Finset.range 51,
          (12070914809319424+(-203073597563520)*(j:ℚ)+
            149522334813*(j:ℚ)^2+(-28157243)*(j:ℚ)^3))=
        (363070291485498774:ℚ) := by
    rw [show 51=50+1 by norm_num,rat_cubic_sum]
    norm_num
  exact_mod_cast hcast.trans heval

def dC (j : Nat) : Nat := 2126947286-3777434*j
def dE (j : Nat) : Nat := 5192-56*j

theorem dContinuous_cast (j : Nat) (hj : j<93) :
    (continuousNumerator (dC j) 133225 (dE j):ℚ)=
      12013367936431218+(-259366633866774)*(j:ℚ)+
        1403350080048*(j:ℚ)^2+(-36996960)*(j:ℚ)^3 := by
  rw [continuousNumerator_cast_full]
  · have hE : dE j=2*(2596-28*j) := by unfold dE; omega
    rw [hE,fullCard_even,fullWeight_even]
    unfold dC
    rw [Nat.cast_sub (by omega : 3777434*j≤2126947286)]
    push_cast
    rw [Nat.cast_sub (by omega : 28*j≤2596)]
    push_cast
    ring
  · norm_num
  · unfold dC dE
    omega

theorem dContinuous_total :
    (∑ j ∈ Finset.range 93,continuousNumerator (dC j) 133225 (dE j))=
      377213451151410342 := by
  have hcast :
      (((∑ j ∈ Finset.range 93,
        continuousNumerator (dC j) 133225 (dE j)):Nat):ℚ)=
        ∑ j ∈ Finset.range 93,
          (12013367936431218+(-259366633866774)*(j:ℚ)+
            1403350080048*(j:ℚ)^2+(-36996960)*(j:ℚ)^3) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    exact dContinuous_cast j (Finset.mem_range.mp hj)
  have heval :
      (∑ j ∈ Finset.range 93,
          (12013367936431218+(-259366633866774)*(j:ℚ)+
            1403350080048*(j:ℚ)^2+(-36996960)*(j:ℚ)^3))=
        (377213451151410342:ℚ) := by
    rw [show 93=92+1 by norm_num,rat_cubic_sum]
    norm_num
  exact_mod_cast hcast.trans heval

theorem jC_mod_pos (j : Nat) (hj : j<75) : 0<jC j%133225 := by
  have htop : 0<jC j := by unfold jC; omega
  have hjne : j≠29294 := by omega
  have hcost : 28290466*j≤2102434254 := by unfold jC at htop; omega
  apply Nat.pos_of_ne_zero
  intro hz
  have hd : 133225∣jC j := Nat.dvd_of_mod_eq_zero hz
  obtain ⟨q,hq⟩ := hd
  unfold jC at hq
  have hlin : 28290466*j+133225*q=2102434254 := by
    simpa [Nat.add_comm] using ((Nat.sub_eq_iff_eq_add hcost).mp hq).symm
  have hscaled :
      j+133225*(1679909*j+7911*q)=29294+133225*124844116 := by
    calc
      _ = 7911*(28290466*j+133225*q) := by ring
      _ = 7911*2102434254 := by rw [hlin]
      _ = _ := by norm_num
  have hjW : j<133225 := hj.trans (by norm_num)
  have hm := congrArg (fun x : Nat => x%133225) hscaled
  have hlj : j%133225=j := Nat.mod_eq_of_lt hjW
  have hl0 :
      (j+133225*(1679909*j+7911*q))%133225=j%133225 :=
    Nat.add_mul_mod_self_left j 133225 (1679909*j+7911*q)
  have hr0 :
      (29294+133225*124844116)%133225=29294%133225 :=
    Nat.add_mul_mod_self_left 29294 133225 124844116
  have hrn : 29294%133225=29294 := Nat.mod_eq_of_lt (by norm_num)
  exact hjne (hlj.symm.trans (hl0.symm.trans (hm.trans (hr0.trans hrn))))

open ProximityPrize.SubmissionLower.WeightedRelaxedFibreFormulaW1332256900

def jClosedSegment (a n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n,relaxedClosedQ (jC (a+i)) 133225 (jE (a+i))

theorem jClosedSegment_add (a u v : Nat) :
    jClosedSegment a (u+v)=jClosedSegment a u+jClosedSegment (a+u) v := by
  simpa only [jClosedSegment,Finset.sum_range_add,Nat.add_assoc]

theorem jClosed_51_4 : jClosedSegment 51 4=54710120578 := by
  norm_num (config := { maxSteps := 300000 })
    [jClosedSegment,Finset.sum_range_succ,jC,jE,relaxedClosedQ,
    triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
    upperCardQ,upperWeightQ]

theorem jClosed_55_5 : jClosedSegment 55 5=39526103914 := by
  norm_num (config := { maxSteps := 300000 })
    [jClosedSegment,Finset.sum_range_succ,jC,jE,relaxedClosedQ,
    triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
    upperCardQ,upperWeightQ]

theorem jClosed_60_5 : jClosedSegment 60 5=15480569900 := by
  norm_num (config := { maxSteps := 300000 })
    [jClosedSegment,Finset.sum_range_succ,jC,jE,relaxedClosedQ,
    triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
    upperCardQ,upperWeightQ]

theorem jClosed_65_5 : jClosedSegment 65 5=3484115895 := by
  norm_num (config := { maxSteps := 300000 })
    [jClosedSegment,Finset.sum_range_succ,jC,jE,relaxedClosedQ,
    triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
    upperCardQ,upperWeightQ]

theorem jClosed_70_5 : jClosedSegment 70 5=211308948 := by
  norm_num (config := { maxSteps := 300000 })
    [jClosedSegment,Finset.sum_range_succ,jC,jE,relaxedClosedQ,
    triangleCardQ,triangleWeightQ,lowerCardQ,lowerWeightQ,
    upperCardQ,upperWeightQ]

theorem jClosed_terminal : jClosedSegment 51 24=113412219235 := by
  rw [show 24=4+20 by norm_num,jClosedSegment_add,jClosed_51_4]
  norm_num only [Nat.reduceAdd]
  rw [show 20=5+15 by norm_num,jClosedSegment_add,jClosed_55_5]
  norm_num only [Nat.reduceAdd]
  rw [show 15=5+10 by norm_num,jClosedSegment_add,jClosed_60_5]
  norm_num only [Nat.reduceAdd]
  rw [show 10=5+5 by norm_num,jClosedSegment_add,jClosed_65_5]
  norm_num only [Nat.reduceAdd]
  rw [jClosed_70_5]
  norm_num

theorem jRelaxed_terminal :
    (∑ i ∈ Finset.range 24,
      triangleRelaxedCount (jC (51+i)) 133225 (jE (51+i)))=
        113412219235 := by
  have hcast :
      (((∑ i ∈ Finset.range 24,
        triangleRelaxedCount (jC (51+i)) 133225 (jE (51+i))):Nat):ℚ)=
          jClosedSegment 51 24 := by
    unfold jClosedSegment
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    apply triangleRelaxedCount_cast_closed
    · apply jC_mod_pos
      have := Finset.mem_range.mp hi
      omega
    · unfold jE
      have := Finset.mem_range.mp hi
      omega
  exact_mod_cast hcast.trans jClosed_terminal


def jRelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (jC j) 133225 (jE j)

def dRelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (dC j) 133225 (dE j)

end ProximityPrize.SubmissionLower.WeightedCutoff2ContinuousArithmeticW1332256900
