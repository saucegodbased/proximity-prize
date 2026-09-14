import WeightedStageFibreBoundProbe6900
import WeightedSourceDerivativeBands6900

/-! A cost-aware but closed two-dimensional majorant for active source fibres. -/
namespace ProximityPrize.SubmissionLower.WeightedRelaxedFibreCoreW1332216900

open scoped BigOperators
open WeightedSourceColumnBands6900 WeightedSourceDerivativeBands6900
open WeightedStageFibreBoundProbe6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

def derivativePairs (E : Nat) : Finset (Nat×Nat) :=
  ((Finset.range (E/2+1)).product (Finset.range (E+1))).filter
    (fun p => p.2+2*p.1≤E)

def triangleMultiplicity (E n : Nat) : Nat := min n (E-n)+1

def relaxedPairCount (C W E : Nat) : Nat :=
  ∑ p ∈ derivativePairs E,
    ceilWidth W (C-(W-2)*(p.1+p.2))

def triangleRelaxedCount (C W E : Nat) : Nat :=
  ∑ n ∈ Finset.range (E+1),
    triangleMultiplicity E n*ceilWidth W (C-(W-2)*n)

theorem derivativePairs_fibre
    (E n : Nat) (hn : n≤E) :
    {p ∈ derivativePairs E | p.1+p.2=n}=
      (Finset.range (min n (E-n)+1)).map
        ⟨(fun t => (t,n-t)),fun a b h => by simpa using congrArg Prod.fst h⟩ := by
  ext p
  rw [Finset.mem_filter,Finset.mem_map]
  rw [show p∈derivativePairs E ↔
      p.1<E/2+1 ∧ p.2<E+1 ∧ p.2+2*p.1≤E by
    simp only [derivativePairs,Finset.mem_filter]
    constructor
    · rintro ⟨hp,hder⟩
      have hpair := Finset.mem_product.mp hp
      exact ⟨Finset.mem_range.mp hpair.1,Finset.mem_range.mp hpair.2,hder⟩
    · rintro ⟨ht,hr,hder⟩
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr ht,Finset.mem_range.mpr hr⟩,hder⟩]
  simp only [Finset.mem_range,Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨ht,hr,hder⟩,hsum⟩
    refine ⟨p.1,?_,?_⟩
    · have htle : p.1≤n := by omega
      have hcap : p.1≤E-n := by omega
      omega
    · apply Prod.ext
      · rfl
      · omega
  · rintro ⟨t,ht,rfl⟩
    have htn : t≤n := by omega
    have htE : t≤E-n := by omega
    refine ⟨⟨?_,?_,?_⟩,?_⟩
    · apply Nat.lt_succ_of_le
      omega
    · apply Nat.lt_succ_of_le
      omega
    · omega
    · omega

theorem derivativePairs_fibre_card (E n : Nat) (hn : n≤E) :
    ({p ∈ derivativePairs E | p.1+p.2=n}).card=triangleMultiplicity E n := by
  rw [derivativePairs_fibre E n hn]
  simp [triangleMultiplicity]

theorem relaxedPairCount_eq_triangle (C W E : Nat) :
    relaxedPairCount C W E=triangleRelaxedCount C W E := by
  unfold relaxedPairCount triangleRelaxedCount
  have hmap : ∀ p∈derivativePairs E,p.1+p.2∈Finset.range (E+1) := by
    intro p hp
    have hder := (Finset.mem_filter.mp hp).2
    apply Finset.mem_range.mpr
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro n hn
  have hnE : n≤E := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  calc
    (∑ p ∈ {p ∈ derivativePairs E | p.1+p.2=n},
      ceilWidth W (C-(W-2)*(p.1+p.2))) =
        ∑ _p ∈ {p ∈ derivativePairs E | p.1+p.2=n},
          ceilWidth W (C-(W-2)*n) := by
      apply Finset.sum_congr rfl
      intro p hp
      have heq := (Finset.mem_filter.mp hp).2
      rw [heq]
    _ = triangleMultiplicity E n*ceilWidth W (C-(W-2)*n) := by
      rw [Finset.sum_const_nat]
      · rw [derivativePairs_fibre_card E n hnE]
      · intro p hp
        rfl

theorem relaxedPairCount_eq_nested (C W E : Nat) :
    relaxedPairCount C W E=
      ∑ t ∈ Finset.range (E/2+1),∑ r ∈ Finset.range (E+1),
        if r+2*t≤E then ceilWidth W (C-(W-2)*(t+r)) else 0 := by
  unfold relaxedPairCount derivativePairs
  rw [Finset.sum_filter]
  exact Finset.sum_product _ _ _

/-- Replacing the `r`-weight `W-1` by `W-2` only enlarges the set of active
fibres.  Unlike the box bound, this retains both the derivative triangle and
the full contact-cost decay. -/
theorem activeFibreCount_le_relaxedPairCount (C W E : Nat) (hW2 : 2≤W) :
    activeFibreCount C W E≤relaxedPairCount C W E := by
  rw [activeFibreCount,WeightedSourceColumnBands6900.fixedSum_eq_nested,
    relaxedPairCount_eq_nested]
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro r hr
  by_cases hder : r+2*t≤E
  · simp only [if_pos hder]
    have hpoint (y : Nat) :
        (if cost W ((t,r),y)<C then 1 else 0)≤
          min 1 ((C-(W-2)*(t+r))-W*y) := by
      by_cases hc : cost W ((t,r),y)<C
      · rw [if_pos hc]
        have hrelaxed : (W-2)*(t+r)+W*y<C := by
          have hcoef : W-2≤W-1 := by omega
          have hle : (W-2)*(t+r)+W*y≤cost W ((t,r),y) := by
            calc
              _ = (W-2)*t+(W-2)*r+W*y := by ring
              _ ≤ (W-2)*t+(W-1)*r+W*y := by
                exact Nat.add_le_add_right
                  (Nat.add_le_add_left (Nat.mul_le_mul_right r hcoef) _) _
              _ = _ := by unfold cost; ring
          exact hle.trans_lt hc
        have hpos : 0<(C-(W-2)*(t+r))-W*y := by omega
        omega
      · rw [if_neg hc]
        exact Nat.zero_le _
    calc
      (∑ y ∈ Finset.range (C/W+1),
          if cost W ((t,r),y)<C then 1 else 0)≤
        ∑ y ∈ Finset.range (C/W+1),
          min 1 ((C-(W-2)*(t+r))-W*y) :=
        Finset.sum_le_sum fun y hy => hpoint y
      _ = ∑ y ∈ Finset.range (C/W+1),
          min 1 ((C-(W-2)*(t+r))-(0+W*y)) := by simp
      _ ≤ ceilWidth W (C-(W-2)*(t+r)) := by
        simpa only [Nat.one_mul] using
          sum_min_width_le W (C-(W-2)*(t+r)) 0 1 (C/W+1) (by omega)
  · simp only [if_neg hder,Finset.sum_const_zero]
    exact le_rfl

end ProximityPrize.SubmissionLower.WeightedRelaxedFibreCoreW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedRelaxedFibreCoreW1332216900.relaxedPairCount_eq_triangle
#print axioms ProximityPrize.SubmissionLower.WeightedRelaxedFibreCoreW1332216900.activeFibreCount_le_relaxedPairCount
