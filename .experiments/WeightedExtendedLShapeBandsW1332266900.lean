import WeightedRelaxedFibreFormulaW1332266900
import WeightedActualProductBandGate6900

/-! Three relaxed helper-band theorems for the W=133226 extended L-shape. -/
namespace ProximityPrize.SubmissionLower.WeightedExtendedLShapeBandsW1332266900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedSourceBoxQuotient6900
open WeightedSourceColumnBands6900
open WeightedSourceDerivativeBands6900
open WeightedStageFibreBoundProbe6900
open WeightedActualProductBandGate6900
open WeightedRelaxedFibreCoreW1332246900
open WeightedTrianglePrefixFormulaW1332246900
open WeightedRelaxedFibreFormulaW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
noncomputable section

def sourceCutoff : Nat := 2130677530
def wordDegree : Nat := 133226
def derivativeCap : Nat := 5248
def stageMax : Nat := 2624
def stageDelta : Nat := 47189
def kernelLower : Nat := 132483198112574379

def helperProductBandSum {K : Type*} [Field K]
    (P : Poly4 K) (fuel : Nat) : Nat :=
  ∑ j∈Finset.range fuel,
    stageBand sourceCutoff wordDegree derivativeCap
      (mainDegree wordDegree P) (derivativeDegree P) stageDelta j

theorem triangleRelaxedCount_zero_133226 (E : Nat) :
    triangleRelaxedCount 0 133226 E=0 := by
  simp [triangleRelaxedCount,ceilWidth]

theorem sum_range_le_fixed_prefix_of_zero (f : Nat→Nat) (fuel cutoff : Nat)
    (hz : ∀ j,cutoff≤j→f j=0) :
    (∑ j ∈ Finset.range fuel,f j)≤∑ j ∈ Finset.range cutoff,f j := by
  by_cases hf : fuel≤cutoff
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hf)
      (fun _ _ _ => Nat.zero_le _)
  · have hcf : cutoff≤fuel := by omega
    have heq : (∑ j ∈ Finset.range cutoff,f j)=
        ∑ j ∈ Finset.range fuel,f j := by
      apply Finset.sum_subset (Finset.range_mono hcf)
      intro j hj hsmall
      apply hz j
      have hnot : ¬j<cutoff := fun h => hsmall (Finset.mem_range.mpr h)
      omega
    exact heq.ge

/-! ## Jet-heavy profile `(213,4)` -/

def j213Top (j : Nat) : Nat :=
  sourceCutoff-(j+1)*28376712-j*stageDelta

def j213Derivative (j : Nat) : Nat := derivativeCap-(j+1)*4

def j213RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (j213Top j) wordDegree (j213Derivative j)

theorem j213RelaxedCount_zero (j : Nat) (hj : 74≤j) :
    j213RelaxedCount j=0 := by
  have htop : j213Top j=0 := by
    unfold j213Top sourceCutoff stageDelta
    omega
  rw [j213RelaxedCount,htop]
  exact triangleRelaxedCount_zero_133226 _

theorem j213Top_mod_pos (j : Nat) (hj : j<74) :
    0<j213Top j%133226 := by
  interval_cases j <;> norm_num [j213Top,sourceCutoff,stageDelta]

theorem j213_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 74,j213RelaxedCount j)=2790849350931 := by
  have hcast : (((∑ j ∈ Finset.range 74,j213RelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 74,
        relaxedClosedQ (j213Top j) 133226 (j213Derivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · exact j213Top_mod_pos j (Finset.mem_range.mp hj)
    · unfold j213Derivative derivativeCap
      omega
  have heval :
      (∑ j ∈ Finset.range 74,
        relaxedClosedQ (j213Top j) 133226 (j213Derivative j))=
          (2790849350931:ℚ) := by
    norm_num (config := { maxSteps := 1200000 })
      [Finset.sum_range_succ,j213Top,j213Derivative,sourceCutoff,
      derivativeCap,stageDelta,relaxedClosedQ,triangleCardQ,triangleWeightQ,
      lowerCardQ,lowerWeightQ,upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

theorem j213_relaxed_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,j213RelaxedCount j)≤2790849350931 :=
  (sum_range_le_fixed_prefix_of_zero j213RelaxedCount fuel 74
    j213RelaxedCount_zero).trans_eq j213_relaxed_prefix_exact

variable {K : Type*} [Field K]

theorem j213_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hjet : 213≤jetDegree P) (hder : 4≤derivativeDegree P) (j : Nat) :
    stageBand sourceCutoff wordDegree derivativeCap (mainDegree wordDegree P)
        (derivativeDegree P) stageDelta j≤stageDelta*j213RelaxedCount j := by
  have hg : 28376712≤mainDegree wordDegree P := by
    have hm := (Nat.mul_le_mul_left (wordDegree-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree wordDegree P hP)
    norm_num [wordDegree] at hm
    exact hm
  have hs := stageBand_le_profile sourceCutoff wordDegree derivativeCap
    (mainDegree wordDegree P) 28376712 (derivativeDegree P) 4 stageDelta j
    (by norm_num [wordDegree]) hg hder
  calc
    _ ≤ stageDelta*activeFibreCount (j213Top j) wordDegree
        (j213Derivative j) := by
      simpa [j213Top,j213Derivative,sourceCutoff,wordDegree,derivativeCap,
        stageDelta] using hs
    _ ≤ stageDelta*relaxedPairCount (j213Top j) wordDegree
        (j213Derivative j) := Nat.mul_le_mul_left stageDelta
      (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num [wordDegree]))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem j213_product_band_le (P : Poly4 K) (hP : P≠0)
    (hjet : 213≤jetDegree P) (hder : 4≤derivativeDegree P)
    (fuel : Nat) :
    helperProductBandSum P fuel≤131697390021082959 := by
  unfold helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,stageDelta*j213RelaxedCount j :=
      Finset.sum_le_sum fun j hj => j213_stage_le_relaxed P hP hjet hder j
    _ = stageDelta*(∑ j ∈ Finset.range fuel,j213RelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ stageDelta*2790849350931 :=
      Nat.mul_le_mul_left stageDelta (j213_relaxed_sum_le fuel)
    _ = _ := by norm_num [stageDelta]

/-! ## Derivative-heavy profile `(33,56)` -/

def d56Top (j : Nat) : Nat :=
  sourceCutoff-(j+1)*4396392-j*stageDelta

def d56Derivative (j : Nat) : Nat := derivativeCap-(j+1)*56

def d56RelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (d56Top j) wordDegree (d56Derivative j)

theorem d56Top_mod_pos (j : Nat) (hj : j<93) :
    0<d56Top j%133226 := by
  interval_cases j <;> norm_num [d56Top,sourceCutoff,stageDelta]

theorem d56_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 93,d56RelaxedCount j)=2806036765035 := by
  have hcast : (((∑ j ∈ Finset.range 93,d56RelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 93,
        relaxedClosedQ (d56Top j) 133226 (d56Derivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · exact d56Top_mod_pos j (Finset.mem_range.mp hj)
    · unfold d56Derivative derivativeCap
      omega
  have heval :
      (∑ j ∈ Finset.range 93,
        relaxedClosedQ (d56Top j) 133226 (d56Derivative j))=
          (2806036765035:ℚ) := by
    norm_num (config := { maxSteps := 1200000 })
      [Finset.sum_range_succ,d56Top,d56Derivative,sourceCutoff,
      derivativeCap,stageDelta,relaxedClosedQ,triangleCardQ,triangleWeightQ,
      lowerCardQ,lowerWeightQ,upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

def d56TruncatedRelaxedCount (j : Nat) : Nat :=
  if j<93 then d56RelaxedCount j else 0

theorem d56TruncatedRelaxedCount_zero (j : Nat) (hj : 93≤j) :
    d56TruncatedRelaxedCount j=0 := by
  simp [d56TruncatedRelaxedCount,hj]

theorem d56_truncated_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,d56TruncatedRelaxedCount j)≤2806036765035 := by
  have hp : (∑ j ∈ Finset.range 93,d56TruncatedRelaxedCount j)=
      2806036765035 := by
    rw [show (∑ j ∈ Finset.range 93,d56TruncatedRelaxedCount j)=
        ∑ j ∈ Finset.range 93,d56RelaxedCount j by
      apply Finset.sum_congr rfl
      intro j hj
      simp [d56TruncatedRelaxedCount,Finset.mem_range.mp hj]]
    exact d56_relaxed_prefix_exact
  exact (sum_range_le_fixed_prefix_of_zero d56TruncatedRelaxedCount fuel 93
    d56TruncatedRelaxedCount_zero).trans_eq hp

theorem d56_stage_zero (P : Poly4 K) (hder : 56≤derivativeDegree P)
    (j : Nat) (hj : 93≤j) :
    stageBand sourceCutoff wordDegree derivativeCap (mainDegree wordDegree P)
      (derivativeDegree P) stageDelta j=0 := by
  unfold stageBand
  rw [if_neg]
  have hj1 : 94≤j+1 := by omega
  have hlo : 94*56≤(j+1)*56 := Nat.mul_le_mul_right 56 hj1
  have hhi : (j+1)*56≤(j+1)*derivativeDegree P :=
    Nat.mul_le_mul_left (j+1) hder
  have hcap : derivativeCap<(j+1)*derivativeDegree P := by
    norm_num [derivativeCap] at hlo ⊢
    omega
  omega

theorem d56_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hjet : 33≤jetDegree P) (hder : 56≤derivativeDegree P) (j : Nat) :
    stageBand sourceCutoff wordDegree derivativeCap (mainDegree wordDegree P)
        (derivativeDegree P) stageDelta j≤
      stageDelta*d56TruncatedRelaxedCount j := by
  by_cases hj : j<93
  · have hg : 4396392≤mainDegree wordDegree P := by
      have hm := (Nat.mul_le_mul_left (wordDegree-2) hjet).trans
        (mainDegree_ge_weighted_jetDegree wordDegree P hP)
      norm_num [wordDegree] at hm
      exact hm
    have hs := stageBand_le_profile sourceCutoff wordDegree derivativeCap
      (mainDegree wordDegree P) 4396392 (derivativeDegree P) 56 stageDelta j
      (by norm_num [wordDegree]) hg hder
    have hs' : stageBand sourceCutoff wordDegree derivativeCap
        (mainDegree wordDegree P) (derivativeDegree P) stageDelta j≤
        stageDelta*d56RelaxedCount j := by
      calc
        _ ≤ stageDelta*activeFibreCount (d56Top j) wordDegree
            (d56Derivative j) := by
          simpa [d56Top,d56Derivative,sourceCutoff,wordDegree,derivativeCap,
            stageDelta] using hs
        _ ≤ stageDelta*relaxedPairCount (d56Top j) wordDegree
            (d56Derivative j) := Nat.mul_le_mul_left stageDelta
          (activeFibreCount_le_relaxedPairCount _ _ _
            (by norm_num [wordDegree]))
        _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl
    simpa [d56TruncatedRelaxedCount,hj] using hs'
  · rw [d56_stage_zero P hder j (by omega)]
    exact Nat.zero_le _

theorem d56_product_band_le (P : Poly4 K) (hP : P≠0)
    (hjet : 33≤jetDegree P) (hder : 56≤derivativeDegree P)
    (fuel : Nat) :
    helperProductBandSum P fuel≤132414068905236615 := by
  unfold helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,stageDelta*d56TruncatedRelaxedCount j :=
      Finset.sum_le_sum fun j hj => d56_stage_le_relaxed P hP hjet hder j
    _ = stageDelta*(∑ j ∈ Finset.range fuel,
        d56TruncatedRelaxedCount j) := by rw [Finset.mul_sum]
    _ ≤ stageDelta*2806036765035 :=
      Nat.mul_le_mul_left stageDelta (d56_truncated_sum_le fuel)
    _ = _ := by norm_num [stageDelta]

/-! ## Isolated corner profile `(212,55)` -/

def cornerTop (j : Nat) : Nat :=
  sourceCutoff-(j+1)*28243488-j*stageDelta

def cornerDerivative (j : Nat) : Nat := derivativeCap-(j+1)*55

def cornerRelaxedCount (j : Nat) : Nat :=
  triangleRelaxedCount (cornerTop j) wordDegree (cornerDerivative j)

theorem cornerRelaxedCount_zero (j : Nat) (hj : 75≤j) :
    cornerRelaxedCount j=0 := by
  have htop : cornerTop j=0 := by
    unfold cornerTop sourceCutoff stageDelta
    omega
  rw [cornerRelaxedCount,htop]
  exact triangleRelaxedCount_zero_133226 _

theorem cornerTop_mod_pos (j : Nat) (hj : j<75) :
    0<cornerTop j%133226 := by
  interval_cases j <;> norm_num [cornerTop,sourceCutoff,stageDelta]

theorem corner_relaxed_prefix_exact :
    (∑ j ∈ Finset.range 75,cornerRelaxedCount j)=1921761785079 := by
  have hcast : (((∑ j ∈ Finset.range 75,cornerRelaxedCount j):Nat):ℚ)=
      ∑ j ∈ Finset.range 75,
        relaxedClosedQ (cornerTop j) 133226 (cornerDerivative j) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    apply triangleRelaxedCount_cast_closed
    · exact cornerTop_mod_pos j (Finset.mem_range.mp hj)
    · unfold cornerDerivative derivativeCap
      omega
  have heval :
      (∑ j ∈ Finset.range 75,
        relaxedClosedQ (cornerTop j) 133226 (cornerDerivative j))=
          (1921761785079:ℚ) := by
    norm_num (config := { maxSteps := 1200000 })
      [Finset.sum_range_succ,cornerTop,cornerDerivative,sourceCutoff,
      derivativeCap,stageDelta,relaxedClosedQ,triangleCardQ,triangleWeightQ,
      lowerCardQ,lowerWeightQ,upperCardQ,upperWeightQ]
  exact_mod_cast hcast.trans heval

theorem corner_relaxed_sum_le (fuel : Nat) :
    (∑ j ∈ Finset.range fuel,cornerRelaxedCount j)≤1921761785079 :=
  (sum_range_le_fixed_prefix_of_zero cornerRelaxedCount fuel 75
    cornerRelaxedCount_zero).trans_eq corner_relaxed_prefix_exact

theorem corner_stage_le_relaxed (P : Poly4 K) (hP : P≠0)
    (hjet : 212≤jetDegree P) (hder : 55≤derivativeDegree P) (j : Nat) :
    stageBand sourceCutoff wordDegree derivativeCap (mainDegree wordDegree P)
        (derivativeDegree P) stageDelta j≤stageDelta*cornerRelaxedCount j := by
  have hg : 28243488≤mainDegree wordDegree P := by
    have hm := (Nat.mul_le_mul_left (wordDegree-2) hjet).trans
      (mainDegree_ge_weighted_jetDegree wordDegree P hP)
    norm_num [wordDegree] at hm
    exact hm
  have hs := stageBand_le_profile sourceCutoff wordDegree derivativeCap
    (mainDegree wordDegree P) 28243488 (derivativeDegree P) 55 stageDelta j
    (by norm_num [wordDegree]) hg hder
  calc
    _ ≤ stageDelta*activeFibreCount (cornerTop j) wordDegree
        (cornerDerivative j) := by
      simpa [cornerTop,cornerDerivative,sourceCutoff,wordDegree,derivativeCap,
        stageDelta] using hs
    _ ≤ stageDelta*relaxedPairCount (cornerTop j) wordDegree
        (cornerDerivative j) := Nat.mul_le_mul_left stageDelta
      (activeFibreCount_le_relaxedPairCount _ _ _ (by norm_num [wordDegree]))
    _ = _ := by rw [relaxedPairCount_eq_triangle]; rfl

theorem corner_product_band_le (P : Poly4 K) (hP : P≠0)
    (hjet : 212≤jetDegree P) (hder : 55≤derivativeDegree P)
    (fuel : Nat) :
    helperProductBandSum P fuel≤90686016876092931 := by
  unfold helperProductBandSum
  calc
    _ ≤ ∑ j ∈ Finset.range fuel,stageDelta*cornerRelaxedCount j :=
      Finset.sum_le_sum fun j hj => corner_stage_le_relaxed P hP hjet hder j
    _ = stageDelta*(∑ j ∈ Finset.range fuel,cornerRelaxedCount j) := by
      rw [Finset.mul_sum]
    _ ≤ stageDelta*1921761785079 :=
      Nat.mul_le_mul_left stageDelta (corner_relaxed_sum_le fuel)
    _ = _ := by norm_num [stageDelta]

theorem extended_lshape_product_band_lt_kernel (P : Poly4 K) (hP : P≠0)
    (hprofile : (213≤jetDegree P ∧ 4≤derivativeDegree P) ∨
      (33≤jetDegree P ∧ 56≤derivativeDegree P) ∨
      (212≤jetDegree P ∧ 55≤derivativeDegree P)) (fuel : Nat) :
    helperProductBandSum P fuel<kernelLower := by
  rcases hprofile with hJ | hD | hC
  · exact (j213_product_band_le P hP hJ.1 hJ.2 fuel).trans_lt
      (by norm_num [kernelLower])
  · exact (d56_product_band_le P hP hD.1 hD.2 fuel).trans_lt
      (by norm_num [kernelLower])
  · exact (corner_product_band_le P hP hC.1 hC.2 fuel).trans_lt
      (by norm_num [kernelLower])

#print axioms j213_relaxed_prefix_exact
#print axioms d56_relaxed_prefix_exact
#print axioms corner_relaxed_prefix_exact
#print axioms extended_lshape_product_band_lt_kernel

end
end ProximityPrize.SubmissionLower.WeightedExtendedLShapeBandsW1332266900
