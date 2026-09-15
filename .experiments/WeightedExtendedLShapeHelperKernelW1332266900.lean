import WeightedCutoff2TargetW1332256900
import WeightedHelperColumnsW1332266900
import WeightedPolynomialContactKernel6900
import WeightedSourcePowerEscape6900

/-!
# Joint helper kernel and generic hard-L-shape escape at W=133226

The product-band producer is intentionally left as an input.  This prevents
an import cycle with the hard-L-shape band module while exposing the exact
kernel rank, low-power escape, tightened original box, and all-node contact
needed by the factor-certificate adapter.
-/
namespace ProximityPrize.SubmissionLower.WeightedExtendedLShapeHelperKernelW1332266900

open scoped BigOperators
open Order2SourceBasisScaffold
open WeightedSourceIndex6900 WeightedSourceSpace6900 WeightedSourceKernel6900
open WeightedSourceBoxQuotient6900 WeightedSourceColumnBands6900
open WeightedQuadricContactTarget6900
open WeightedPolynomialContactKernel6900 WeightedSourcePowerEscape6900
open WeightedCutoff2TargetW1332256900 WeightedHelperColumnsW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3000

noncomputable section

variable (K : Type*) [Field K]

def contactOrder : Nat := 11810
def sourceCutoff : Nat := 2130677530
def wordDegree : Nat := 133226
def sourceParameter : Nat := 1312
def derivativeCap : Nat := 5248
def stageMax : Nat := 2624
def stageDelta : Nat := 47189
def kernelLower : Nat := 132483198112574379

/-- The exact reconstructed polynomial kernel at the joint helper profile. -/
def helperPolynomialKernel (I : Type*) [Fintype I]
    (htwo : (2:K)≠0) (nodes values : I→K) : Submodule K (Poly4 K) :=
  polynomialKernel K I htwo 11810 2130677530 133226
    1312 (by norm_num) nodes values

theorem helperPolynomialKernel_le_box (I : Type*) [Fintype I]
    (htwo : (2:K)≠0) (nodes values : I→K) :
    helperPolynomialKernel K I htwo nodes values≤
      weightedCoefficientBox K sourceCutoff wordDegree derivativeCap := by
  simpa only [helperPolynomialKernel,sourceCutoff,wordDegree,derivativeCap,
    Nat.reduceMul] using
      polynomialKernel_le_box K I htwo 11810 2130677530 133226
        1312 (by norm_num) nodes values

/-- Exact dimension receipt:

`82571120962332601259 - 262144*314478446061020
  = 132483198112574379`.
-/
theorem helperPolynomialKernel_dimension
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144) :
    kernelLower≤Module.finrank K
      (helperPolynomialKernel K I htwo nodes values) := by
  change 132483198112574379≤Module.finrank K
    (helperPolynomialKernel K I htwo nodes values)
  have hr := helper_totalTarget_rank_le K htwo
  have hg := globalKernel_finrank_lower K I htwo 11810 2130677530
    133226 1312 (by norm_num) nodes values
  norm_num only [Nat.reduceMul,Nat.reduceSub,Nat.reduceDiv] at hg
  have hproduct : Fintype.card I*
      Module.finrank K (totalTarget K 11810 15993 1312)≤
        262144*314478446061020 := Nat.mul_le_mul hn hr
  have hsource := helper_columns_lower
  have hbudget :
      132483198112574379≤columns 2130677530 133226 5248-
        Fintype.card I*
          Module.finrank K (totalTarget K 11810 15993 1312) := by
    omega
  unfold helperPolynomialKernel
  rw [polynomialKernel_finrank]
  exact hbudget.trans hg

/-- The literal band sum whose strict comparison with the actual kernel rank
is the only numerical premise of the generic escape theorem. -/
def productBandSum (P : Poly4 K) : Nat :=
  ∑ j∈Finset.range stageMax,
    stageBand sourceCutoff wordDegree derivativeCap
      (mainDegree wordDegree P) (derivativeDegree P) stageDelta j

theorem productBand_lt_kernel_of_lt_lower
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144)
    (P : Poly4 K) (hband : productBandSum K P<kernelLower) :
    productBandSum K P<
      Module.finrank K (helperPolynomialKernel K I htwo nodes values) :=
  hband.trans_le (helperPolynomialKernel_dimension K I htwo nodes values hn)

/-- Generic low-power escape at fuel `2624`.  The caller supplies only the
strict product-band comparison, so a separately compiled band module can
instantiate this theorem without being imported here. -/
theorem product_escape_of_band_lt_kernel
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K)
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P)
    (hband : productBandSum K P<
      Module.finrank K (helperPolynomialKernel K I htwo nodes values)) :
    ∃ (j : Nat) (G : Poly4 K),
      j≤stageMax ∧ G≠0 ∧ ¬P∣G ∧
      P^j*G∈helperPolynomialKernel K I htwo nodes values ∧
      G∈weightedCoefficientBox K
        (sourceCutoff-j*mainDegree wordDegree P-j*stageDelta) wordDegree
        (derivativeCap-j*derivativeDegree P) ∧
      P^j*G∈weightedCoefficientBox K
        (sourceCutoff-j*stageDelta) wordDegree derivativeCap ∧
      (∀ i:I,contactTruncation K contactOrder
        (localSubstitution K (nodes i) (values i) (P^j*G))=0) ∧
      P^j*G≠0 ∧ j*mainDegree wordDegree P<sourceCutoff ∧
      j*derivativeDegree P≤derivativeCap := by
  let V := helperPolynomialKernel K I htwo nodes values
  have hV : V≤weightedCoefficientBox K sourceCutoff wordDegree derivativeCap :=
    helperPolynomialKernel_le_box K I htwo nodes values
  have hterminal : derivativeCap<(stageMax+1)*derivativeDegree P := by
    norm_num [derivativeCap,stageMax]
    omega
  obtain ⟨j,G,hj,hG,hOriginal,hQuotient,hnot,hmain,hder⟩ :=
    exists_low_power_quotient V P sourceCutoff wordDegree derivativeCap
      stageDelta stageMax (by norm_num [wordDegree]) hV hP hband
      (Or.inr hterminal)
  have hstage : G∈powerStage V P sourceCutoff wordDegree derivativeCap
      stageDelta j := ⟨hOriginal,hQuotient⟩
  have htight := stage_original_mem_tightened V P G sourceCutoff wordDegree
    derivativeCap stageDelta j hV hP hG hstage
  have hcontact := polynomialKernel_contact K I htwo contactOrder sourceCutoff
    wordDegree sourceParameter (by norm_num [wordDegree]) nodes values hOriginal
  exact ⟨j,G,hj,hG,hnot,hOriginal,hQuotient,htight,hcontact,
    mul_ne_zero (pow_ne_zero j hP) hG,hmain,hder⟩

/-- Numeric wrapper matching the hard-L-shape band's conservative endpoint.
It turns `< kernelLower` into the direct premise above using the dimension
receipt. -/
theorem product_escape_of_band_lt_lower
    (I : Type*) [Fintype I] (htwo : (2:K)≠0)
    (nodes values : I→K) (hn : Fintype.card I≤262144)
    (P : Poly4 K) (hP : P≠0) (hrho : 2≤derivativeDegree P)
    (hband : productBandSum K P<kernelLower) :
    ∃ (j : Nat) (G : Poly4 K),
      j≤stageMax ∧ G≠0 ∧ ¬P∣G ∧
      P^j*G∈helperPolynomialKernel K I htwo nodes values ∧
      G∈weightedCoefficientBox K
        (sourceCutoff-j*mainDegree wordDegree P-j*stageDelta) wordDegree
        (derivativeCap-j*derivativeDegree P) ∧
      P^j*G∈weightedCoefficientBox K
        (sourceCutoff-j*stageDelta) wordDegree derivativeCap ∧
      (∀ i:I,contactTruncation K contactOrder
        (localSubstitution K (nodes i) (values i) (P^j*G))=0) ∧
      P^j*G≠0 ∧ j*mainDegree wordDegree P<sourceCutoff ∧
      j*derivativeDegree P≤derivativeCap := by
  apply product_escape_of_band_lt_kernel K I htwo nodes values P hP hrho
  exact productBand_lt_kernel_of_lt_lower K I htwo nodes values hn P hband

theorem kernel_arithmetic_receipt :
    82571120962332601259-262144*314478446061020=kernelLower ∧
    derivativeCap=4*sourceParameter ∧ stageMax*2=derivativeCap := by
  norm_num [kernelLower,derivativeCap,sourceParameter,stageMax]

#print axioms helperPolynomialKernel_dimension
#print axioms productBand_lt_kernel_of_lt_lower
#print axioms product_escape_of_band_lt_kernel
#print axioms product_escape_of_band_lt_lower
#print axioms kernel_arithmetic_receipt

end
end ProximityPrize.SubmissionLower.WeightedExtendedLShapeHelperKernelW1332266900
