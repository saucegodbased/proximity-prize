import ProximityPrize.Benchmark.TargetLower
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Exact physical/normalized ratio boundary on the m69 DataEleven leaf

The actual cross gives `(B*E0)*wedge = B*N0`.  Since `E0` is root-free on
the NTT domain, the normalized ratio `W=N0/E0` is globally defined and obeys
`E0*W=N0`.  It is provably equal to the physical wedge only away from roots
of `B`.  At a `B`-root the original cross is vacuous; the imported explicit
counterexample proves that no all-node cancellation principle is available.
-/

namespace ProximityPrize.SubmissionLower.M69DataElevenPhysicalRatioBoundary6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- The global normalized ratio attached to a root-free denominator. -/
def normalizedRatio
    {I K : Type*} [Field K] (nodes : I -> K) (E0 N0 : K[X]) : I -> K :=
  fun i => N0.eval (nodes i) / E0.eval (nodes i)

theorem normalizedRatio_den_mul
    {I K : Type*} [Field K] (nodes : I -> K) (E0 N0 : K[X])
    (hroot : forall i, E0.eval (nodes i) ≠ 0) :
    forall i, E0.eval (nodes i) * normalizedRatio nodes E0 N0 i =
      N0.eval (nodes i) := by
  intro i
  exact mul_div_cancel₀ _ (hroot i)

theorem cancel_factored_cross_at_nonroot
    {K : Type*} [Field K] (B E N : K[X]) (x z : K)
    (hB : B.eval x ≠ 0)
    (hcross : (B * E).eval x * z = (B * N).eval x) :
    E.eval x * z = N.eval x := by
  simp only [eval_mul] at hcross
  apply mul_left_cancel₀ hB
  simpa only [mul_assoc] using hcross

/-- A zero common factor makes cancellation logically invalid, even when the
normalized denominator is nonzero. -/
theorem zero_common_factor_counterexample
    {K : Type*} [Field K] :
    let b : K := 0
    let e : K := 1
    let n : K := 1
    let z : K := 0
    b * e * z = b * n ∧ e ≠ 0 ∧ e * z ≠ n := by
  simp

/-- Strongest ratio statement derivable from the factored physical cross.
The DataEleven leaf supplies these exact hypotheses with
`nodes=IRSProfile.domain` and `physicalW=d*U0-c*U1`.  The final clause must
remain restricted to the complement of the common-factor roots. -/
theorem normalized_ratio_and_physical_off_common_factor
    {I K : Type*} [Field K] (nodes : I -> K)
    (B E0 N0 : K[X]) (physicalW : I -> K)
    (hroot : forall i, E0.eval (nodes i) ≠ 0)
    (hcross : forall i,
      (B * E0).eval (nodes i) * physicalW i =
        (B * N0).eval (nodes i)) :
    let W := normalizedRatio nodes E0 N0
    (forall i, E0.eval (nodes i) * W i = N0.eval (nodes i)) ∧
      (forall i, B.eval (nodes i) ≠ 0 -> W i = physicalW i) := by
  dsimp only
  refine ⟨normalizedRatio_den_mul nodes E0 N0 hroot, ?_⟩
  intro i hBi
  have hphysical := cancel_factored_cross_at_nonroot B E0 N0
    (nodes i) (physicalW i) hBi (hcross i)
  apply mul_left_cancel₀ (hroot i)
  calc
    E0.eval (nodes i) * normalizedRatio nodes E0 N0 i =
        N0.eval (nodes i) :=
      normalizedRatio_den_mul nodes E0 N0 hroot i
    _ = E0.eval (nodes i) * physicalW i := hphysical.symm

#print axioms normalizedRatio_den_mul
#print axioms cancel_factored_cross_at_nonroot
#print axioms zero_common_factor_counterexample
#print axioms normalized_ratio_and_physical_off_common_factor

end
end ProximityPrize.SubmissionLower.M69DataElevenPhysicalRatioBoundary6900
