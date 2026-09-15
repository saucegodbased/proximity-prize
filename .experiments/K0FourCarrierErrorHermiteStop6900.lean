import HrsCrtPairingBridge6900
import Mathlib.Tactic.NormNum

/-!
# Error-Hermite stop for a fixed four-carrier coefficient space

Once the epsilon-zero carrier matrix is invertible at every error, vanishing
of 44 output coefficients forces the 44-jet of every carrier coefficient to
vanish at every error.  This file records the resulting target degree stop.
-/

namespace ProximityPrize.SubmissionLower.K0FourCarrierErrorHermiteStop6900

open Polynomial
open HrsCrtPairingBridge6900 HrsU0PoleCancellation6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

variable {K E : Type*} [Field K] [Fintype E]

/-- Formal recurrence step used in the fixed-carrier STOP.  If every output
coefficient has an injective common leading block on the same-order carrier
jets, while all remaining terms depend only on earlier jets, zero output
forces every jet to vanish. -/
theorem jets_zero_of_injective_leading_recurrence
    {V : Type*} [AddCommGroup V] [Module K V]
    (m : Nat) (lead : V →ₗ[K] V) (hlead : Function.Injective lead)
    (jet tail : Nat → V)
    (htail : ∀ r, (∀ j, j < r → jet j = 0) → tail r = 0)
    (hequation : ∀ r, r < m → lead (jet r) + tail r = 0) :
    ∀ r, r < m → jet r = 0 := by
  intro r hr
  induction r using Nat.strong_induction_on with
  | h r ih =>
      have htailZero : tail r = 0 := by
        apply htail r
        intro j hj
        exact ih j hj (by omega)
      have hleadZero : lead (jet r) = 0 := by
        have h := hequation r hr
        simpa [htailZero] using h
      apply hlead
      simpa using hleadZero

/-- A polynomial below the largest of the four target coefficient windows
cannot have a zero depth-44 Hasse jet at all 81,731 distinct error nodes
unless it is zero. -/
theorem eq_zero_of_target_window_and_all_error_44jets
    (nodes : E → K) (hnodes : Function.Injective nodes)
    (hcard : Fintype.card E = 81731)
    (V : K[X]) (hdegree : V.natDegree < 590584)
    (hjets : ∀ i : E, ∀ j < 44, hasseAt (nodes i) V j = 0) :
    V = 0 := by
  let depth : E → Nat := fun _ ↦ 44
  have htotal : totalDepth depth = 44 * 81731 := by
    simp [totalDepth, depth, hcard]
  by_cases hV : V = 0
  · exact hV
  have hdegreeTotal : V.natDegree < totalDepth depth := by
    rw [htotal]
    omega
  let p : Polynomial.degreeLT K (totalDepth depth) :=
    ⟨V, Polynomial.mem_degreeLT.mpr
      ((Polynomial.natDegree_lt_iff_degree_lt hV).mp hdegreeTotal)⟩
  have hpmap : hasseJetMap nodes depth p = 0 := by
    funext i j
    rw [hasseJetMap_apply]
    exact hjets i j.val j.isLt
  have hpzero : p = 0 := by
    apply hasseJetMap_injective nodes depth hnodes
    simpa using hpmap
  have hval := congrArg (fun q : Polynomial.degreeLT K (totalDepth depth) ↦ q.1)
    hpzero
  simpa [p] using hval

/-- The numerical obstruction is not close: the required error Hermite
degree is over six times the largest available carrier-coefficient window. -/
theorem target_fourCarrier_errorHermite_degree_stop :
    44 * 81731 = 3596164 ∧
      47 * 180413 - (43 * 180413 + 131069) = 590583 ∧
      590583 < 3596164 ∧
      47 * 180413 - 44 * 180413 = 541239 ∧
      541239 < 3596164 := by
  norm_num

#print axioms eq_zero_of_target_window_and_all_error_44jets
#print axioms jets_zero_of_injective_leading_recurrence
#print axioms target_fourCarrier_errorHermite_degree_stop

end

end ProximityPrize.SubmissionLower.K0FourCarrierErrorHermiteStop6900
