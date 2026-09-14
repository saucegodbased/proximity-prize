import HrsGlobalSelectedErrorTestInterface6900
import K0LocatorErrorCRT6900
import K0RawRSConnectionTranspose6900
import Lean.Elab.Tactic.Omega

/-!
# Passive-Z ghost layer and the final three reverse-Hasse moments

This file isolates the part of the proposed passive-layer repair which is
actually formal before any global confluence assertion.

* Reverse-Hasse triangular closure does not require source equations at all
  47 coordinates when the consumer only uses the final three coordinates.
  The upward-closed tail `44 <= i < 47` closes on itself.
* One passive successor is a literal member of the target raw source throughout
  the large range `z <= 3692`.
* A grade-three agreement locator plus one error-value interpolant fits inside
  the tight `S*Y^48` window, hence also inside the adjacent critical windows.

The missing assertion is intentionally absent: the literal passive layer must
still produce the three aggregate equations at reverse-Hasse indices 44, 45,
and 46 after quotienting by the old contact image.  The Ward identity alone
does not prove that relative connecting map is onto.
-/

namespace ProximityPrize.SubmissionLower.K0PassiveGhostThreeMoment6900

open scoped BigOperators
open Polynomial
open HrsU0PoleCancellation6900
open HrsGlobalSelectedErrorTestInterface6900
open K0RawRSConnectionTranspose6900

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

variable {K I : Type*} [Field K] [Fintype I]

/-- Reverse-Hasse product-rule closure on an arbitrary upward-closed tail.
Only multiplier equations in that tail are used.  This is the restricted
version of the all-coordinate closure needed when a boundary cokernel exposes
only its final few Hasse moments. -/
theorem upperTail_reversedMoments_eq_zero_of_multiplier_equations
    (nodes : I → K) (depth w base : Nat) (g : I → K[X])
    (hsource : ∀ i, base ≤ i → i < depth → ∀ V : K[X],
      V.natDegree < w →
        (∑ x, reversedHasse (nodes x) depth (V * g x) i) = 0) :
    ∀ i, base ≤ i → i < depth → ∀ V : K[X], V.natDegree < w →
      reversedMoment nodes depth i g V = 0 := by
  intro i hbase hi
  let gap := depth - 1 - i
  have hmain : ∀ gap' i', gap' = depth - 1 - i' → base ≤ i' →
      i' < depth → ∀ V : K[X], V.natDegree < w →
        reversedMoment nodes depth i' g V = 0 := by
    intro gap'
    induction gap' using Nat.strong_induction_on with
    | h gap' ih =>
      intro i' hgap hbase' hi' V hV
      have hproduct := aggregate_multiplier_eq_diagonal_plus_earlier_moments
        nodes depth V g i'
      have hzero := hsource i' hbase' hi' V hV
      have htail :
          (∑ j ∈ Finset.range (depth - 1 - i'),
            reversedMoment nodes depth (i' + j + 1) g
              (Polynomial.hasseDeriv (j + 1) V)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjlt : j < depth - 1 - i' := by simpa using hj
        have hindices := reversedHasseUpperTail_indices hi' hj
        apply ih (depth - 1 - (i' + j + 1))
        · omega
        · rfl
        · omega
        · exact hindices.2
        · exact hasseDerivative_preserves_strict_source_window
            V w (j + 1) hV
      rw [hzero, htail, add_zero] at hproduct
      exact hproduct.symm
  exact hmain gap i rfl hbase hi

/-- At depth 47 the tail beginning at 44 consists of exactly three
reverse-Hasse coordinates.  Thus three source-equation families suffice to
kill all product-rule diagonal moments used by that tail. -/
theorem depth47_lastThree_reversedMoments_eq_zero
    (nodes : I → K) (w : Nat) (g : I → K[X])
    (hsource : ∀ i, 44 ≤ i → i < 47 → ∀ V : K[X],
      V.natDegree < w →
        (∑ x, reversedHasse (nodes x) 47 (V * g x) i) = 0) :
    ∀ i, 44 ≤ i → i < 47 → ∀ V : K[X], V.natDegree < w →
      reversedMoment nodes 47 i g V = 0 := by
  exact upperTail_reversedMoments_eq_zero_of_multiplier_equations
    nodes 47 w 44 g hsource

/-- A simple selected-node locator localizes any of the final three
coordinates once the same three aggregate multiplier equations are supplied.
No equations at indices `0,...,43` occur in the hypotheses. -/
theorem depth47_lastThree_selected_sum_eq_zero
    [DecidableEq I]
    (nodes : I → K) (w : Nat) (U : K[X]) (g : I → K[X])
    (i : Nat) (hi0 : 44 ≤ i) (hi1 : i < 47) (S : Finset I)
    (hU : U.natDegree < w)
    (hsource : ∀ k, 44 ≤ k → k < 47 → ∀ V : K[X],
      V.natDegree < w →
        (∑ x, reversedHasse (nodes x) 47 (V * g x) k) = 0)
    (hroot : ∀ x, x ∉ S → U.eval (nodes x) = 0) :
    (∑ x ∈ S,
      U.eval (nodes x) * reversedHasse (nodes x) 47 (g x) i) = 0 := by
  have hlocal := aggregate_multiplier_localizes_after_descending_moment_IH
    nodes 47 U g i S (by
      intro j hj
      have hindices := reversedHasseUpperTail_indices hi1 hj
      apply depth47_lastThree_reversedMoments_eq_zero
        nodes w g hsource (i + j + 1)
      · omega
      · exact hindices.2
      · exact hasseDerivative_preserves_strict_source_window
          U w (j + 1) hU) hroot
  rw [hsource i hi0 hi1 U hU] at hlocal
  exact hlocal.symm

/-! ## Literal target source and degree receipts -/

/-- In the literal `(m,L,B,s,U)=(47,3757,16,8,64)` raw source, every legal
shape with `z <= 3692` has its one-step passive successor in the source as
well.  The weighted X cutoff is unchanged by this successor. -/
theorem target_rawShapeLegal_passive_succ
    (a s y r z : Nat) (hz : z ≤ 3692)
    (hlegal : rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r z) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r (z + 1) := by
  unfold rawShapeLegal at hlegal ⊢
  omega

/-- Three locator grades plus one arbitrary error-value interpolant fit in
the tightest adjacent critical window `S*Y^48`.  The same certificate
therefore fits the wider `S*Y^47` and `S*Y^46*R` windows. -/
theorem target_locatorGrade3_errorValues_fit_critical_windows :
    3 * 180413 + 81731 <
        47 * 180413 - 48 * 131071 - 131069 ∧
      3 * 180413 + 81731 <
        47 * 180413 - 47 * 131071 - 131069 ∧
      3 * 180413 + 81731 <
        47 * 180413 - 46 * 131071 - 131070 - 131069 := by
  norm_num

#print axioms upperTail_reversedMoments_eq_zero_of_multiplier_equations
#print axioms depth47_lastThree_reversedMoments_eq_zero
#print axioms depth47_lastThree_selected_sum_eq_zero
#print axioms target_rawShapeLegal_passive_succ
#print axioms target_locatorGrade3_errorValues_fit_critical_windows

end

end ProximityPrize.SubmissionLower.K0PassiveGhostThreeMoment6900
