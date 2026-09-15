import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Terminal-coordinate detection for compatible contact duals

This is the abstract implication used by the exact m8 last-three receipt.
Split the complete contact target into head and terminal coordinates.  If the
boundary map on the kernel of the head contact map is already surjective,
then no nonzero compatible boundary dual can have zero terminal component.

The statement deliberately concerns restriction of a *complete* compatible
dual.  It does not replace the complete contact map by its terminal rows.
-/

namespace ProximityPrize.SubmissionLower.K0TerminalDualDetection6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

variable {K Source Head Tail Boundary : Type*}
  [Field K]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Head] [Module K Head]
  [AddCommGroup Tail] [Module K Tail]
  [AddCommGroup Boundary] [Module K Boundary]

/-- If the head-contact kernel already realizes every boundary vector, a
compatible adjoint pair whose terminal dual coordinate is zero has zero
boundary covector.  This is the basis-free kernel test behind the quotient-
aware last-three detector. -/
theorem boundaryDual_eq_zero_of_terminal_eq_zero
    (head : Source →ₗ[K] Head) (tail : Source →ₗ[K] Tail)
    (boundary : Source →ₗ[K] Boundary)
    (hsurj : Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)))
    (ell : Module.Dual K Boundary)
    (etaHead : Module.Dual K Head) (etaTail : Module.Dual K Tail)
    (hcompatible : boundary.dualMap ell =
      head.dualMap etaHead + tail.dualMap etaTail)
    (hterminal : etaTail = 0) :
    ell = 0 := by
  apply LinearMap.ext
  intro b
  obtain ⟨v, hv⟩ := hsurj b
  have hpoint := LinearMap.congr_fun hcompatible v.1
  change ell (boundary v.1) =
    etaHead (head v.1) + etaTail (tail v.1) at hpoint
  change boundary v.1 = b at hv
  rw [hv, v.2, hterminal] at hpoint
  simpa using hpoint

/-- Quotient-aware form.  If the difference of two compatible terminal
components is the terminal part of a pure contact annihilator, then their
boundary covectors agree.  This says that terminal restriction modulo pure
contact annihilators is injective on compatible boundary-dual classes. -/
theorem boundaryDual_eq_of_terminal_diff_is_pure
    (head : Source →ₗ[K] Head) (tail : Source →ₗ[K] Tail)
    (boundary : Source →ₗ[K] Boundary)
    (hsurj : Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)))
    (ell₁ ell₂ : Module.Dual K Boundary)
    (etaHead₁ etaHead₂ : Module.Dual K Head)
    (etaTail₁ etaTail₂ : Module.Dual K Tail)
    (hcompatible₁ : boundary.dualMap ell₁ =
      head.dualMap etaHead₁ + tail.dualMap etaTail₁)
    (hcompatible₂ : boundary.dualMap ell₂ =
      head.dualMap etaHead₂ + tail.dualMap etaTail₂)
    (pureHead : Module.Dual K Head) (pureTail : Module.Dual K Tail)
    (hpure : head.dualMap pureHead + tail.dualMap pureTail = 0)
    (hterminal : etaTail₁ - etaTail₂ = pureTail) :
    ell₁ = ell₂ := by
  have hcompatibleDiff :
      boundary.dualMap (ell₁ - ell₂) =
        head.dualMap (etaHead₁ - etaHead₂ - pureHead) +
          tail.dualMap (etaTail₁ - etaTail₂ - pureTail) := by
    apply LinearMap.ext
    intro v
    have h₁ := LinearMap.congr_fun hcompatible₁ v
    have h₂ := LinearMap.congr_fun hcompatible₂ v
    have h₀ := LinearMap.congr_fun hpure v
    change ell₁ (boundary v) =
      etaHead₁ (head v) + etaTail₁ (tail v) at h₁
    change ell₂ (boundary v) =
      etaHead₂ (head v) + etaTail₂ (tail v) at h₂
    change pureHead (head v) + pureTail (tail v) = 0 at h₀
    change ell₁ (boundary v) - ell₂ (boundary v) =
      (etaHead₁ (head v) - etaHead₂ (head v) - pureHead (head v)) +
        (etaTail₁ (tail v) - etaTail₂ (tail v) - pureTail (tail v))
    rw [h₁, h₂]
    linear_combination h₀
  have hzero : etaTail₁ - etaTail₂ - pureTail = 0 := by
    rw [hterminal]
    exact sub_self pureTail
  have hell : ell₁ - ell₂ = 0 :=
    boundaryDual_eq_zero_of_terminal_eq_zero
      head tail boundary hsurj (ell₁ - ell₂)
        (etaHead₁ - etaHead₂ - pureHead)
        (etaTail₁ - etaTail₂ - pureTail) hcompatibleDiff hzero
  exact sub_eq_zero.mp hell

/-! ## Literal target arithmetic (dimension-only) -/

/-- Removing ordinary outer orders `0,1,2` from the published local-rank
bound leaves the stated head-`>=3` allowance, and the cap-3756 source has a
large positive dimension margin against that reduced allowance.  This is
only arithmetic; it does not assert that the projected target contact kernel
has boundary rank four. -/
theorem target_head_ge_three_dimension_margin :
    303669 + 607257 + 910764 = 1821690 ∧
      248124600 - 1821690 = 246302910 ∧
      65044354424601 - 262144 * 246302910 = 477524385561 := by
  norm_num

/-- One further passive layer raises the literal target ledger margin by
`23,088,879`, from `2,371,080` at `L=3757` to `25,459,959` at `L=3758`.
Again this is source/rank-bound arithmetic, not the relative producer. -/
theorem target_L3758_margin_receipt :
    65079223811319 - 262144 * 248257440 = 25459959 ∧
      25459959 - 2371080 = 23088879 := by
  norm_num

#print axioms boundaryDual_eq_zero_of_terminal_eq_zero
#print axioms boundaryDual_eq_of_terminal_diff_is_pure
#print axioms target_head_ge_three_dimension_margin
#print axioms target_L3758_margin_receipt

end

end ProximityPrize.SubmissionLower.K0TerminalDualDetection6900
