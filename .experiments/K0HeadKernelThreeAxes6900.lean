import K0SRTinyContactCore6900
import K0TerminalDualDetection6900
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Three free boundary axes in the high-epsilon head kernel

When the old cap contact is projected to ordinary outer orders at least three,
the literal raw monomials `S`, `R`, and `Z` are automatically in its kernel:
their contact columns have epsilon order zero.  Their boundary gradients are
the three coordinate axes `e_S,e_R,e_Z`.  Thus the target head-kernel boundary
problem is only one-dimensional: it remains to construct a kernel vector with
nonzero `Y` boundary coordinate.

The pure `Y` column displays the obstruction exactly.  Its only term of outer
order at least three is `epsilon^3*T`.  A target recurrence/HRS producer must
cancel this channel while retaining a nonzero `Y` boundary derivative.
-/

namespace ProximityPrize.SubmissionLower.K0HeadKernelThreeAxes6900

open K0SRTinyContactCore6900
open K0TerminalDualDetection6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K V : Type*} [Field K]
  [AddCommGroup V] [Module K V]

/-! ## Literal contact and boundary identities -/

theorem pureS_contact (x u0 u1 : K) :
    rawContactColumn x u0 u1 0 1 0 0 0 = localS := by
  simp [rawContactColumn]

theorem pureR_contact (x u0 u1 : K) :
    rawContactColumn x u0 u1 0 0 0 1 0 = localR := by
  simp [rawContactColumn]

theorem pureZ_contact (x u0 u1 : K) :
    rawContactColumn x u0 u1 0 0 0 0 1 = localZ := by
  simp [rawContactColumn]

theorem pureY_contact_high_obstruction (x u0 u1 : K) :
    rawContactColumn x u0 u1 0 0 1 0 0 - eps ^ 3 * localT =
      MvPolynomial.C u0 + MvPolynomial.C u1 * localZ +
        eps * localR - eps ^ 2 * localS := by
  simp only [rawContactColumn, pow_zero, one_mul, mul_one, contactedY]
  ring

theorem pureS_boundary
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma
      lambdaS lambdaY lambdaR lambdaZ 1 0 0 0 = lambdaS := by
  simp [rawBoundaryScalar]

theorem pureR_boundary
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma
      lambdaS lambdaY lambdaR lambdaZ 0 0 1 0 = lambdaR := by
  simp [rawBoundaryScalar]

theorem pureZ_boundary
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma
      lambdaS lambdaY lambdaR lambdaZ 0 0 0 1 = lambdaZ := by
  simp [rawBoundaryScalar]

theorem pureY_boundary
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma
      lambdaS lambdaY lambdaR lambdaZ 0 1 0 0 = lambdaY := by
  simp [rawBoundaryScalar]

/-- All four pure coordinates are source-legal already at target cap 3756;
the first three are the automatic high-head-kernel axes. -/
theorem target_oldCap_pure_axes_legal :
    rawShapeLegal (47 * 180413) 131071 3756 16 8 64 0 1 0 0 0 ∧
    rawShapeLegal (47 * 180413) 131071 3756 16 8 64 0 0 0 1 0 ∧
    rawShapeLegal (47 * 180413) 131071 3756 16 8 64 0 0 0 0 1 ∧
    rawShapeLegal (47 * 180413) 131071 3756 16 8 64 0 0 1 0 0 := by
  norm_num [rawShapeLegal]

/-- All-node interpolation in the direct `Lambda_G^46` witness misses the
strict X cutoff by exactly `e-1`.  Agreement interpolation fits, but does not
cancel the error-node head contact. -/
theorem target_direct_Y_allNode_interpolation_overrun :
    46 * 180413 + 262144 - 1 = 47 * 180413 + 81730 ∧
      262144 - 180413 - 1 = 81730 ∧
      46 * 180413 + 131071 + 49342 = 47 * 180413 ∧
      90867 - (262144 - 180413) = 9136 := by
  norm_num

/-! ## Rank-four reduction to one scalar witness -/

def boundaryVector (s y r z : K) : Fin 4 → K := ![s, y, r, z]

/-- Once `S,R,Z` are available in the domain of the map under consideration,
any vector with nonzero `Y` coordinate completes its boundary map to a
surjection.  Below this is applied specifically to the boundary map whose
domain is the *head-projected* contact kernel, not the full contact kernel. -/
theorem surjective_of_three_axes_and_nonzero_Y
    (normal : V →ₗ[K] (Fin 4 → K)) (vS vR vZ vY : V)
    (hS : normal vS = boundaryVector 1 0 0 0)
    (hR : normal vR = boundaryVector 0 0 1 0)
    (hZ : normal vZ = boundaryVector 0 0 0 1)
    (hY : normal vY 1 ≠ 0) :
    Function.Surjective normal := by
  intro b
  let c : K := b 1 / normal vY 1
  let v : V := c • vY +
    (b 0 - c * normal vY 0) • vS +
    (b 2 - c * normal vY 2) • vR +
    (b 3 - c * normal vY 3) • vZ
  refine ⟨v, ?_⟩
  funext i
  simp only [v, map_add, map_smul]
  change c * normal vY i +
      (b 0 - c * normal vY 0) * normal vS i +
      (b 2 - c * normal vY 2) * normal vR i +
      (b 3 - c * normal vY 3) * normal vZ i = b i
  rw [hS, hR, hZ]
  fin_cases i
  · simp [boundaryVector]
  · simpa [boundaryVector, c] using div_mul_cancel₀ (b 1) hY
  · simp [boundaryVector]
  · simp [boundaryVector]

/-- Composition-safe head-kernel statement.  The four source vectors are
required to lie in `ker headContact`; no claim is made that they lie in the
full contact kernel.  A separate terminal correction/dual-detection theorem
is still needed to return from this projected kernel to complete contact. -/
theorem headKernelBoundary_surjective_of_three_axes_and_nonzero_Y
    {Source Head : Type*}
    [AddCommGroup Source] [Module K Source]
    [AddCommGroup Head] [Module K Head]
    (headContact : Source →ₗ[K] Head)
    (boundary : Source →ₗ[K] (Fin 4 → K))
    (vS vR vZ vY : Source)
    (hSker : headContact vS = 0)
    (hRker : headContact vR = 0)
    (hZker : headContact vZ = 0)
    (hYker : headContact vY = 0)
    (hS : boundary vS = boundaryVector 1 0 0 0)
    (hR : boundary vR = boundaryVector 0 0 1 0)
    (hZ : boundary vZ = boundaryVector 0 0 0 1)
    (hY : boundary vY 1 ≠ 0) :
    Function.Surjective
      (boundary.domRestrict (LinearMap.ker headContact)) := by
  let s : LinearMap.ker headContact :=
    ⟨vS, LinearMap.mem_ker.mpr hSker⟩
  let r : LinearMap.ker headContact :=
    ⟨vR, LinearMap.mem_ker.mpr hRker⟩
  let z : LinearMap.ker headContact :=
    ⟨vZ, LinearMap.mem_ker.mpr hZker⟩
  let y : LinearMap.ker headContact :=
    ⟨vY, LinearMap.mem_ker.mpr hYker⟩
  apply surjective_of_three_axes_and_nonzero_Y
    (boundary.domRestrict (LinearMap.ker headContact)) s r z y
  · exact hS
  · exact hR
  · exact hZ
  · exact hY

/-- Auditable end-to-end dual consumer.  The axes and one nonzero-Y witness
live only in the head-projected kernel.  Their head-boundary surjectivity is
then passed to the quotient-aware terminal theorem: a *complete* compatible
dual whose terminal component vanishes has zero boundary covector. -/
theorem fullCompatibleDual_boundary_eq_zero_of_axes_Y_and_terminal_zero
    {Source Head Tail : Type*}
    [AddCommGroup Source] [Module K Source]
    [AddCommGroup Head] [Module K Head]
    [AddCommGroup Tail] [Module K Tail]
    (headContact : Source →ₗ[K] Head)
    (tailContact : Source →ₗ[K] Tail)
    (boundary : Source →ₗ[K] (Fin 4 → K))
    (vS vR vZ vY : Source)
    (hSker : headContact vS = 0)
    (hRker : headContact vR = 0)
    (hZker : headContact vZ = 0)
    (hYker : headContact vY = 0)
    (hS : boundary vS = boundaryVector 1 0 0 0)
    (hR : boundary vR = boundaryVector 0 0 1 0)
    (hZ : boundary vZ = boundaryVector 0 0 0 1)
    (hY : boundary vY 1 ≠ 0)
    (ell : Module.Dual K (Fin 4 → K))
    (etaHead : Module.Dual K Head) (etaTail : Module.Dual K Tail)
    (hcompatible : boundary.dualMap ell =
      headContact.dualMap etaHead + tailContact.dualMap etaTail)
    (hterminal : etaTail = 0) :
    ell = 0 := by
  apply boundaryDual_eq_zero_of_terminal_eq_zero
    headContact tailContact boundary _ ell etaHead etaTail
      hcompatible hterminal
  exact headKernelBoundary_surjective_of_three_axes_and_nonzero_Y
    headContact boundary vS vR vZ vY
      hSker hRker hZker hYker hS hR hZ hY

#print axioms pureS_contact
#print axioms pureR_contact
#print axioms pureZ_contact
#print axioms pureY_contact_high_obstruction
#print axioms pureS_boundary
#print axioms pureR_boundary
#print axioms pureZ_boundary
#print axioms pureY_boundary
#print axioms target_oldCap_pure_axes_legal
#print axioms target_direct_Y_allNode_interpolation_overrun
#print axioms surjective_of_three_axes_and_nonzero_Y
#print axioms headKernelBoundary_surjective_of_three_axes_and_nonzero_Y
#print axioms fullCompatibleDual_boundary_eq_zero_of_axes_Y_and_terminal_zero

end
end ProximityPrize.SubmissionLower.K0HeadKernelThreeAxes6900
