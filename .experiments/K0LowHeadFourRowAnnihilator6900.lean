import K0TerminalDualDetection6900

/-!
# A four-row annihilator certificate for the K0 low head

The target terminal argument does not need a complete extra-node CRT.  It
only needs the four boundary rows to be independent modulo the old low-head
contact rows.  This file packages a still smaller sufficient certificate:
an operator on source duals which kills every old contact row and is
injective on the four-dimensional boundary-row space.

The intended target instance is a nodal/confluent recurrence operator.  Its
old-node characteristic polynomial kills the old contact distributions, and
the four boundary rows give a four-by-four defect matrix at a fresh point.
Only that defect matrix has to be nonsingular.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadFourRowAnnihilator6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K Source Head Boundary Defect : Type*}
  [Field K]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Head] [Module K Head]
  [AddCommGroup Boundary] [Module K Boundary]
  [AddCommGroup Defect] [Module K Defect]

open K0TerminalDualDetection6900

/-- The exact dual criterion: it is enough to rule out a nonzero boundary
covector whose pullback is an old low-head contact covector.  This asks about
four quotient rows, rather than an entire extra local contact block. -/
theorem kernelBoundary_surjective_of_dual_separation
    (head : Source →ₗ[K] Head)
    (boundary : Source →ₗ[K] Boundary)
    (hseparate : ∀ (ell : Module.Dual K Boundary)
        (eta : Module.Dual K Head),
      boundary.dualMap ell = head.dualMap eta → ell = 0) :
    Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro ell₁ ell₂ hell
  have hmem : boundary.dualMap (ell₁ - ell₂) ∈
      (LinearMap.ker head).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    have hpoint := LinearMap.congr_fun hell ⟨v, hv⟩
    change ell₁ (boundary v) = ell₂ (boundary v) at hpoint
    change ell₁ (boundary v) - ell₂ (boundary v) = 0
    exact sub_eq_zero.mpr hpoint
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨eta, heta⟩ := hmem
  have hzero := hseparate (ell₁ - ell₂) eta heta.symm
  exact sub_eq_zero.mp hzero

/-- Recurrence/annihilator form.  An operator `annihilator` may discard the
huge old row space.  If it kills the pullback of every old head covector and
remains injective on pullbacks of the four boundary covectors, the boundary
map on the old head kernel is onto.

For a concrete nodal recurrence, `Defect` can be only four-dimensional: the
map `annihilator.comp boundary.dualMap` is then the small terminal defect
matrix whose determinant must be nonzero. -/
theorem kernelBoundary_surjective_of_annihilator
    (head : Source →ₗ[K] Head)
    (boundary : Source →ₗ[K] Boundary)
    (annihilator : Module.Dual K Source →ₗ[K] Defect)
    (hkill : annihilator.comp head.dualMap = 0)
    (hboundary : Function.Injective
      (annihilator.comp boundary.dualMap)) :
    Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)) := by
  apply kernelBoundary_surjective_of_dual_separation head boundary
  intro ell eta heq
  apply hboundary
  have hkillEta := LinearMap.congr_fun hkill eta
  change annihilator (boundary.dualMap ell) =
    annihilator (boundary.dualMap 0)
  rw [heq]
  simpa using hkillEta

/-- A pointwise version is often easier to instantiate than equality of
linear maps: every old contact covector has zero defect, and zero defect of a
boundary covector forces that boundary covector to vanish. -/
theorem kernelBoundary_surjective_of_pointwise_defect
    (head : Source →ₗ[K] Head)
    (boundary : Source →ₗ[K] Boundary)
    (annihilator : Module.Dual K Source →ₗ[K] Defect)
    (hkill : ∀ eta : Module.Dual K Head,
      annihilator (head.dualMap eta) = 0)
    (hdetect : ∀ ell : Module.Dual K Boundary,
      annihilator (boundary.dualMap ell) = 0 → ell = 0) :
    Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)) := by
  apply kernelBoundary_surjective_of_dual_separation head boundary
  intro ell eta heq
  apply hdetect ell
  rw [heq]
  exact hkill eta

/-- A small explicit inverse of the boundary defect matrix is sufficient.
This avoids choosing a basis or mentioning a determinant in the abstract
consumer; a target proof may discharge `hleft` by four coefficient
identities. -/
theorem kernelBoundary_surjective_of_defect_leftInverse
    (head : Source →ₗ[K] Head)
    (boundary : Source →ₗ[K] Boundary)
    (annihilator : Module.Dual K Source →ₗ[K] Defect)
    (decode : Defect →ₗ[K] Module.Dual K Boundary)
    (hkill : annihilator.comp head.dualMap = 0)
    (hleft : decode.comp (annihilator.comp boundary.dualMap) =
      LinearMap.id) :
    Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)) := by
  apply kernelBoundary_surjective_of_annihilator
    head boundary annihilator hkill
  intro ell₁ ell₂ hell
  have hdecoded := congrArg decode hell
  have hleft₁ := LinearMap.congr_fun hleft ell₁
  have hleft₂ := LinearMap.congr_fun hleft ell₂
  change decode (annihilator (boundary.dualMap ell₁)) = ell₁ at hleft₁
  change decode (annihilator (boundary.dualMap ell₂)) = ell₂ at hleft₂
  exact hleft₁.symm.trans (hdecoded.trans hleft₂)

/-- End-to-end terminal consumer.  A four-dimensional recurrence defect
certificate for the low head supplies exactly the surjectivity hypothesis of
the quotient-aware last-three detector.  No full extra-node contact block
occurs in the statement. -/
theorem compatibleBoundaryDual_eq_zero_of_lowHead_annihilator
    {Tail : Type*} [AddCommGroup Tail] [Module K Tail]
    (head : Source →ₗ[K] Head)
    (tail : Source →ₗ[K] Tail)
    (boundary : Source →ₗ[K] Boundary)
    (annihilator : Module.Dual K Source →ₗ[K] Defect)
    (hkill : annihilator.comp head.dualMap = 0)
    (hboundary : Function.Injective
      (annihilator.comp boundary.dualMap))
    (ell : Module.Dual K Boundary)
    (etaHead : Module.Dual K Head)
    (etaTail : Module.Dual K Tail)
    (hcompatible : boundary.dualMap ell =
      head.dualMap etaHead + tail.dualMap etaTail)
    (hterminal : etaTail = 0) :
    ell = 0 := by
  apply boundaryDual_eq_zero_of_terminal_eq_zero
    head tail boundary _ ell etaHead etaTail hcompatible hterminal
  exact kernelBoundary_surjective_of_annihilator
    head boundary annihilator hkill hboundary

#print axioms kernelBoundary_surjective_of_dual_separation
#print axioms kernelBoundary_surjective_of_annihilator
#print axioms kernelBoundary_surjective_of_pointwise_defect
#print axioms kernelBoundary_surjective_of_defect_leftInverse
#print axioms compatibleBoundaryDual_eq_zero_of_lowHead_annihilator

end

end ProximityPrize.SubmissionLower.K0LowHeadFourRowAnnihilator6900
