import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rank-adaptive dual interface for the exact-G k=0 route

The raw bordered-minor probes choose a basis of the contact image.  That
basis is not stable when more error nodes or later Newton coefficients are
introduced.  The intrinsic statement does not need a basis: failure of the
boundary map on the complete contact kernel is equivalent to a nonzero
boundary covector whose pullback is a contact row.

This file records that equivalence.  It is source-agnostic and deliberately
does not assert the missing m47 contact/partial-locator recurrence.
-/

namespace ProximityPrize.SubmissionLower.K0RankAdaptiveDual6900

noncomputable section

set_option autoImplicit false

variable {K Source Contact Boundary : Type*}
  [Field K]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Contact] [Module K Contact]
  [AddCommGroup Boundary] [Module K Boundary]

/-- The boundary map after imposing every contact equation. -/
def normalOnContactKernel
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary) :
    LinearMap.ker contact →ₗ[K] Boundary :=
  boundary.domRestrict (LinearMap.ker contact)

/-- A rank-adaptive replacement for fixed bordered minors.

The normal map is not onto exactly when there is a nonzero boundary covector
`lambda` and a contact covector `mu` with

`boundaryᵀ lambda = contactᵀ mu`.

No contact rank, pivot rows, basis, or finite-dimensional hypothesis appears
in the statement. -/
theorem not_surjective_normal_iff_exists_compatible_dual
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary) :
    ¬ Function.Surjective (normalOnContactKernel contact boundary) ↔
      ∃ lambda : Module.Dual K Boundary,
        lambda ≠ 0 ∧ boundary.dualMap lambda ∈ LinearMap.range contact.dualMap := by
  constructor
  · intro hnot
    have hrange : LinearMap.range (normalOnContactKernel contact boundary) < ⊤ := by
      rw [lt_top_iff_ne_top, ne_eq, LinearMap.range_eq_top]
      exact hnot
    obtain ⟨lambda, hlambda, hann⟩ :=
      (LinearMap.range (normalOnContactKernel contact boundary)).exists_le_ker_of_lt_top
        hrange
    refine ⟨lambda, hlambda, ?_⟩
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      Submodule.mem_dualAnnihilator]
    intro source hsource
    have himage :
        (normalOnContactKernel contact boundary) ⟨source, hsource⟩ ∈
          LinearMap.range (normalOnContactKernel contact boundary) :=
      ⟨⟨source, hsource⟩, rfl⟩
    have hzero := LinearMap.mem_ker.mp (hann himage)
    simpa [normalOnContactKernel, LinearMap.dualMap_apply] using hzero
  · rintro ⟨lambda, hlambda, ⟨mu, hcompat⟩⟩ hsurj
    apply hlambda
    ext boundaryValue
    obtain ⟨source, hsource⟩ := hsurj boundaryValue
    have hpoint := LinearMap.congr_fun hcompat source.1
    have hcontact : contact source.1 = 0 := source.2
    change mu (contact source.1) = lambda (boundary source.1) at hpoint
    have hlambdaImage : lambda (boundary source.1) = 0 := by
      simpa [hcontact] using hpoint.symm
    simpa [normalOnContactKernel] using hsource ▸ hlambdaImage

/-- Equivalent positive formulation: complete conormal rank is full exactly
when every boundary covector which is also a contact row is zero.  This is the
form the literal partial-locator/Hasse theorem should target. -/
theorem normal_surjective_iff_compatible_dual_zero
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary) :
    Function.Surjective (normalOnContactKernel contact boundary) ↔
      ∀ lambda : Module.Dual K Boundary,
        boundary.dualMap lambda ∈ LinearMap.range contact.dualMap → lambda = 0 := by
  constructor
  · intro hsurj lambda hcompatible
    by_contra hlambda
    exact
      (not_surjective_normal_iff_exists_compatible_dual contact boundary).mpr
        ⟨lambda, hlambda, hcompatible⟩ hsurj
  · intro hzero
    by_contra hnot
    obtain ⟨lambda, hlambda, hcompatible⟩ :=
      (not_surjective_normal_iff_exists_compatible_dual contact boundary).mp hnot
    exact hlambda (hzero lambda hcompatible)

/-! ## An adversarial constant-ratio family for two adjacent anchor charts -/

/-- If two anchor interpolants differ by `c * locatorShared`, changing the
anchor does not force the passive mismatch ratio `-delta/epsilon` to vary
among error nodes.  Pointwise substitute `locatorShared(x)` for `ell` below.
The constructed residual and two mismatches obey the anchor-change equation,
while the two ratios are the independently prescribed constants `rho0` and
`rho1`.

Thus a two-anchor proof may exploit the changed locator prefactors, but may
not claim that the passive-seed powers automatically form a Vandermonde
system after the swap. -/
theorem adjacent_anchor_swap_preserves_constant_ratio_family
    (c ell rho0 rho1 : K)
    (hc : c ≠ 0) (hell : ell ≠ 0)
    (hrho0 : rho0 ≠ 0) (hrho1 : rho1 ≠ 0)
    (hne : rho0 ≠ rho1) :
    let delta := c * ell * rho0 * rho1 / (rho0 - rho1)
    let epsilon0 := -(c * ell * rho1) / (rho0 - rho1)
    let epsilon1 := -(c * ell * rho0) / (rho0 - rho1)
    delta ≠ 0 ∧ epsilon0 ≠ 0 ∧ epsilon1 ≠ 0 ∧
      epsilon0 - epsilon1 = c * ell ∧
      -delta / epsilon0 = rho0 ∧ -delta / epsilon1 = rho1 := by
  dsimp only
  have hdiff : rho0 - rho1 ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hc hell) hrho0) hrho1) hdiff
  constructor
  · exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hc hell) hrho1))
      hdiff
  constructor
  · exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hc hell) hrho0))
      hdiff
  constructor
  · field_simp
    ring
  constructor <;> field_simp

#print axioms not_surjective_normal_iff_exists_compatible_dual
#print axioms normal_surjective_iff_compatible_dual_zero
#print axioms adjacent_anchor_swap_preserves_constant_ratio_family

end

end ProximityPrize.SubmissionLower.K0RankAdaptiveDual6900
