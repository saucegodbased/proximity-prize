import K0AssociatedGradeStrictness6900

/-!
# The lower-grade obstruction carried by a top-face relation

This packages the precise obstruction left after the target-native associated
top-face count.  A vector in `ker top` gives a genuine old-correctable contact
relation exactly when its lower component vanishes in the quotient by the old
contact image.

Consequently a `q`-dimensional top-symbol kernel contains at least
`q - dim (Wlo / range old)` genuinely liftable relations.  The numerical
`23,088,879` lower bound therefore does **not** by itself prove liftability:
an upper bound on this lower-grade cokernel (or a strictness theorem) remains
an explicit open premise.
-/

namespace ProximityPrize.SubmissionLower.K0FullFaceFilteredObstruction6900

open K0RelativeAttachmentExactSequence6900
open K0AssociatedGradeStrictness6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K P F Wlo Whi : Type*}
  [Field K]
  [AddCommGroup P] [Module K P]
  [AddCommGroup F] [Module K F]
  [AddCommGroup Wlo] [Module K Wlo]
  [AddCommGroup Whi] [Module K Whi]

/-- The connecting obstruction from an associated top-face relation to the
lower contact cokernel. -/
def lowerGradeObstruction
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi) :
    LinearMap.ker top →ₗ[K] (Wlo ⧸ LinearMap.range old) :=
  (LinearMap.range old).mkQ.comp (lower.domRestrict (LinearMap.ker top))

theorem lowerGradeObstruction_apply
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (v : LinearMap.ker top) :
    lowerGradeObstruction old lower top v =
      (LinearMap.range old).mkQ (lower v.1) := by
  rfl

/-- The obstruction vanishes precisely on associated relations whose lower
remainder is supplied by the preceding cap. -/
theorem mem_ker_lowerGradeObstruction_iff
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (v : LinearMap.ker top) :
    v ∈ LinearMap.ker (lowerGradeObstruction old lower top) ↔
      lower v.1 ∈ LinearMap.range old := by
  rw [LinearMap.mem_ker, lowerGradeObstruction_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- Equivalently, the obstruction kernel is exactly the true relative domain
inside the associated top-symbol kernel. -/
theorem mem_ker_lowerGradeObstruction_iff_liftable
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (v : LinearMap.ker top) :
    v ∈ LinearMap.ker (lowerGradeObstruction old lower top) ↔
      v.1 ∈ liftableFace (filteredOldContact old)
        (filteredFaceContact lower top) := by
  rw [mem_ker_lowerGradeObstruction_iff,
    mem_liftableFace_filtered_iff]
  constructor
  · exact fun hlower ↦ ⟨LinearMap.mem_ker.mp v.2, hlower⟩
  · exact fun h ↦ h.2

/-- Rank-nullity gives the sharp dimension-only loss: at most the dimension
of the lower-grade cokernel can be consumed by the obstruction. -/
theorem finrank_obstruction_kernel_lower_bound
    [FiniteDimensional K F] [FiniteDimensional K Wlo]
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (q : ℕ) (hkernel : q ≤ Module.finrank K (LinearMap.ker top)) :
    q - Module.finrank K (Wlo ⧸ LinearMap.range old) ≤
      Module.finrank K (LinearMap.ker (lowerGradeObstruction old lower top)) := by
  let obs := lowerGradeObstruction old lower top
  have hsum := obs.finrank_range_add_finrank_ker
  have hrange : Module.finrank K obs.range ≤
      Module.finrank K (Wlo ⧸ LinearMap.range old) :=
    Submodule.finrank_le obs.range
  change q - Module.finrank K (Wlo ⧸ LinearMap.range old) ≤
    Module.finrank K (LinearMap.ker obs)
  rw [Nat.sub_le_iff_le_add']
  omega

/-- Target specialization of the preceding theorem.  This is intentionally a
conditional bridge, not a claim that the lower-grade cokernel is small. -/
theorem target_23088879_liftable_lower_bound
    [FiniteDimensional K F] [FiniteDimensional K Wlo]
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (hkernel : 23088879 ≤ Module.finrank K (LinearMap.ker top)) :
    23088879 - Module.finrank K (Wlo ⧸ LinearMap.range old) ≤
      Module.finrank K (LinearMap.ker (lowerGradeObstruction old lower top)) :=
  finrank_obstruction_kernel_lower_bound old lower top 23088879 hkernel

/-- Strictness is exactly the statement that the obstruction map is zero. -/
theorem strictAtFace_iff_lowerGradeObstruction_eq_zero
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi) :
    StrictAtFace old lower top ↔ lowerGradeObstruction old lower top = 0 := by
  constructor
  · intro hstrict
    ext v
    rw [LinearMap.zero_apply, lowerGradeObstruction_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hstrict v.1 (LinearMap.mem_ker.mp v.2)
  · intro hzero f htop
    let v : LinearMap.ker top := ⟨f, LinearMap.mem_ker.mpr htop⟩
    have hv : v ∈ LinearMap.ker (lowerGradeObstruction old lower top) := by
      rw [LinearMap.mem_ker, hzero, LinearMap.zero_apply]
    exact (mem_ker_lowerGradeObstruction_iff old lower top v).mp hv

#print axioms mem_ker_lowerGradeObstruction_iff_liftable
#print axioms finrank_obstruction_kernel_lower_bound
#print axioms target_23088879_liftable_lower_bound
#print axioms strictAtFace_iff_lowerGradeObstruction_eq_zero

end
end ProximityPrize.SubmissionLower.K0FullFaceFilteredObstruction6900
