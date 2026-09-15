import K0FullFaceFilteredObstruction6900

/-!
# A single filtered class carrying lift obstruction and relative boundary

For a top-symbol relation `v`, the pair `(lower v, faceBoundary v)` is
well-defined modulo the joint old contact/boundary image.  Its projection to
`Wlo / range oldContact` is exactly the lower-grade lift obstruction.  On the
kernel of that projection, the remaining class is the correction-independent
relative boundary (modulo boundaries of old contact-kernel vectors).

This is the mapping-cone object suggested by the target audit.  It does not
assert that its projection factors through error-supported rows; that is the
next literal-contact premise being tested separately.
-/

namespace ProximityPrize.SubmissionLower.K0FullFaceCombinedConnecting6900

open K0FullFaceFilteredObstruction6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K P F Wlo Whi B E : Type*}
  [Field K]
  [AddCommGroup P] [Module K P]
  [AddCommGroup F] [Module K F]
  [AddCommGroup Wlo] [Module K Wlo]
  [AddCommGroup Whi] [Module K Whi]
  [AddCommGroup B] [Module K B]
  [AddCommGroup E] [Module K E]

def oldJoint
    (old : P →ₗ[K] Wlo) (oldBoundary : P →ₗ[K] B) :
    P →ₗ[K] Wlo × B where
  toFun p := (old p, oldBoundary p)
  map_add' x y := by simp
  map_smul' c x := by simp

def faceJoint
    (lower : F →ₗ[K] Wlo) (faceBoundary : F →ₗ[K] B) :
    F →ₗ[K] Wlo × B where
  toFun f := (lower f, faceBoundary f)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- One class simultaneously records failure to lift through lower contact
grades and, when liftable, the relative boundary class. -/
def combinedConnecting
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    LinearMap.ker top →ₗ[K]
      ((Wlo × B) ⧸ LinearMap.range (oldJoint old oldBoundary)) :=
  (LinearMap.range (oldJoint old oldBoundary)).mkQ.comp
    ((faceJoint lower faceBoundary).domRestrict (LinearMap.ker top))

theorem mem_ker_combinedConnecting_iff
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B)
    (v : LinearMap.ker top) :
    v ∈ LinearMap.ker
        (combinedConnecting old lower top oldBoundary faceBoundary) ↔
      ∃ p : P, (old p, oldBoundary p) = (lower v.1, faceBoundary v.1) := by
  rw [LinearMap.mem_ker, combinedConnecting, LinearMap.comp_apply,
    LinearMap.domRestrict_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rfl

/-- The lower-cokernel projection annihilates the old joint image. -/
def jointLowerProjection
    (old : P →ₗ[K] Wlo) (oldBoundary : P →ₗ[K] B) :
    ((Wlo × B) ⧸ LinearMap.range (oldJoint old oldBoundary)) →ₗ[K]
      (Wlo ⧸ LinearMap.range old) :=
  (LinearMap.range (oldJoint old oldBoundary)).liftQ
    ((LinearMap.range old).mkQ.comp (LinearMap.fst K Wlo B)) (by
      intro wb hwb
      rw [LinearMap.mem_ker]
      rcases hwb with ⟨p, rfl⟩
      simp [oldJoint, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero])

/-- Projecting the combined class recovers exactly the lower-grade
obstruction. -/
theorem jointLowerProjection_combinedConnecting
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B)
    (v : LinearMap.ker top) :
    jointLowerProjection old oldBoundary
        (combinedConnecting old lower top oldBoundary faceBoundary v) =
      lowerGradeObstruction old lower top v := by
  rfl

/-- A direct rank bound on the lower obstruction loses at most that many
dimensions from the associated kernel. -/
theorem finrank_liftable_lower_bound_of_obstruction_rank
    [FiniteDimensional K F]
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (q r : ℕ)
    (hkernel : q ≤ Module.finrank K (LinearMap.ker top))
    (hrank : Module.finrank K (LinearMap.range
        (lowerGradeObstruction old lower top)) ≤ r) :
    q - r ≤ Module.finrank K
      (LinearMap.ker (lowerGradeObstruction old lower top)) := by
  have hsum := (lowerGradeObstruction old lower top).finrank_range_add_finrank_ker
  rw [Nat.sub_le_iff_le_add']
  omega

/-- Any factorization through a finite error-syndrome space gives the required
rank bound.  Establishing such a factorization for literal contact is open. -/
theorem finrank_liftable_lower_bound_of_factorization
    [FiniteDimensional K F] [FiniteDimensional K E]
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (g : LinearMap.ker top →ₗ[K] E)
    (h : E →ₗ[K] (Wlo ⧸ LinearMap.range old))
    (hfactor : lowerGradeObstruction old lower top = h.comp g)
    (q r : ℕ)
    (hkernel : q ≤ Module.finrank K (LinearMap.ker top))
    (hE : Module.finrank K E ≤ r) :
    q - r ≤ Module.finrank K
      (LinearMap.ker (lowerGradeObstruction old lower top)) := by
  apply finrank_liftable_lower_bound_of_obstruction_rank old lower top q r hkernel
  rw [hfactor]
  exact (Submodule.finrank_mono (LinearMap.range_comp_le_range g h)).trans
    ((LinearMap.finrank_range_le h).trans hE)

/-- First falsifiable target inequality.  If the obstruction factors through
at most three scalars at each of 81,731 error positions, at least 22,843,686
associated relations genuinely lift. -/
theorem target_three_error_scalar_factorization_receipt :
    3 * 81731 = 245193 ∧ 23088879 - 245193 = 22843686 := by
  norm_num

#print axioms mem_ker_combinedConnecting_iff
#print axioms jointLowerProjection_combinedConnecting
#print axioms finrank_liftable_lower_bound_of_factorization
#print axioms target_three_error_scalar_factorization_receipt

end
end ProximityPrize.SubmissionLower.K0FullFaceCombinedConnecting6900
