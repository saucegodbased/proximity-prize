import K0RelativeAttachmentExactSequence6900

/-!
# The exact strictness condition behind a one-spare-layer argument

Splitting the contact target into lower passive grades and the newly attached
top grade makes the logical gap precise.  The top associated contact of a
face vector may vanish while its lower-grade remainder is not in the image of
the preceding source cap.  Thus an associated-grade kernel lifts to a true
relative contact relation exactly when the filtered contact map is strict at
that vector.

The final counterexample proves that this gap exists for arbitrary linear
maps.  Any target proof must use the literal contact recurrence/interpolation
structure to establish strictness; positive dimensions alone cannot do it.
-/

namespace ProximityPrize.SubmissionLower.K0AssociatedGradeStrictness6900

open K0RelativeAttachmentExactSequence6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K P F Wlo Whi : Type*}
  [Field K]
  [AddCommGroup P] [Module K P]
  [AddCommGroup F] [Module K F]
  [AddCommGroup Wlo] [Module K Wlo]
  [AddCommGroup Whi] [Module K Whi]

/-- The preceding cap has no component in the newly attached grade. -/
def filteredOldContact (old : P →ₗ[K] Wlo) : P →ₗ[K] Wlo × Whi where
  toFun p := (old p, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Split the contact of a last-face vector into its lower remainder and its
associated top-grade symbol. -/
def filteredFaceContact
    (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi) : F →ₗ[K] Wlo × Whi where
  toFun f := (lower f, top f)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- A face vector is genuinely old-correctable iff its associated symbol
vanishes *and* its lower-grade remainder belongs to the old contact image. -/
theorem mem_liftableFace_filtered_iff
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi)
    (f : F) :
    f ∈ liftableFace (filteredOldContact old)
          (filteredFaceContact lower top) ↔
      top f = 0 ∧ lower f ∈ LinearMap.range old := by
  constructor
  · rintro ⟨p, hp⟩
    change (old p, 0) = (lower f, top f) at hp
    exact ⟨(congrArg Prod.snd hp).symm, ⟨p, congrArg Prod.fst hp⟩⟩
  · rintro ⟨htop, p, hp⟩
    refine ⟨p, ?_⟩
    change (old p, 0) = (lower f, top f)
    rw [← hp, htop]

/-- `StrictAtFace` is the exact missing interpolation statement: every
top-symbol relation has an old correction for its lower terms. -/
def StrictAtFace
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi) : Prop :=
  ∀ f, top f = 0 → lower f ∈ LinearMap.range old

/-- Under strictness, and only then, the associated-grade kernel is the true
relative domain used by the connecting boundary map. -/
theorem liftableFace_eq_ker_top_iff_strict
    (old : P →ₗ[K] Wlo) (lower : F →ₗ[K] Wlo) (top : F →ₗ[K] Whi) :
    liftableFace (filteredOldContact old) (filteredFaceContact lower top) =
        LinearMap.ker top ↔
      StrictAtFace old lower top := by
  constructor
  · intro heq f htop
    have hfker : f ∈ LinearMap.ker top := LinearMap.mem_ker.mpr htop
    rw [← heq, mem_liftableFace_filtered_iff] at hfker
    exact hfker.2
  · intro hstrict
    ext f
    rw [mem_liftableFace_filtered_iff, LinearMap.mem_ker]
    constructor
    · exact fun h ↦ h.1
    · intro htop
      exact ⟨htop, hstrict f htop⟩

/-! ## An exact arbitrary-matrix counterexample -/

/-- The lower remainder can obstruct every nonzero associated relation even
when the top symbol has a nontrivial kernel. -/
theorem associated_kernel_need_not_lift :
    let old : K →ₗ[K] K := 0
    let lower : K × K →ₗ[K] K := LinearMap.snd K K K
    let top : K × K →ₗ[K] K := LinearMap.fst K K K
    ((0 : K), 1) ∈ LinearMap.ker top ∧
      ((0 : K), 1) ∉
        liftableFace (filteredOldContact old)
          (filteredFaceContact lower top) := by
  dsimp
  constructor
  · rw [LinearMap.mem_ker]
    rfl
  · rw [mem_liftableFace_filtered_iff]
    simp

#print axioms mem_liftableFace_filtered_iff
#print axioms liftableFace_eq_ker_top_iff_strict
#print axioms associated_kernel_need_not_lift

end
end ProximityPrize.SubmissionLower.K0AssociatedGradeStrictness6900
