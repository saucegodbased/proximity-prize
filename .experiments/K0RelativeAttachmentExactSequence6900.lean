import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.NormNum

/-!
# The last-passive-face exact sequence for lower 6900

This file isolates the linear algebra of attaching the cap-`3757` face to
the cap-`3756` source.  It does **not** assume that the old source has a
contact-kernel vector.  For arbitrary old and face contact maps it proves

```text
ker(old contact) --> ker(attached contact) -->
  {face vectors whose contact is old-correctable} --> 0.
```

After quotienting boundary space by the boundary image of the old kernel,
the boundary map factors canonically through the last term.  Surjectivity of
that relative connecting map implies surjectivity of the complete boundary
map.  This is the exact target-uniform producer statement appropriate when
the cap-`3756` dimension margin is negative.

The final section records why the positive cap-`3757` dimension margin does
not prove this producer: adjoining four boundary rows leaves a positive
nullity lower bound, but gives no lower bound on the four-row rank increment.
-/

namespace ProximityPrize.SubmissionLower.K0RelativeAttachmentExactSequence6900

noncomputable section

set_option autoImplicit false
set_option Elab.async false

variable {K P F W B : Type*}
  [Field K]
  [AddCommGroup P] [Module K P]
  [AddCommGroup F] [Module K F]
  [AddCommGroup W] [Module K W]
  [AddCommGroup B] [Module K B]

/-! ## The filtration attachment -/

/-- Contact after adjoining a new filtration face. -/
def attachedContact (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    P × F →ₗ[K] W where
  toFun pf := oldContact pf.1 + faceContact pf.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c x := by
    change oldContact (c • x.1) + faceContact (c • x.2) =
      c • (oldContact x.1 + faceContact x.2)
    simp only [map_smul, smul_add]

/-- Boundary map after adjoining a new filtration face. -/
def attachedBoundary (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    P × F →ₗ[K] B where
  toFun pf := oldBoundary pf.1 + faceBoundary pf.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' c x := by
    change oldBoundary (c • x.1) + faceBoundary (c • x.2) =
      c • (oldBoundary x.1 + faceBoundary x.2)
    simp only [map_smul, smul_add]

/-- New-face vectors whose contact class vanishes modulo the old contact
image.  This is the kernel of the filtration connecting map to the old
contact cokernel, expressed without choosing a quotient representative. -/
def liftableFace (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    Submodule K F :=
  (LinearMap.range oldContact).comap faceContact

/-- Projection of a complete attached contact relation to its new-face
coordinate. -/
def relativeProjection
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    LinearMap.ker (attachedContact oldContact faceContact) →ₗ[K]
      liftableFace oldContact faceContact where
  toFun v := ⟨v.1.2, by
    refine ⟨-v.1.1, ?_⟩
    have hv := LinearMap.mem_ker.mp v.2
    change oldContact v.1.1 + faceContact v.1.2 = 0 at hv
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_right hv⟩
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

/-- Every old-kernel vector is canonically an attached relation with zero
new-face coordinate. -/
def oldKernelInclusion
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    LinearMap.ker oldContact →ₗ[K]
      LinearMap.ker (attachedContact oldContact faceContact) where
  toFun p := ⟨(p.1, 0), by
    rw [LinearMap.mem_ker]
    simp [attachedContact, LinearMap.mem_ker.mp p.2]⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_smul' c x := by
    apply Subtype.ext
    apply Prod.ext <;> simp

theorem oldKernelInclusion_injective
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    Function.Injective (oldKernelInclusion oldContact faceContact) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun v ↦ v.1.1) hxy

/-- Exactness at the complete attached kernel. -/
theorem relativeProjection_eq_zero_iff_mem_oldKernel
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (v : LinearMap.ker (attachedContact oldContact faceContact)) :
    relativeProjection oldContact faceContact v = 0 ↔
      ∃ p : LinearMap.ker oldContact,
        oldKernelInclusion oldContact faceContact p = v := by
  constructor
  · intro hv
    have hface : v.1.2 = 0 := by
      exact congrArg Subtype.val hv
    have hvcontact := LinearMap.mem_ker.mp v.2
    change oldContact v.1.1 + faceContact v.1.2 = 0 at hvcontact
    rw [hface, map_zero, add_zero] at hvcontact
    let p : LinearMap.ker oldContact :=
      ⟨v.1.1, LinearMap.mem_ker.mpr hvcontact⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hface.symm
  · rintro ⟨p, rfl⟩
    apply Subtype.ext
    rfl

/-- Exactness at the new face: every old-correctable face contact has a
complete attached lift.  No injectivity or old-kernel existence is used. -/
theorem relativeProjection_surjective
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    Function.Surjective (relativeProjection oldContact faceContact) := by
  rintro ⟨f, hf⟩
  rcases hf with ⟨p, hp⟩
  let v : LinearMap.ker (attachedContact oldContact faceContact) :=
    ⟨(-p, f), by
      rw [LinearMap.mem_ker]
      change oldContact (-p) + faceContact f = 0
      rw [map_neg, ← hp]
      exact neg_add_cancel _⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  rfl

/-! ## Boundary modulo the old-kernel image -/

def oldNormal
    (oldContact : P →ₗ[K] W) (oldBoundary : P →ₗ[K] B) :
    LinearMap.ker oldContact →ₗ[K] B :=
  oldBoundary.domRestrict (LinearMap.ker oldContact)

def attachedNormal
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    LinearMap.ker (attachedContact oldContact faceContact) →ₗ[K] B :=
  (attachedBoundary oldBoundary faceBoundary).domRestrict
    (LinearMap.ker (attachedContact oldContact faceContact))

/-- Complete boundary, reduced modulo the boundary image already generated
by old contact-kernel relations. -/
def quotientAttachedNormal
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    LinearMap.ker (attachedContact oldContact faceContact) →ₗ[K]
      B ⧸ (LinearMap.range (oldNormal oldContact oldBoundary)) :=
  (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ.comp
    (attachedNormal oldContact faceContact oldBoundary faceBoundary)

theorem relativeProjection_ker_le_quotientAttachedNormal_ker
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    LinearMap.ker (relativeProjection oldContact faceContact) ≤
      LinearMap.ker
        (quotientAttachedNormal oldContact faceContact
          oldBoundary faceBoundary) := by
  intro v hv
  have hvzero : relativeProjection oldContact faceContact v = 0 :=
    LinearMap.mem_ker.mp hv
  rcases (relativeProjection_eq_zero_iff_mem_oldKernel
      oldContact faceContact v).mp hvzero with ⟨p, rfl⟩
  rw [LinearMap.mem_ker]
  change (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ
      (oldBoundary p.1 + faceBoundary 0) = 0
  simp only [map_zero, add_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  refine ⟨p, ?_⟩
  rfl

/-- The canonical relative boundary connecting map on old-correctable
new-face vectors.  Its construction is independent of a choice of old
contact correction: two corrections differ by an old-kernel vector, whose
boundary is zero in the quotient. -/
def relativeConnectingBoundary
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    liftableFace oldContact faceContact →ₗ[K]
      B ⧸ (LinearMap.range (oldNormal oldContact oldBoundary)) :=
  ((LinearMap.ker (relativeProjection oldContact faceContact)).liftQ
      (quotientAttachedNormal oldContact faceContact oldBoundary faceBoundary)
      (relativeProjection_ker_le_quotientAttachedNormal_ker
        oldContact faceContact oldBoundary faceBoundary)).comp
    ((relativeProjection oldContact faceContact).quotKerEquivOfSurjective
      (relativeProjection_surjective oldContact faceContact)).symm.toLinearMap

theorem relativeConnectingBoundary_relativeProjection
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B)
    (v : LinearMap.ker (attachedContact oldContact faceContact)) :
    relativeConnectingBoundary oldContact faceContact oldBoundary faceBoundary
        (relativeProjection oldContact faceContact v) =
      quotientAttachedNormal oldContact faceContact oldBoundary faceBoundary v := by
  simp [relativeConnectingBoundary, quotientAttachedNormal]

/-- The exact relative producer theorem.  It needs no cap-`3756` kernel and
no contact pivot: surjectivity on the old-correctable new face, modulo the
old normal image, supplies every complete boundary direction. -/
theorem attachedNormal_surjective_of_relativeConnectingBoundary_surjective
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B)
    (hrelative : Function.Surjective
      (relativeConnectingBoundary oldContact faceContact
        oldBoundary faceBoundary)) :
    Function.Surjective
      (attachedNormal oldContact faceContact oldBoundary faceBoundary) := by
  intro b
  let q :=
    (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ b
  obtain ⟨f, hf⟩ := hrelative q
  obtain ⟨v, hv⟩ :=
    relativeProjection_surjective oldContact faceContact f
  have hq : quotientAttachedNormal oldContact faceContact
      oldBoundary faceBoundary v = q := by
    rw [← relativeConnectingBoundary_relativeProjection
      oldContact faceContact oldBoundary faceBoundary v, hv, hf]
  have hdiff : b - attachedNormal oldContact faceContact
      oldBoundary faceBoundary v ∈
        LinearMap.range (oldNormal oldContact oldBoundary) := by
    rw [← Submodule.Quotient.eq]
    change (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ b =
      (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ
        (attachedNormal oldContact faceContact oldBoundary faceBoundary v)
    exact hq.symm
  rcases hdiff with ⟨p, hp⟩
  let oldv := oldKernelInclusion oldContact faceContact p
  refine ⟨v + oldv, ?_⟩
  change attachedNormal oldContact faceContact oldBoundary faceBoundary
      (v + oldv) = b
  rw [map_add]
  have hold : attachedNormal oldContact faceContact oldBoundary faceBoundary
      oldv = oldNormal oldContact oldBoundary p := by
    simp [oldv, attachedNormal, attachedBoundary, oldKernelInclusion,
      oldNormal]
  rw [hold, hp]
  abel

/-- Conversely, a surjective complete normal map is already surjective after
passing to the relative new-face quotient.  Combined with the preceding
theorem, this says that the relative connecting map is not merely sufficient:
it is the exact producer. -/
theorem attachedNormal_surjective_iff_relativeConnectingBoundary_surjective
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    Function.Surjective
        (attachedNormal oldContact faceContact oldBoundary faceBoundary) ↔
      Function.Surjective
        (relativeConnectingBoundary oldContact faceContact
          oldBoundary faceBoundary) := by
  constructor
  · intro hfull q
    obtain ⟨b, rfl⟩ :=
      (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ_surjective q
    obtain ⟨v, hv⟩ := hfull b
    refine ⟨relativeProjection oldContact faceContact v, ?_⟩
    rw [relativeConnectingBoundary_relativeProjection]
    change (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ
        (attachedNormal oldContact faceContact oldBoundary faceBoundary v) =
      (LinearMap.range (oldNormal oldContact oldBoundary)).mkQ b
    rw [hv]
  · exact attachedNormal_surjective_of_relativeConnectingBoundary_surjective
      oldContact faceContact oldBoundary faceBoundary

/-- Dual reverse-Hasse form of the exact producer.  To prove the complete
normal map onto, it is necessary and sufficient to show that every covector
on the relative boundary quotient which kills all old-correctable face
vectors is zero.  This is the minimal hypothesis to be discharged by the
adjacent-cell/locator recurrence. -/
theorem attachedNormal_surjective_iff_no_relative_dual
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] B) (faceBoundary : F →ₗ[K] B) :
    Function.Surjective
        (attachedNormal oldContact faceContact oldBoundary faceBoundary) ↔
      ∀ ell : Module.Dual K
          (B ⧸ (LinearMap.range (oldNormal oldContact oldBoundary))),
        (∀ f : liftableFace oldContact faceContact,
          ell (relativeConnectingBoundary oldContact faceContact
            oldBoundary faceBoundary f) = 0) →
        ell = 0 := by
  rw [attachedNormal_surjective_iff_relativeConnectingBoundary_surjective]
  let delta := relativeConnectingBoundary oldContact faceContact
    oldBoundary faceBoundary
  constructor
  · intro hsurj ell hann
    have hinj : Function.Injective delta.dualMap :=
      LinearMap.dualMap_injective_iff.mpr hsurj
    apply hinj
    apply LinearMap.ext
    intro f
    simpa [LinearMap.dualMap_apply, delta] using hann f
  · intro hzero
    rw [← LinearMap.dualMap_injective_iff]
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro ell hell
    apply hzero ell
    intro f
    have hpoint := LinearMap.congr_fun hell f
    simpa [LinearMap.dualMap_apply, delta] using hpoint

/-! ## Exact rank identity and the dimension-count audit -/

variable [FiniteDimensional K P] [FiniteDimensional K F]

theorem attachedKernel_finrank_eq_oldKernel_add_liftableFace
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    Module.finrank K (LinearMap.ker (attachedContact oldContact faceContact)) =
      Module.finrank K (LinearMap.ker oldContact) +
        Module.finrank K (liftableFace oldContact faceContact) := by
  let proj := relativeProjection oldContact faceContact
  have hsum := proj.finrank_range_add_finrank_ker
  have hrange : Module.finrank K (LinearMap.range proj) =
      Module.finrank K (liftableFace oldContact faceContact) := by
    rw [LinearMap.range_eq_top.mpr
      (relativeProjection_surjective oldContact faceContact), finrank_top]
  have hker : Module.finrank K (LinearMap.ker proj) =
      Module.finrank K (LinearMap.ker oldContact) := by
    let inc := oldKernelInclusion oldContact faceContact
    have hinc : Function.Injective inc :=
      oldKernelInclusion_injective oldContact faceContact
    have hRange : LinearMap.range inc = LinearMap.ker proj := by
      ext v
      constructor
      · rintro ⟨p, rfl⟩
        rw [LinearMap.mem_ker]
        exact (relativeProjection_eq_zero_iff_mem_oldKernel
          oldContact faceContact _).mpr ⟨p, rfl⟩
      · intro hv
        have hvzero := LinearMap.mem_ker.mp hv
        rcases (relativeProjection_eq_zero_iff_mem_oldKernel
          oldContact faceContact v).mp hvzero with ⟨p, hp⟩
        exact ⟨p, hp⟩
    rw [← hRange, LinearMap.finrank_range_of_inj hinc]
  rw [hrange, hker] at hsum
  omega

/-- Hilbert-function form of the attachment exact sequence.  It isolates the
new-face contribution without requiring the old contact map to be injective:

`dim liftable face + rank attached = dim face + rank old`.
-/
theorem liftableFace_finrank_add_attachedRank
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) :
    Module.finrank K (liftableFace oldContact faceContact) +
        Module.finrank K
          (LinearMap.range (attachedContact oldContact faceContact)) =
      Module.finrank K F +
        Module.finrank K (LinearMap.range oldContact) := by
  have hkernel := attachedKernel_finrank_eq_oldKernel_add_liftableFace
    oldContact faceContact
  have hattached :=
    (attachedContact oldContact faceContact).finrank_range_add_finrank_ker
  have hold := oldContact.finrank_range_add_finrank_ker
  have hprod : Module.finrank K (P × F) =
      Module.finrank K P + Module.finrank K F := by
    exact Module.finrank_prod
  omega

/-- Consequently, a bound on the *rank increment* across the filtration face
gives a lower bound on the old-correctable part of that face.  Separate rank
upper bounds at the two caps do not by themselves supply `hIncrement`. -/
theorem liftableFace_finrank_lower_bound_of_rank_increment
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W) (q : Nat)
    (hIncrement :
      Module.finrank K
          (LinearMap.range (attachedContact oldContact faceContact)) ≤
        Module.finrank K (LinearMap.range oldContact) + q) :
    Module.finrank K F - q ≤
      Module.finrank K (liftableFace oldContact faceContact) := by
  have hid := liftableFace_finrank_add_attachedRank oldContact faceContact
  omega

/-- If the published difference of local rank budgets were proved to bound
the actual all-node rank increment, the literal last passive face would have
at least `23,088,879` old-correctable dimensions. -/
theorem target_lastFace_liftable_finrank_of_increment_bound
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (hFace : Module.finrank K F = 17434693359)
    (hIncrement :
      Module.finrank K
          (LinearMap.range (attachedContact oldContact faceContact)) ≤
        Module.finrank K (LinearMap.range oldContact) + 17411604480) :
    23088879 ≤ Module.finrank K
      (liftableFace oldContact faceContact) := by
  have h := liftableFace_finrank_lower_bound_of_rank_increment
    oldContact faceContact 17411604480 hIncrement
  rw [hFace] at h
  norm_num at h ⊢
  exact h

/-- Four boundary equations can remove at most four dimensions from the
relative domain.  This is why a huge old-correctable face space still says
nothing about whether its boundary image has rank four. -/
theorem relativeConnectingBoundary_kernel_lower_bound_four
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] (Fin 4 → K))
    (faceBoundary : F →ₗ[K] (Fin 4 → K)) :
    Module.finrank K (liftableFace oldContact faceContact) - 4 ≤
      Module.finrank K
        (LinearMap.ker
          (relativeConnectingBoundary oldContact faceContact
            oldBoundary faceBoundary)) := by
  let delta := relativeConnectingBoundary oldContact faceContact
    oldBoundary faceBoundary
  have hsum := delta.finrank_range_add_finrank_ker
  have hsum' :
      Module.finrank K
          (LinearMap.range
            (relativeConnectingBoundary oldContact faceContact
              oldBoundary faceBoundary)) +
        Module.finrank K
          (LinearMap.ker
            (relativeConnectingBoundary oldContact faceContact
              oldBoundary faceBoundary)) =
        Module.finrank K (liftableFace oldContact faceContact) := by
    simpa only [delta] using hsum
  have hrange : Module.finrank K (LinearMap.range delta) ≤ 4 := by
    calc
      Module.finrank K (LinearMap.range delta) ≤
          Module.finrank K
            ((Fin 4 → K) ⧸
              (LinearMap.range (oldNormal oldContact oldBoundary))) :=
        Submodule.finrank_le _
      _ ≤ Module.finrank K (Fin 4 → K) :=
        Submodule.finrank_quotient_le _
      _ = 4 := by simp
  have hrange' : Module.finrank K
      (LinearMap.range
        (relativeConnectingBoundary oldContact faceContact
          oldBoundary faceBoundary)) ≤ 4 := by
    simpa only [delta] using hrange
  omega

/-- Combining the two conditional ledgers leaves at least `23,088,875`
relative directions which kill contact and all four boundary rows.  This is
not a rank-four conclusion; it is the sharp dimensional reason the augmented
nullity audit cannot prove one. -/
theorem target_lastFace_jointKernel_of_increment_bound
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] (Fin 4 → K))
    (faceBoundary : F →ₗ[K] (Fin 4 → K))
    (hFace : Module.finrank K F = 17434693359)
    (hIncrement :
      Module.finrank K
          (LinearMap.range (attachedContact oldContact faceContact)) ≤
        Module.finrank K (LinearMap.range oldContact) + 17411604480) :
    23088875 ≤ Module.finrank K
      (LinearMap.ker
        (relativeConnectingBoundary oldContact faceContact
          oldBoundary faceBoundary)) := by
  have hlift := target_lastFace_liftable_finrank_of_increment_bound
    oldContact faceContact hFace hIncrement
  have hker := relativeConnectingBoundary_kernel_lower_bound_four
    oldContact faceContact oldBoundary faceBoundary
  omega

/-- Exact four-boundary rank ledger.  The new face has to contribute the
complement of the rank already supplied by old-kernel boundaries; no
existence of an old relation is assumed. -/
theorem attachedNormal_surjective_iff_relative_rank_add_old_rank_eq_four
    (oldContact : P →ₗ[K] W) (faceContact : F →ₗ[K] W)
    (oldBoundary : P →ₗ[K] (Fin 4 → K))
    (faceBoundary : F →ₗ[K] (Fin 4 → K)) :
    Function.Surjective
        (attachedNormal oldContact faceContact oldBoundary faceBoundary) ↔
      Module.finrank K
          (LinearMap.range
            (relativeConnectingBoundary oldContact faceContact
              oldBoundary faceBoundary)) +
        Module.finrank K
          (LinearMap.range (oldNormal oldContact oldBoundary)) = 4 := by
  let oldRange := LinearMap.range (oldNormal oldContact oldBoundary)
  let delta := relativeConnectingBoundary oldContact faceContact
    oldBoundary faceBoundary
  have hquot : Module.finrank K ((Fin 4 → K) ⧸ oldRange) +
      Module.finrank K oldRange = 4 := by
    have h := oldRange.finrank_quotient_add_finrank
    simpa only [Module.finrank_pi_fintype, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_one,
      Module.finrank_self] using h
  rw [attachedNormal_surjective_iff_relativeConnectingBoundary_surjective]
  constructor
  · intro hsurj
    have hrange : LinearMap.range delta = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hdim : Module.finrank K (LinearMap.range delta) =
        Module.finrank K ((Fin 4 → K) ⧸ oldRange) := by
      rw [hrange, finrank_top]
    simpa only [delta, oldRange] using hdim ▸ hquot
  · intro hrank
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have hdim : Module.finrank K (LinearMap.range delta) =
        Module.finrank K ((Fin 4 → K) ⧸ oldRange) := by
      have hrank' : Module.finrank K (LinearMap.range delta) +
          Module.finrank K oldRange = 4 := by
        simpa only [delta, oldRange] using hrank
      omega
    simpa only [delta, oldRange] using hdim

private def kernelBoundary
    {V S : Type*}
    [AddCommGroup V] [Module K V]
    [AddCommGroup S] [Module K S]
    (contact : V →ₗ[K] S) (boundary : V →ₗ[K] (Fin 4 → K)) :
    LinearMap.ker contact →ₗ[K] (Fin 4 → K) :=
  boundary.domRestrict (LinearMap.ker contact)

private def pairedKernelEquiv
    {V S : Type*}
    [AddCommGroup V] [Module K V]
    [AddCommGroup S] [Module K S]
    (contact : V →ₗ[K] S) (boundary : V →ₗ[K] (Fin 4 → K)) :
    LinearMap.ker (kernelBoundary contact boundary) ≃ₗ[K]
      LinearMap.ker (contact.prod boundary) where
  toFun x := ⟨x.1.1, by
    rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero]
    exact ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, by
    have hx := x.2
    rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hx
    exact hx.1⟩, by
      have hx := x.2
      rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hx
      exact hx.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

private theorem kernelBoundary_rank_add_contact
    {V S : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup S] [Module K S]
    (contact : V →ₗ[K] S) (boundary : V →ₗ[K] (Fin 4 → K)) :
    Module.finrank K (LinearMap.range (kernelBoundary contact boundary)) +
        Module.finrank K (LinearMap.range contact) =
      Module.finrank K (LinearMap.range (contact.prod boundary)) := by
  have hrestricted :=
    (kernelBoundary contact boundary).finrank_range_add_finrank_ker
  have hcontact := contact.finrank_range_add_finrank_ker
  have hpaired := (contact.prod boundary).finrank_range_add_finrank_ker
  have hker :
      Module.finrank K (LinearMap.ker (kernelBoundary contact boundary)) =
        Module.finrank K (LinearMap.ker (contact.prod boundary)) :=
    LinearEquiv.finrank_eq (pairedKernelEquiv contact boundary)
  omega

/-- A four-row augmentation can increase rank by at most four. -/
theorem augmented_rank_le_contact_rank_add_four
    {V S : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup S] [Module K S]
    (contact : V →ₗ[K] S) (boundary : V →ₗ[K] (Fin 4 → K)) :
    Module.finrank K (LinearMap.range (contact.prod boundary)) ≤
      Module.finrank K (LinearMap.range contact) + 4 := by
  have hid := kernelBoundary_rank_add_contact contact boundary
  have hnormal : Module.finrank K
      (LinearMap.range (kernelBoundary contact boundary)) ≤ 4 := by
    calc
      Module.finrank K
          (LinearMap.range (kernelBoundary contact boundary)) ≤
          Module.finrank K (Fin 4 → K) := Submodule.finrank_le _
      _ = 4 := by simp
  omega

/-- What a source-margin argument really proves after adding four boundary
rows: a lower bound on the kernel of the *augmented* map.  It does not give a
lower bound on the rank gained by those rows. -/
theorem augmented_kernel_finrank_lower_bound
    {V S : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup S] [Module K S]
    (contact : V →ₗ[K] S) (boundary : V →ₗ[K] (Fin 4 → K))
    (N R : Nat) (hSource : Module.finrank K V = N)
    (hContact : Module.finrank K (LinearMap.range contact) ≤ R) :
    N - (R + 4) ≤
      Module.finrank K (LinearMap.ker (contact.prod boundary)) := by
  have haug := augmented_rank_le_contact_rank_add_four contact boundary
  have hrank : Module.finrank K
      (LinearMap.range (contact.prod boundary)) ≤ R + 4 := by
    omega
  have hsum := (contact.prod boundary).finrank_range_add_finrank_ker
  omega

/-- Literal target specialization of the preceding statement.  The output
`2,371,076` counts simultaneous contact-and-boundary-zero vectors. -/
theorem target_L3757_augmented_kernel_lower_bound
    {V S : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup S] [Module K S]
    (contact : V →ₗ[K] S) (boundary : V →ₗ[K] (Fin 4 → K))
    (hSource : Module.finrank K V = 65061789117960)
    (hContact : Module.finrank K (LinearMap.range contact) ≤
      65061786746880) :
    2371076 ≤
      Module.finrank K (LinearMap.ker (contact.prod boundary)) := by
  have h := augmented_kernel_finrank_lower_bound contact boundary
    65061789117960 65061786746880 hSource hContact
  norm_num at h ⊢
  exact h

/-- Exact arithmetic behind the cap-`3757` source margin and its four-row
augmentation.  The last number is a *joint-kernel* lower-bound ledger, not a
four-boundary rank lower bound. -/
theorem target_L3757_contact_and_augmented_margin_receipt :
    248191020 * 262144 = 65061786746880 ∧
      65061789117960 - 65061786746880 = 2371080 ∧
      65061789117960 - (65061786746880 + 4) = 2371076 := by
  norm_num

/-- The preceding kind of dimension data cannot imply boundary
surjectivity.  Even with source dimension five and zero contact rank (hence
four units of spare dimension), the zero four-boundary map has rank zero. -/
theorem dimension_margin_four_countermodel :
    ∃ contact : (Fin 5 → K) →ₗ[K] (Fin 1 → K),
      ∃ boundary : (Fin 5 → K) →ₗ[K] (Fin 4 → K),
        Module.finrank K (Fin 5 → K) = 5 ∧
          Module.finrank K (LinearMap.range contact) = 0 ∧
          4 ≤ Module.finrank K (Fin 5 → K) -
            Module.finrank K (LinearMap.range contact) ∧
          ¬ Function.Surjective
            (boundary.domRestrict (LinearMap.ker contact)) := by
  let contact : (Fin 5 → K) →ₗ[K] (Fin 1 → K) := 0
  let boundary : (Fin 5 → K) →ₗ[K] (Fin 4 → K) := 0
  have hcrank : Module.finrank K (LinearMap.range contact) = 0 := by
    simp [contact]
  refine ⟨contact, boundary, by simp, hcrank, ?_, ?_⟩
  · rw [hcrank]
    norm_num
  intro hsurj
  let e : Fin 4 → K := fun i ↦ if i = 0 then 1 else 0
  obtain ⟨v, hv⟩ := hsurj e
  have hzero : boundary.domRestrict (LinearMap.ker contact) v = 0 := by
    simp [boundary]
  have hezero : e = 0 := hv ▸ hzero
  have hcoord := congrFun hezero 0
  simp [e] at hcoord

#print axioms relativeProjection_eq_zero_iff_mem_oldKernel
#print axioms relativeProjection_surjective
#print axioms relativeConnectingBoundary_relativeProjection
#print axioms attachedNormal_surjective_of_relativeConnectingBoundary_surjective
#print axioms attachedNormal_surjective_iff_relativeConnectingBoundary_surjective
#print axioms attachedNormal_surjective_iff_no_relative_dual
#print axioms attachedKernel_finrank_eq_oldKernel_add_liftableFace
#print axioms liftableFace_finrank_add_attachedRank
#print axioms target_lastFace_liftable_finrank_of_increment_bound
#print axioms target_lastFace_jointKernel_of_increment_bound
#print axioms attachedNormal_surjective_iff_relative_rank_add_old_rank_eq_four
#print axioms augmented_rank_le_contact_rank_add_four
#print axioms augmented_kernel_finrank_lower_bound
#print axioms target_L3757_augmented_kernel_lower_bound
#print axioms target_L3757_contact_and_augmented_margin_receipt
#print axioms dimension_margin_four_countermodel

end

end ProximityPrize.SubmissionLower.K0RelativeAttachmentExactSequence6900
