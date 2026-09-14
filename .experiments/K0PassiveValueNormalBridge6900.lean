import K0LineThenKill6900
import K0PassiveSeedProductRule6900
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Passive-value bridge, its root-count stop, and the relative repair

This file isolates the target-uniform consequence of the passive-seed
product rule.  Let `old` be any source subspace on which the contact kernel
already supplies the residual boundary hyperplane.  Suppose multiplication
by the passive coordinate is source-legal on `old`, preserves contact-kernel
relations, and satisfies

`boundary (Z * v) = gamma * boundary v + value(v) * eZ`.

Conditionally, one old contact-kernel relation with nonzero boundary value
produces a complete-kernel vector in the missing `eZ` direction.  The file
also records why this attractive condition is normally false in the exact-G
application: 47 zero Hasse coordinates at each of `g` distinct agreement
nodes force every degree-`< 47*g` value trace to vanish identically.  That
root-count result is compiled separately in `K0PassiveValueRootStop6900` so
both checks stay below the local memory ceiling.

The honest producer is therefore relative.  A newly legal passive-layer
vector must have the same complete contact trace as an old vector but a
transverse boundary difference.  Their difference is the genuinely new
kernel normal.  This is the precise connecting-map hypothesis left open by
the finite passive-reach ablation.

The theorem is rank-adaptive: the residual hyperplane is named by an
arbitrary covector, not by fixed boundary coordinates or a contact pivot.
The final section records the exact one-step passive-cap legality in the
literal lower-6900 source.
-/

namespace ProximityPrize.SubmissionLower.K0PassiveValueNormalBridge6900

open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

variable {K Source Contact Boundary : Type*}
  [Field K]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Contact] [Module K Contact]
  [AddCommGroup Boundary] [Module K Boundary]

/-- A nonzero linear functional to the ground field is surjective, and this
is the only way such a functional can be surjective.  Applied to the value
functional on an old contact kernel, this identifies the two useful forms of
the remaining hypothesis. -/
theorem linearFunctional_surjective_iff_exists_ne_zero
    {V : Type*} [AddCommGroup V] [Module K V] (f : V →ₗ[K] K) :
    Function.Surjective f ↔ ∃ v : V, f v ≠ 0 := by
  constructor
  · intro hsurj
    obtain ⟨v, hv⟩ := hsurj 1
    refine ⟨v, ?_⟩
    rw [hv]
    exact one_ne_zero
  · rintro ⟨v, hv⟩ y
    refine ⟨(y / f v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    field_simp

/-- The restriction of the boundary-value functional to the old contact
kernel. -/
def oldKernelValue
    (contact : Source →ₗ[K] Contact) (old : Submodule K Source)
    (value : old →ₗ[K] K) :
    LinearMap.ker (contact.domRestrict old) →ₗ[K] K :=
  value.domRestrict (LinearMap.ker (contact.domRestrict old))

/-- Product-rule cancellation: subtracting `gamma` times an old relation
from its passive shift removes the old boundary vector and leaves exactly
its scalar value times the passive basis vector.  Both terms remain in the
complete contact kernel. -/
theorem passive_difference_realizes_old_value
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (shift : old →ₗ[K] Source)
    (value : old →ₗ[K] K) (gamma : K) (eZ : Boundary)
    (hshiftContact : ∀ v : old, contact v.1 = 0 → contact (shift v) = 0)
    (hproduct : ∀ v : old,
      boundary (shift v) = gamma • boundary v.1 + value v • eZ)
    (v : LinearMap.ker (contact.domRestrict old)) :
    ∃ repaired : LinearMap.ker contact,
      boundary repaired.1 = oldKernelValue contact old value v • eZ := by
  have hvcontact : contact v.1.1 = 0 := by
    exact v.2
  refine ⟨⟨shift v.1 - gamma • v.1.1, ?_⟩, ?_⟩
  · simp [hshiftContact v.1 hvcontact, hvcontact]
  · simp only [map_sub, map_smul, hproduct]
    change gamma • boundary v.1.1 + value v.1 • eZ -
        gamma • boundary v.1.1 = value v.1 • eZ
    abel

/-- The product rule turns a nonzero old-kernel boundary value into a
complete contact-kernel normal detected by any residual covector which sees
the passive basis direction. -/
theorem exists_residual_normal_of_oldKernelValue_ne_zero
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (shift : old →ₗ[K] Source)
    (value : old →ₗ[K] K) (gamma : K) (eZ : Boundary)
    (residual : Module.Dual K Boundary)
    (hshiftContact : ∀ v : old, contact v.1 = 0 → contact (shift v) = 0)
    (hproduct : ∀ v : old,
      boundary (shift v) = gamma • boundary v.1 + value v • eZ)
    (heZ : residual eZ ≠ 0)
    (hvalue : ∃ v : LinearMap.ker (contact.domRestrict old),
      oldKernelValue contact old value v ≠ 0) :
    ∃ repaired : LinearMap.ker contact,
      residual (boundary repaired.1) ≠ 0 := by
  obtain ⟨v, hv⟩ := hvalue
  obtain ⟨repaired, hboundary⟩ :=
    passive_difference_realizes_old_value contact boundary old shift value
      gamma eZ hshiftContact hproduct v
  refine ⟨repaired, ?_⟩
  rw [hboundary, map_smul]
  exact mul_ne_zero hv heZ

/-- A residual hyperplane supplied by an old contact kernel plus one
transverse complete-kernel vector spans the whole boundary.  This is the
coordinate-free rank-three-plus-one consumer used by both bridges below. -/
theorem normal_surjective_of_old_hyperplane_and_transverse_kernel
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (residual : Module.Dual K Boundary)
    (hhyperplane : ∀ b : Boundary, residual b = 0 →
      ∃ v : old, contact v.1 = 0 ∧ boundary v.1 = b)
    (repaired : LinearMap.ker contact)
    (htransverse : residual (boundary repaired.1) ≠ 0) :
    Function.Surjective
      (K0LineThenKill6900.normalOnContactKernel contact boundary) := by
  intro b
  let a : K := residual b / residual (boundary repaired.1)
  let b0 : Boundary := b - a • boundary repaired.1
  have hb0 : residual b0 = 0 := by
    dsimp only [b0, a]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  obtain ⟨v, hvcontact, hvboundary⟩ := hhyperplane b0 hb0
  refine ⟨⟨v.1 + a • repaired.1, ?_⟩, ?_⟩
  · simp [hvcontact]
  · change boundary (v.1 + a • repaired.1) = b
    rw [map_add, map_smul, hvboundary]
    dsimp only [b0]
    abel

/-- The correct passive-layer endpoint after the old-value route is ruled
out.  The new vector need not be a shift of an old kernel relation.  It must
instead match the complete contact trace of some old vector while changing
the residual boundary value. -/
theorem normal_surjective_of_old_hyperplane_and_relative_repair
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (residual : Module.Dual K Boundary)
    (hhyperplane : ∀ b : Boundary, residual b = 0 →
      ∃ v : old, contact v.1 = 0 ∧ boundary v.1 = b)
    (newRepair : Source) (oldRepair : old)
    (hcontact : contact newRepair = contact oldRepair.1)
    (hboundary :
      residual (boundary newRepair - boundary oldRepair.1) ≠ 0) :
    Function.Surjective
      (K0LineThenKill6900.normalOnContactKernel contact boundary) := by
  let repaired : LinearMap.ker contact :=
    ⟨newRepair - oldRepair.1, by simp [hcontact]⟩
  apply normal_surjective_of_old_hyperplane_and_transverse_kernel
    contact boundary old residual hhyperplane repaired
  simpa [repaired, map_sub] using hboundary

/-- Main target-uniform bridge.

The old contact kernel need only cover the hyperplane killed by `residual`.
One nonzero old-kernel value then supplies a transverse complete-kernel
normal through a source-legal passive shift, so the complete normal map is
surjective. -/
theorem normal_surjective_of_old_hyperplane_and_value_ne_zero
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (shift : old →ₗ[K] Source)
    (value : old →ₗ[K] K) (gamma : K) (eZ : Boundary)
    (residual : Module.Dual K Boundary)
    (hshiftContact : ∀ v : old, contact v.1 = 0 → contact (shift v) = 0)
    (hproduct : ∀ v : old,
      boundary (shift v) = gamma • boundary v.1 + value v • eZ)
    (hhyperplane : ∀ b : Boundary, residual b = 0 →
      ∃ v : old, contact v.1 = 0 ∧ boundary v.1 = b)
    (heZ : residual eZ ≠ 0)
    (hvalue : ∃ v : LinearMap.ker (contact.domRestrict old),
      oldKernelValue contact old value v ≠ 0) :
    Function.Surjective
      (K0LineThenKill6900.normalOnContactKernel contact boundary) := by
  obtain ⟨repaired, hrepaired⟩ :=
    exists_residual_normal_of_oldKernelValue_ne_zero
      contact boundary old shift value gamma eZ residual
      hshiftContact hproduct heZ hvalue
  exact normal_surjective_of_old_hyperplane_and_transverse_kernel
    contact boundary old residual hhyperplane repaired hrepaired

/-- Surjective-value formulation of the main bridge.  Because the codomain
is the field, this is equivalent to the preceding nonvanishing premise. -/
theorem normal_surjective_of_old_hyperplane_and_value_surjective
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (shift : old →ₗ[K] Source)
    (value : old →ₗ[K] K) (gamma : K) (eZ : Boundary)
    (residual : Module.Dual K Boundary)
    (hshiftContact : ∀ v : old, contact v.1 = 0 → contact (shift v) = 0)
    (hproduct : ∀ v : old,
      boundary (shift v) = gamma • boundary v.1 + value v • eZ)
    (hhyperplane : ∀ b : Boundary, residual b = 0 →
      ∃ v : old, contact v.1 = 0 ∧ boundary v.1 = b)
    (heZ : residual eZ ≠ 0)
    (hvalue : Function.Surjective (oldKernelValue contact old value)) :
    Function.Surjective
      (K0LineThenKill6900.normalOnContactKernel contact boundary) := by
  apply normal_surjective_of_old_hyperplane_and_value_ne_zero
    contact boundary old shift value gamma eZ residual
    hshiftContact hproduct hhyperplane heZ
  exact (linearFunctional_surjective_iff_exists_ne_zero
    (oldKernelValue contact old value)).mp hvalue

/-! ## Abstract no-gain consequence of the exact-G root-count stop -/

/-- When the root bound makes the old-kernel value zero, every passive shift
of an old kernel relation has boundary normal `gamma` times an old normal.
It therefore cannot be the new transverse direction seen in the ablation. -/
theorem passive_shift_of_zero_value_stays_in_old_normal_range
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (old : Submodule K Source) (shift : old →ₗ[K] Source)
    (value : old →ₗ[K] K) (gamma : K) (eZ : Boundary)
    (hproduct : ∀ v : old,
      boundary (shift v) = gamma • boundary v.1 + value v • eZ)
    (hvalueZero : oldKernelValue contact old value = 0)
    (v : LinearMap.ker (contact.domRestrict old)) :
    boundary (shift v.1) ∈ LinearMap.range
      (K0LineThenKill6900.normalOnContactKernel
        (contact.domRestrict old) (boundary.domRestrict old)) := by
  have hvzero : value v.1 = 0 := by
    have hpoint := LinearMap.congr_fun hvalueZero v
    exact hpoint
  refine ⟨gamma • v, ?_⟩
  change boundary (gamma • v.1.1) = boundary (shift v.1)
  rw [hproduct v.1, hvzero]
  simp

/-! ## Exact lower-6900 passive-cap legality -/

/-- For a monomial already legal in the target source, a one-step passive
shift is legal exactly when it is not on the terminal total-degree face.
Every active and weighted cap is unchanged. -/
theorem target_rawShapeLegal_passive_succ_iff
    (a s y r z : Nat)
    (hlegal : rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r z) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        a s y r (z + 1) ↔
      s + y + r + z < 3757 := by
  unfold rawShapeLegal at hlegal ⊢
  omega

/-- In particular, every member of the one-lower passive truncation embeds
after multiplication by `Z` into the literal target source. -/
theorem target_L3756_to_L3757_passive_shift_legal
    (a s y r z : Nat)
    (hlegal : rawShapeLegal (47 * 180413) 131071 3756 16 8 64
      a s y r z) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r (z + 1) := by
  unfold rawShapeLegal at hlegal ⊢
  omega

/-- The uniform target-safe window obtained only from the active cap
`s+y+r <= 64`: all passive exponents through `3692` have a legal successor.
-/
theorem target_rawShapeLegal_passive_succ_of_z_le_3692
    (a s y r z : Nat) (hz : z ≤ 3692)
    (hlegal : rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r z) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r (z + 1) := by
  exact (target_rawShapeLegal_passive_succ_iff a s y r z hlegal).2 (by
    unfold rawShapeLegal at hlegal
    omega)

/-- The literal adjacent `Y^48` bands proposed by the finite mechanism are
both source-legal for every exact admissible X exponent. -/
theorem target_y48_Z0_Z1_bands_legal
    (a : Nat) (ha : a < 2188003) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64 a 0 48 0 0 ∧
      rawShapeLegal (47 * 180413) 131071 3757 16 8 64 a 0 48 0 1 := by
  constructor <;> unfold rawShapeLegal <;> norm_num <;> omega

#print axioms linearFunctional_surjective_iff_exists_ne_zero
#print axioms passive_difference_realizes_old_value
#print axioms exists_residual_normal_of_oldKernelValue_ne_zero
#print axioms normal_surjective_of_old_hyperplane_and_transverse_kernel
#print axioms normal_surjective_of_old_hyperplane_and_relative_repair
#print axioms normal_surjective_of_old_hyperplane_and_value_ne_zero
#print axioms normal_surjective_of_old_hyperplane_and_value_surjective
#print axioms passive_shift_of_zero_value_stays_in_old_normal_range
#print axioms target_rawShapeLegal_passive_succ_iff
#print axioms target_L3756_to_L3757_passive_shift_legal
#print axioms target_rawShapeLegal_passive_succ_of_z_le_3692
#print axioms target_y48_Z0_Z1_bands_legal

end

end ProximityPrize.SubmissionLower.K0PassiveValueNormalBridge6900
