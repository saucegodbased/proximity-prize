import K0RawIndexContactCore6900
import Mathlib.Tactic.NormNum

/-!
# The minimal four-row CRT target for the K0 low head

The finite extra-node experiment proves independence of the entire fresh
low-head image.  The terminal consumer does not need that much: it needs only
the four boundary readout coordinates modulo the old low-head constraints.

This file gives the exact basis-free equivalence and instantiates the literal
target maps.  It intentionally leaves the target interpolation statement as
a named proposition; a source-dimension inequality is not used as a proof.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadFourRowCRT6900

open K0RawIndexContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

variable {K Source Head Boundary : Type*}
  [Field K]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Head] [Module K Head]
  [AddCommGroup Boundary] [Module K Boundary]

/-- Once the old head codomain is replaced by its actual range, joint
surjectivity with a small readout is *equivalent* to realizing that readout
on the old-head kernel.  This is the precise four-row theorem needed by the
terminal detector. -/
theorem rangeHead_prod_surjective_iff_kernelReadout_surjective
    (head : Source →ₗ[K] Head) (readout : Source →ₗ[K] Boundary) :
    Function.Surjective (head.rangeRestrict.prod readout) ↔
      Function.Surjective (readout.domRestrict (LinearMap.ker head)) := by
  constructor
  · intro hjoint b
    obtain ⟨v, hv⟩ := hjoint (0, b)
    have hhead : head v = 0 := by
      have h := congrArg (fun x : head.range × Boundary => x.1.val) hv
      simpa using h
    have hreadout : readout v = b := congrArg Prod.snd hv
    exact ⟨⟨v, LinearMap.mem_ker.mpr hhead⟩, hreadout⟩
  · intro hkernel target
    rcases target with ⟨h, b⟩
    obtain ⟨v, hv⟩ := h.property
    obtain ⟨z, hz⟩ := hkernel (b - readout v)
    refine ⟨v + z.1, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change head (v + (z : Source)) = (h : Head)
      rw [LinearMap.map_add, z.property, add_zero, hv]
    · change readout (v + (z : Source)) = b
      change readout (z : Source) = b - readout v at hz
      rw [LinearMap.map_add, hz]
      abel

/-- The finite experiment's stronger range-relative full-probe statement
implies the four-row statement whenever the local readout is onto.  The
converse is neither asserted nor needed. -/
theorem fourRow_surjective_of_fullProbe_surjective
    {Probe : Type*} [AddCommGroup Probe] [Module K Probe]
    (head : Source →ₗ[K] Head) (probe : Source →ₗ[K] Probe)
    (readout : Probe →ₗ[K] Boundary)
    (hjoint : Function.Surjective
      (head.rangeRestrict.prod probe.rangeRestrict))
    (hreadout : Function.Surjective
      (readout.domRestrict probe.range)) :
    Function.Surjective
      (head.rangeRestrict.prod (readout.comp probe)) := by
  intro target
  rcases target with ⟨h, b⟩
  obtain ⟨p, hp⟩ := hreadout b
  obtain ⟨v, hv⟩ := hjoint (h, p)
  refine ⟨v, ?_⟩
  apply Prod.ext
  · change head.rangeRestrict v = h
    exact congrArg Prod.fst hv
  · have hprobe : probe v = p.1 := by
      have h := congrArg (fun x : head.range × probe.range => x.2.val) hv
      simpa using h
    change readout (probe v) = b
    change readout (p : Probe) = b at hp
    rw [hprobe, hp]

/-! ## Literal target maps -/

/-- Projection to the corrected low head `epsilon^0,...,epsilon^43`. -/
def lowHeadProjection :
    Target K →ₗ[K] Target K :=
  (Polynomial.modByMonicHom (Polynomial.X ^ 44 : Target K)).restrictScalars K

/-- One literal m47 target low-head block at a node. -/
def targetRawLocalLowHead
    (x u0 u1 : K) :
    K0RawSource K 180413 →ₗ[K] Target K :=
  lowHeadProjection.comp (k0RawLocalContact 180413 x u0 u1)

/-- The old all-node target low head. -/
def targetRawOldLowHead
    {I : Type*} [Fintype I] (nodes u0 u1 : I → K) :
    K0RawSource K 180413 →ₗ[K]
      (I → Target K) :=
  LinearMap.pi (fun i ↦ targetRawLocalLowHead (nodes i) (u0 i) (u1 i))

/-- The exact target-specific missing theorem, parameterized only by the
four-dimensional compatible-node readout supplied by the local calculation.
It asks for four rows modulo the actual old image, not the 213,740,910-row
fresh local image. -/
def TargetFourRowCRT
    {I : Type*} [Fintype I]
    (nodes u0 u1 : I → K) (xStar u0Star u1Star : K)
    (readout : Target K →ₗ[K] (Fin 4 → K)) : Prop :=
  Function.Surjective
    ((targetRawOldLowHead nodes u0 u1).rangeRestrict.prod
      (readout.comp (targetRawLocalLowHead xStar u0Star u1Star)))

/-! ## Why the one-shot X-only Hermite construction is not the proof -/

theorem target_depth44_allNode_X_only_stop :
    47 * 180413 = 8479411 ∧
      262144 * 44 = 11534336 ∧
      8479411 < 11534336 ∧
      11534336 - 8479411 = 3054925 ∧
      (262144 + 1) * 44 = 11534380 ∧
      11534380 - 8479411 = 3054969 := by
  norm_num

#print axioms rangeHead_prod_surjective_iff_kernelReadout_surjective
#print axioms fourRow_surjective_of_fullProbe_surjective
#print axioms target_depth44_allNode_X_only_stop

end

end ProximityPrize.SubmissionLower.K0LowHeadFourRowCRT6900
