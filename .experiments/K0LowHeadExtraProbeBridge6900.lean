import K0TerminalDualDetection6900

/-!
# Low-head extra-probe bridge for the K0 terminal route

The corrected terminal detector splits the literal contact coordinates into
the low head `epsilon^0,...,epsilon^43` and the final three coordinates
`epsilon^44,epsilon^45,epsilon^46`.  The target low-head dimension ledger has
enough room for many additional local blocks.  This file records the exact
linear-algebra statement which would turn one *surjective* extra local probe
into the required four-dimensional boundary image.

This deliberately does not infer surjectivity from a dimension inequality.
The missing target theorem is a simultaneous interpolation/CRT statement for
the actual raw source.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadExtraProbeBridge6900

open K0TerminalDualDetection6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K Source OldHead Probe Boundary Tail : Type*}
  [Field K]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup OldHead] [Module K OldHead]
  [AddCommGroup Probe] [Module K Probe]
  [AddCommGroup Boundary] [Module K Boundary]
  [AddCommGroup Tail] [Module K Tail]

/-- Surjectivity onto the old head constraints together with four boundary
coordinates is exactly enough to realize every boundary value while killing
all old head constraints. -/
theorem kernelBoundary_surjective_of_jointBoundary_surjective
    (head : Source →ₗ[K] OldHead)
    (boundary : Source →ₗ[K] Boundary)
    (hjoint : Function.Surjective (head.prod boundary)) :
    Function.Surjective
      (boundary.domRestrict (LinearMap.ker head)) := by
  intro b
  obtain ⟨v, hv⟩ := hjoint (0, b)
  have hhead : head v = 0 := congrArg Prod.fst hv
  have hboundary : boundary v = b := congrArg Prod.snd hv
  exact ⟨⟨v, LinearMap.mem_ker.mpr hhead⟩, hboundary⟩

/-- It is enough to interpolate an entire extra local probe, provided the
four-coordinate boundary readout is a surjective linear quotient of that
probe.  This is the precise bridge suggested by an `(n+1)`-node low-head CRT
construction. -/
theorem kernelBoundary_surjective_of_extraProbe
    (head : Source →ₗ[K] OldHead)
    (probe : Source →ₗ[K] Probe)
    (readout : Probe →ₗ[K] Boundary)
    (hjoint : Function.Surjective (head.prod probe))
    (hreadout : Function.Surjective readout) :
    Function.Surjective
      ((readout.comp probe).domRestrict (LinearMap.ker head)) := by
  intro b
  obtain ⟨t, ht⟩ := hreadout b
  obtain ⟨v, hv⟩ := hjoint (0, t)
  have hhead : head v = 0 := congrArg Prod.fst hv
  have hprobe : probe v = t := congrArg Prod.snd hv
  refine ⟨⟨v, LinearMap.mem_ker.mpr hhead⟩, ?_⟩
  change readout (probe v) = b
  rw [hprobe, ht]

/-- End-to-end abstract consumer: an extra-probe interpolation theorem gives
the low-head boundary surjectivity needed by the quotient-aware terminal
detector.  A complete compatible dual with zero terminal component then has
zero boundary covector. -/
theorem compatibleBoundaryDual_eq_zero_of_extraProbe
    (head : Source →ₗ[K] OldHead)
    (tail : Source →ₗ[K] Tail)
    (probe : Source →ₗ[K] Probe)
    (readout : Probe →ₗ[K] Boundary)
    (hjoint : Function.Surjective (head.prod probe))
    (hreadout : Function.Surjective readout)
    (ell : Module.Dual K Boundary)
    (etaHead : Module.Dual K OldHead)
    (etaTail : Module.Dual K Tail)
    (hcompatible : (readout.comp probe).dualMap ell =
      head.dualMap etaHead + tail.dualMap etaTail)
    (hterminal : etaTail = 0) :
    ell = 0 := by
  apply boundaryDual_eq_zero_of_terminal_eq_zero
    head tail (readout.comp probe) _ ell etaHead etaTail
      hcompatible hterminal
  exact kernelBoundary_surjective_of_extraProbe
    head probe readout hjoint hreadout

#print axioms kernelBoundary_surjective_of_jointBoundary_surjective
#print axioms kernelBoundary_surjective_of_extraProbe
#print axioms compatibleBoundaryDual_eq_zero_of_extraProbe

end

end ProximityPrize.SubmissionLower.K0LowHeadExtraProbeBridge6900
