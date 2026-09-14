import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rank-adaptive line-then-kill interface for the exact-G k=0 route

Suppose a packet subspace forces every compatible boundary covector into one
line.  A single vector in the complete contact kernel on which a generator of
that line is nonzero then makes the complete normal map surjective.  The
vector may equivalently be supplied as a raw repair whose contact image is
already produced by the packet.

The statements make no choice of contact pivots and require no finite-
dimensional hypothesis.  They isolate exactly what the constant-T raw-family
rank certificate proves in its finite chamber, and exactly what remains to be
proved uniformly at m=47.
-/

namespace ProximityPrize.SubmissionLower.K0LineThenKill6900

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

/-- Normal surjectivity is monotone under enlarging the source.  Consequently,
a proved rank-four theorem on the literal raw `{1,R,S}` subspace remains true
when the higher derivative layers needed for source capacity are restored. -/
theorem normal_surjective_mono_submodule
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (small : Submodule K Source)
    (hsmall : Function.Surjective
      (normalOnContactKernel
        (contact.domRestrict small) (boundary.domRestrict small))) :
    Function.Surjective (normalOnContactKernel contact boundary) := by
  intro boundaryValue
  obtain ⟨smallKernel, hvalue⟩ := hsmall boundaryValue
  refine ⟨⟨smallKernel.1.1, ?_⟩, ?_⟩
  · exact smallKernel.2
  · simpa [normalOnContactKernel] using hvalue

/-- Dual-zero implies surjectivity of the normal map, without choosing a
contact rank or pivot basis. -/
theorem normal_surjective_of_compatible_dual_zero
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (hzero : ∀ lambda : Module.Dual K Boundary,
      boundary.dualMap lambda ∈ LinearMap.range contact.dualMap → lambda = 0) :
    Function.Surjective (normalOnContactKernel contact boundary) := by
  by_contra hnot
  have hrange : LinearMap.range (normalOnContactKernel contact boundary) < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, LinearMap.range_eq_top]
    exact hnot
  obtain ⟨lambda, hlambda, hann⟩ :=
    (LinearMap.range (normalOnContactKernel contact boundary)).exists_le_ker_of_lt_top
      hrange
  apply hlambda
  apply hzero lambda
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    Submodule.mem_dualAnnihilator]
  intro source hsource
  have himage :
      (normalOnContactKernel contact boundary) ⟨source, hsource⟩ ∈
        LinearMap.range (normalOnContactKernel contact boundary) :=
    ⟨⟨source, hsource⟩, rfl⟩
  have hvanish := LinearMap.mem_ker.mp (hann himage)
  simpa [normalOnContactKernel, LinearMap.dualMap_apply] using hvanish

/-- If packet compatibility confines all boundary covectors to the line
spanned by `lambda0`, a complete-kernel vector detected by `lambda0` kills
that last line.

This is the invariant form of a rank-three packet plus one Schur direction.
It neither fixes nor assumes the rank of either contact map. -/
theorem compatible_dual_zero_of_packet_line_and_kernel_killer
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (packet : Submodule K Source) (lambda0 : Module.Dual K Boundary)
    (hline : ∀ lambda : Module.Dual K Boundary,
      (boundary.domRestrict packet).dualMap lambda ∈
          LinearMap.range (contact.domRestrict packet).dualMap →
        ∃ a : K, lambda = a • lambda0)
    (killer : Source) (hkillerContact : contact killer = 0)
    (hkillerBoundary : lambda0 (boundary killer) ≠ 0) :
    ∀ lambda : Module.Dual K Boundary,
      boundary.dualMap lambda ∈ LinearMap.range contact.dualMap → lambda = 0 := by
  intro lambda hcompatible
  obtain ⟨mu, hmu⟩ := hcompatible
  have hpacketCompatible :
      (boundary.domRestrict packet).dualMap lambda ∈
        LinearMap.range (contact.domRestrict packet).dualMap := by
    refine ⟨mu, ?_⟩
    ext packetSource
    have hpoint := LinearMap.congr_fun hmu packetSource.1
    simpa [LinearMap.dualMap_apply] using hpoint
  obtain ⟨a, rfl⟩ := hline lambda hpacketCompatible
  have hpoint := LinearMap.congr_fun hmu killer
  have hzero : (a • lambda0) (boundary killer) = 0 := by
    change mu (contact killer) = (a • lambda0) (boundary killer) at hpoint
    simpa [hkillerContact] using hpoint.symm
  have ha : a = 0 := by
    simpa [smul_eq_mul] using
      (mul_eq_zero.mp (show a * lambda0 (boundary killer) = 0 by simpa using hzero)).resolve_right
        hkillerBoundary
  simp [ha]

/-- Relative repair form used by raw-family certificates.  It is enough to
find a raw vector whose contact image agrees with a packet vector and whose
boundary difference is detected by the residual line.  Subtracting the
packet vector produces the kernel killer required above. -/
theorem compatible_dual_zero_of_packet_line_and_relative_killer
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (packet : Submodule K Source) (lambda0 : Module.Dual K Boundary)
    (hline : ∀ lambda : Module.Dual K Boundary,
      (boundary.domRestrict packet).dualMap lambda ∈
          LinearMap.range (contact.domRestrict packet).dualMap →
        ∃ a : K, lambda = a • lambda0)
    (rawRepair : Source) (packetRepair : packet)
    (hcontact : contact rawRepair = contact packetRepair.1)
    (hboundary :
      lambda0 (boundary rawRepair - boundary packetRepair.1) ≠ 0) :
    ∀ lambda : Module.Dual K Boundary,
      boundary.dualMap lambda ∈ LinearMap.range contact.dualMap → lambda = 0 := by
  apply compatible_dual_zero_of_packet_line_and_kernel_killer
    contact boundary packet lambda0 hline (rawRepair - packetRepair.1)
  · simp [map_sub, hcontact]
  · simpa [map_sub] using hboundary

/-- Final compositional form: packet line confinement plus one relative raw
repair implies surjectivity of the complete normal map. -/
theorem normal_surjective_of_packet_line_and_relative_killer
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (packet : Submodule K Source) (lambda0 : Module.Dual K Boundary)
    (hline : ∀ lambda : Module.Dual K Boundary,
      (boundary.domRestrict packet).dualMap lambda ∈
          LinearMap.range (contact.domRestrict packet).dualMap →
        ∃ a : K, lambda = a • lambda0)
    (rawRepair : Source) (packetRepair : packet)
    (hcontact : contact rawRepair = contact packetRepair.1)
    (hboundary :
      lambda0 (boundary rawRepair - boundary packetRepair.1) ≠ 0) :
    Function.Surjective (normalOnContactKernel contact boundary) := by
  apply normal_surjective_of_compatible_dual_zero contact boundary
  exact compatible_dual_zero_of_packet_line_and_relative_killer
    contact boundary packet lambda0 hline rawRepair packetRepair hcontact hboundary

/-! ## Arbitrary-corank packet replacement

The target-ratio controls show that an all-anchor packet can leave three
compatible boundary directions rather than one.  The following version does
not assume a line: any family of complete-kernel vectors which separates the
packet-compatible dual space suffices.
-/

variable {I : Type*}

/-- A packet-compatible dual space of arbitrary dimension is killed by any
family of complete-kernel vectors which separates it. -/
theorem compatible_dual_zero_of_packet_separating_kernel_family
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (packet : Submodule K Source)
    (killer : I → Source) (hkiller : ∀ i, contact (killer i) = 0)
    (hseparate : ∀ lambda : Module.Dual K Boundary,
      (boundary.domRestrict packet).dualMap lambda ∈
          LinearMap.range (contact.domRestrict packet).dualMap →
      (∀ i, lambda (boundary (killer i)) = 0) → lambda = 0) :
    ∀ lambda : Module.Dual K Boundary,
      boundary.dualMap lambda ∈ LinearMap.range contact.dualMap → lambda = 0 := by
  intro lambda hcompatible
  obtain ⟨mu, hmu⟩ := hcompatible
  have hpacketCompatible :
      (boundary.domRestrict packet).dualMap lambda ∈
        LinearMap.range (contact.domRestrict packet).dualMap := by
    refine ⟨mu, ?_⟩
    ext packetSource
    have hpoint := LinearMap.congr_fun hmu packetSource.1
    simpa [LinearMap.dualMap_apply] using hpoint
  apply hseparate lambda hpacketCompatible
  intro i
  have hpoint := LinearMap.congr_fun hmu (killer i)
  change mu (contact (killer i)) = lambda (boundary (killer i)) at hpoint
  simpa [hkiller i] using hpoint.symm

/-- Relative raw-repair form of the arbitrary-corank theorem. -/
theorem compatible_dual_zero_of_packet_separating_relative_family
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (packet : Submodule K Source)
    (rawRepair : I → Source) (packetRepair : I → packet)
    (hcontact : ∀ i, contact (rawRepair i) = contact (packetRepair i).1)
    (hseparate : ∀ lambda : Module.Dual K Boundary,
      (boundary.domRestrict packet).dualMap lambda ∈
          LinearMap.range (contact.domRestrict packet).dualMap →
      (∀ i, lambda (boundary (rawRepair i) - boundary (packetRepair i).1) = 0) →
        lambda = 0) :
    ∀ lambda : Module.Dual K Boundary,
      boundary.dualMap lambda ∈ LinearMap.range contact.dualMap → lambda = 0 := by
  apply compatible_dual_zero_of_packet_separating_kernel_family
    contact boundary packet
    (fun i ↦ rawRepair i - (packetRepair i).1)
  · intro i
    simp [map_sub, hcontact i]
  · intro lambda hpacket hvanish
    apply hseparate lambda hpacket
    intro i
    simpa [map_sub] using hvanish i

/-- Final arbitrary-corank compositional form. -/
theorem normal_surjective_of_packet_separating_relative_family
    (contact : Source →ₗ[K] Contact) (boundary : Source →ₗ[K] Boundary)
    (packet : Submodule K Source)
    (rawRepair : I → Source) (packetRepair : I → packet)
    (hcontact : ∀ i, contact (rawRepair i) = contact (packetRepair i).1)
    (hseparate : ∀ lambda : Module.Dual K Boundary,
      (boundary.domRestrict packet).dualMap lambda ∈
          LinearMap.range (contact.domRestrict packet).dualMap →
      (∀ i, lambda (boundary (rawRepair i) - boundary (packetRepair i).1) = 0) →
        lambda = 0) :
    Function.Surjective (normalOnContactKernel contact boundary) := by
  apply normal_surjective_of_compatible_dual_zero contact boundary
  exact compatible_dual_zero_of_packet_separating_relative_family
    contact boundary packet rawRepair packetRepair hcontact hseparate

/-! ## Exact target arithmetic for the finite killer's literal analogue -/

/-- At m=47 the raw `Y^(m+1)` band has this many legal X coefficients. -/
theorem target_y48_band_width :
    47 * 180413 - 131071 * 48 = 2188003 := by
  norm_num

/-- The two adjacent passive-seed bands contain 4,376,006 coefficients. -/
theorem target_y48_two_band_columns :
    2 * (47 * 180413 - 131071 * 48) = 4376006 := by
  norm_num

/-- The pair fits the target active and total caps. -/
theorem target_y48_two_band_shape_legal :
    48 ≤ 64 ∧ 48 + 1 ≤ 3757 ∧ 0 ≤ 16 ∧ 0 ≤ 8 := by
  norm_num

/-- Even charging only the 81,731 error nodes at the elementary two-band
local cap `2m=94`, this family has a 3,306,708 coefficient deficit.  Thus its
small exact circuit cannot be promoted by a standalone dimension count. -/
theorem target_y48_two_band_error_only_capacity_red :
    4376006 - 81731 * 94 = -(3306708 : ℤ) := by
  norm_num

#print axioms normal_surjective_of_compatible_dual_zero
#print axioms normal_surjective_mono_submodule
#print axioms compatible_dual_zero_of_packet_line_and_kernel_killer
#print axioms compatible_dual_zero_of_packet_line_and_relative_killer
#print axioms normal_surjective_of_packet_line_and_relative_killer
#print axioms compatible_dual_zero_of_packet_separating_kernel_family
#print axioms compatible_dual_zero_of_packet_separating_relative_family
#print axioms normal_surjective_of_packet_separating_relative_family
#print axioms target_y48_band_width
#print axioms target_y48_two_band_error_only_capacity_red

end

end ProximityPrize.SubmissionLower.K0LineThenKill6900
