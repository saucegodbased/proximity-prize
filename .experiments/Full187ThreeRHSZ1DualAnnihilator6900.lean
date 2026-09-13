import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Exact dual obstruction for the Full187 three-RHS plus Z1 gate

Work over the coefficient field after restricting the source to `ker C_G`.
For `D = C_E` and `J = J_YRS`, the three prescribed corrections are not a
surjectivity assertion about `D`.  Their exact dual test is that every error
covector whose pullback is already a `J`-row annihilates the three prescribed
error values.  Independently, the normalized residual-Z row exists exactly
when `z^*` is not an `(D,J)`-row.

This is deliberately source-agnostic.  In the terminal-Schur presentation one
applies it after replacing the source by the terminal-cokernel kernel and
pulling the boundary maps through a correction lift.
-/

namespace ProximityPrize.SubmissionLower.Full187ThreeRHSZ1DualAnnihilator6900

noncomputable section

set_option autoImplicit false

variable {k V E B : Type*}
  [Field k]
  [AddCommGroup V] [Module k V]
  [AddCommGroup E] [Module k E]
  [AddCommGroup B] [Module k B]

/-- Error contact after the Y/R/S-zero restriction. -/
def errorOnYRSKernel
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) :
    LinearMap.ker yrs →ₗ[k] E :=
  error.domRestrict (LinearMap.ker yrs)

/-- The exact annihilator condition for the three distinguished error values.

`error^*(lambda)` is allowed to be a Y/R/S row; precisely those `lambda`
annihilate `error (ker yrs)`.  No basis, rank count, or whole-error-space
surjectivity occurs in this definition. -/
def ThreeRHSAnnihilator
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) (rhs : Fin 3 → E) : Prop :=
  ∀ lambda : Module.Dual k E,
    error.dualMap lambda ∈ LinearMap.range yrs.dualMap →
      ∀ i : Fin 3, lambda (rhs i) = 0

/-- The exact dual form of the normalized residual-Z condition. -/
def Z1DualNoncontainment
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) (z : V →ₗ[k] k) : Prop :=
  z ∉ LinearMap.range (error.prod yrs).dualMap

/-- Three prescribed corrections are equivalent to the smallest possible
dual test on their three error values. -/
theorem threeCorrections_iff_threeRHSAnnihilator
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) (rhs : Fin 3 → E) :
    (∀ i : Fin 3, ∃ h : V, yrs h = 0 ∧ error h = rhs i) ↔
      ThreeRHSAnnihilator error yrs rhs := by
  constructor
  · intro hcorr lambda hlambda i
    obtain ⟨h, hhyrs, hherror⟩ := hcorr i
    rcases hlambda with ⟨mu, hmu⟩
    have heq := LinearMap.congr_fun hmu h
    change mu (yrs h) = lambda (error h) at heq
    simpa [hhyrs, hherror] using heq.symm
  · intro hann i
    have hmem : rhs i ∈ LinearMap.range (errorOnYRSKernel error yrs) := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (LinearMap.range (errorOnYRSKernel error yrs)) (rhs i)).mp
      intro lambda hlambda
      have hker : (errorOnYRSKernel error yrs).dualMap lambda = 0 := by
        apply LinearMap.mem_ker.mp
        rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
        exact hlambda
      have hrow : error.dualMap lambda ∈ LinearMap.range yrs.dualMap := by
        rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
          Submodule.mem_dualAnnihilator]
        intro v hv
        have hpoint := LinearMap.congr_fun hker ⟨v, hv⟩
        simpa [errorOnYRSKernel, LinearMap.dualMap_apply] using hpoint
      exact hann lambda hrow i
    rcases hmem with ⟨h, hh⟩
    exact ⟨h.1, h.2, hh⟩

/-- The residual normalized-Z row is equivalent to one noncontainment test in
the dual row space.  This is the independent fourth condition after the three
RHS corrections; it is not an ambient contact-surjectivity claim. -/
theorem normalizedZ_iff_z1DualNoncontainment
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) (z : V →ₗ[k] k) :
    (∃ v : V, error v = 0 ∧ yrs v = 0 ∧ z v = 1) ↔
      Z1DualNoncontainment error yrs z := by
  constructor
  · rintro ⟨v, herror, hyrs, hz⟩ hmem
    rcases hmem with ⟨lambda, hlambda⟩
    have hpoint := LinearMap.congr_fun hlambda v
    have hp : (error.prod yrs) v = 0 := by
      ext <;> simp [herror, hyrs]
    have : (0 : k) = 1 := by
      simpa [LinearMap.dualMap_apply, hp, hz] using hpoint
    exact zero_ne_one this
  · intro hnoncontain
    change z ∉ LinearMap.range (error.prod yrs).dualMap at hnoncontain
    have hann : z ∉ (LinearMap.ker (error.prod yrs)).dualAnnihilator := by
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      exact hnoncontain
    rw [Submodule.mem_dualAnnihilator] at hann
    push Not at hann
    obtain ⟨v, hv, hz⟩ := hann
    have hpair : (error.prod yrs) v = 0 := LinearMap.mem_ker.mp hv
    have herror : error v = 0 := by
      have hpoint := congrArg Prod.fst hpair
      simpa [LinearMap.prod_apply] using hpoint
    have hyrs : yrs v = 0 := by
      have hpoint := congrArg Prod.snd hpair
      simpa [LinearMap.prod_apply] using hpoint
    refine ⟨(z v)⁻¹ • v, ?_, ?_, ?_⟩
    · rw [map_smul, herror, smul_zero]
    · rw [map_smul, hyrs, smul_zero]
    · rw [map_smul]
      simpa [smul_eq_mul] using inv_mul_cancel₀ hz

/-- The requested Full187 interface, with `rhs i = C_E(F_i)` after the source
has been restricted to `ker C_G`. -/
def ThreeRHSPlusZ1DualGate
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) (z : V →ₗ[k] k)
    (rhs : Fin 3 → E) : Prop :=
  ThreeRHSAnnihilator error yrs rhs ∧ Z1DualNoncontainment error yrs z

/-- Primal and dual forms of the complete `F0/F1/F2` plus normalized-Z
obligation agree exactly. -/
theorem threeCorrections_and_normalizedZ_iff_dualGate
    (error : V →ₗ[k] E) (yrs : V →ₗ[k] B) (z : V →ₗ[k] k)
    (rhs : Fin 3 → E) :
    ((∀ i : Fin 3, ∃ h : V, yrs h = 0 ∧ error h = rhs i) ∧
      ∃ v : V, error v = 0 ∧ yrs v = 0 ∧ z v = 1) ↔
      ThreeRHSPlusZ1DualGate error yrs z rhs := by
  rw [ThreeRHSPlusZ1DualGate,
    threeCorrections_iff_threeRHSAnnihilator,
    normalizedZ_iff_z1DualNoncontainment]

/-- Exact arithmetic used by the low-`E0` compatibility countergate.  It is
intentionally only arithmetic: these leaf summaries contain no map from the
selected scalar family into the Full187 reduced contact cokernel. -/
theorem lowE_rankForty_occupancyThree_numeric_compatibility :
    18414 < 18415 ∧ 39 ≤ 131071 ∧ 2 ≤ 3 ∧
      40 ≤ 253511670984674103 := by
  norm_num

end

end ProximityPrize.SubmissionLower.Full187ThreeRHSZ1DualAnnihilator6900

#print axioms ProximityPrize.SubmissionLower.Full187ThreeRHSZ1DualAnnihilator6900.threeCorrections_iff_threeRHSAnnihilator
#print axioms ProximityPrize.SubmissionLower.Full187ThreeRHSZ1DualAnnihilator6900.normalizedZ_iff_z1DualNoncontainment
#print axioms ProximityPrize.SubmissionLower.Full187ThreeRHSZ1DualAnnihilator6900.threeCorrections_and_normalizedZ_iff_dualGate
#print axioms ProximityPrize.SubmissionLower.Full187ThreeRHSZ1DualAnnihilator6900.lowE_rankForty_occupancyThree_numeric_compatibility
