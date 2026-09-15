import K0RawIndexContactCore6900
import Mathlib.Tactic.NormNum

/-!
# Projection mismatch: the known three axes are not low-head-kernel axes

The existing `S,R,Z` three-axis construction is for the projection retaining
epsilon orders at least three.  The corrected terminal split instead retains
the low head `epsilon^0,...,epsilon^43`.  This file pins the mismatch to the
literal target K0 raw source: its legal pure `S,R,Z` basis vectors have
nonzero low-head contact already at epsilon zero.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadRankThreeSpliceRed6900

open K0RawIndexContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

def lowHeadProjection : Target K →ₗ[K] Target K :=
  (Polynomial.modByMonicHom (Polynomial.X ^ 44 : Target K)).restrictScalars K

def targetLowHead (x u0 u1 : K) :
    K0RawSource K 180413 →ₗ[K] Target K :=
  lowHeadProjection.comp (k0RawLocalContact 180413 x u0 u1)

def targetOldLowHead
    {I : Type*} [Fintype I] (nodes u0 u1 : I → K) :
    K0RawSource K 180413 →ₗ[K] (I → Target K) :=
  LinearMap.pi (fun i ↦ targetLowHead (nodes i) (u0 i) (u1 i))

def targetFreshBoundary
    (xStar u0Star u1Star : K)
    (readout : Target K →ₗ[K] (Fin 4 → K)) :
    K0RawSource K 180413 →ₗ[K] (Fin 4 → K) :=
  readout.comp (targetLowHead xStar u0Star u1Star)

/-- The exact premise route F would have needed but which no current target
theorem supplies: the literal low-head kernel covers one named boundary
hyperplane. -/
def TargetRankThreeHyperplane
    {I : Type*} [Fintype I]
    (nodes u0 u1 : I → K) (xStar u0Star u1Star : K)
    (readout : Target K →ₗ[K] (Fin 4 → K))
    (ell : Module.Dual K (Fin 4 → K)) : Prop :=
  ∀ b, ell b = 0 →
    ∃ v : LinearMap.ker (targetOldLowHead nodes u0 u1),
      targetFreshBoundary xStar u0Star u1Star readout v.1 = b

/-- Conditional on the preceding hyperplane, this is the single remaining
syndrome.  It is stated directly on the literal target low-head kernel. -/
def TargetOneSyndrome
    {I : Type*} [Fintype I]
    (nodes u0 u1 : I → K) (xStar u0Star u1Star : K)
    (readout : Target K →ₗ[K] (Fin 4 → K))
    (ell : Module.Dual K (Fin 4 → K)) : Prop :=
  ∃ v : LinearMap.ker (targetOldLowHead nodes u0 u1),
    ell (targetFreshBoundary xStar u0Star u1Star readout v.1) ≠ 0

/-- Coordinate-free rank-three-plus-one linear algebra.  This theorem is
useful only after the rank-three hyperplane premise has actually been proved
for the same map. -/
theorem surjective_of_hyperplane_and_oneSyndrome
    {V B : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup B] [Module K B]
    (normal : V →ₗ[K] B) (ell : Module.Dual K B)
    (hhyperplane : ∀ b, ell b = 0 → ∃ v, normal v = b)
    (hone : ∃ v, ell (normal v) ≠ 0) :
    Function.Surjective normal := by
  intro b
  obtain ⟨v, hv⟩ := hone
  let a : K := ell b / ell (normal v)
  let b0 : B := b - a • normal v
  have hb0 : ell b0 = 0 := by
    dsimp only [b0, a]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  obtain ⟨u, hu⟩ := hhyperplane b0 hb0
  refine ⟨u + a • v, ?_⟩
  rw [map_add, map_smul, hu]
  dsimp only [b0]
  abel

def pureSIndex : K0RawIndex 180413 :=
  ⟨⟨1, by norm_num⟩,
    ⟨⟨0, by norm_num⟩,
      ⟨⟨0, by norm_num [yCount, budget, k0Cutoff]⟩,
        (⟨0, by norm_num [budget, k0Cutoff]⟩,
          ⟨0, by norm_num⟩)⟩⟩⟩

def pureRIndex : K0RawIndex 180413 :=
  ⟨⟨0, by norm_num⟩,
    ⟨⟨1, by norm_num⟩,
      ⟨⟨0, by norm_num [yCount, budget, k0Cutoff]⟩,
        (⟨0, by norm_num [budget, k0Cutoff]⟩,
          ⟨0, by norm_num⟩)⟩⟩⟩

def pureZIndex : K0RawIndex 180413 :=
  ⟨⟨0, by norm_num⟩,
    ⟨⟨0, by norm_num⟩,
      ⟨⟨0, by norm_num [yCount, budget, k0Cutoff]⟩,
        (⟨0, by norm_num [budget, k0Cutoff]⟩,
          ⟨1, by norm_num⟩)⟩⟩⟩

theorem pureSIndex_exponent :
    exponent pureSIndex = Finsupp.single 1 1 := by
  ext i
  fin_cases i <;> simp [pureSIndex, exponent]

theorem pureRIndex_exponent :
    exponent pureRIndex = Finsupp.single 3 1 := by
  ext i
  fin_cases i <;> simp [pureRIndex, exponent]

theorem pureZIndex_exponent :
    exponent pureZIndex = Finsupp.single 4 1 := by
  ext i
  fin_cases i <;> simp [pureZIndex, exponent]

theorem localize_pureS (x u0 u1 : K) :
    localize x u0 u1
        (MvPolynomial.monomial (exponent pureSIndex) 1) =
      MvPolynomial.X 1 := by
  rw [pureSIndex_exponent]
  rw [← MvPolynomial.X_pow_eq_monomial]
  simp [localize]

theorem flatEquiv_pureS :
    flatEquiv (K := K) (MvPolynomial.X 1) =
      Polynomial.C Polynomial.X := by
  change Polynomial.map
      (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 4
        (MvPolynomial.X ((0 : Fin 4).succ))) =
    Polynomial.C Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  exact MvPolynomial.finSuccEquiv_X_zero

theorem contact_pureS :
    contact (K := K) (Polynomial.C Polynomial.X) =
      Polynomial.C (MvPolynomial.X 0) := by
  change Polynomial.eval₂ innerEval.toRingHom Polynomial.X
      (Polynomial.C Polynomial.X) = _
  rw [Polynomial.eval₂_C]
  change Polynomial.eval₂ baseEval.toRingHom
      (Polynomial.C (MvPolynomial.X 0))
      Polynomial.X = _
  rw [Polynomial.eval₂_X]

theorem targetLowHead_pureS (x u0 u1 : K) :
    targetLowHead x u0 u1 (k0RawBasis (K := K) 180413 pureSIndex) =
      Polynomial.C (MvPolynomial.X 0) := by
  rw [targetLowHead, LinearMap.comp_apply, k0RawLocalContact_basis]
  rw [localize_pureS]
  rw [flatEquiv_pureS]
  change
    (contact (K := K)
      ((Polynomial.C Polynomial.X : Jet K) %ₘ Polynomial.X ^ 47) %ₘ
        Polynomial.X ^ 47) %ₘ Polynomial.X ^ 44 =
      Polynomial.C (MvPolynomial.X 0)
  have hsourceMod :
      (Polynomial.C Polynomial.X : Jet K) %ₘ Polynomial.X ^ 47 =
        Polynomial.C Polynomial.X := by
    apply (Polynomial.modByMonic_eq_self_iff
      (Polynomial.monic_X_pow 47)).2
    simp
  rw [hsourceMod, contact_pureS]
  have hcontactMod :
      (Polynomial.C (MvPolynomial.X 0) : Target K) %ₘ
          Polynomial.X ^ 47 = Polynomial.C (MvPolynomial.X 0) := by
    apply (Polynomial.modByMonic_eq_self_iff
      (Polynomial.monic_X_pow 47)).2
    simp
  rw [hcontactMod]
  apply (Polynomial.modByMonic_eq_self_iff
    (Polynomial.monic_X_pow 44)).2
  simp

/-- The first purported automatic axis is not in the corrected low-head
kernel.  This is a literal target-source statement, not a dimension audit. -/
theorem targetLowHead_pureS_ne_zero (x u0 u1 : K) :
    targetLowHead x u0 u1
      (k0RawBasis (K := K) 180413 pureSIndex) ≠ 0 := by
  rw [targetLowHead_pureS]
  exact Polynomial.C_ne_zero.mpr (MvPolynomial.X_ne_zero 0)

theorem pureS_not_mem_targetLowHead_ker (x u0 u1 : K) :
    k0RawBasis (K := K) 180413 pureSIndex ∉
      LinearMap.ker (targetLowHead x u0 u1) := by
  rw [LinearMap.mem_ker]
  exact targetLowHead_pureS_ne_zero x u0 u1

/-! ## First error-side equation for the four osculating carriers -/

/-- At an error node write `h = H(beta)`, `delta` for the nonzero value
mismatch, and use the local monomial rows `(1,R,S,W)`.  The epsilon-zero
coefficients of

`H^43*A, H^42*B1, H^41*B2, H^44*W`

are triangular.  These four rows alone force all four carrier coefficients
to vanish.  Thus the carriers are not old-low-head kernel vectors: the very
first recurrence equation must add four independently prescribed error-value
corrections. -/
theorem error_epsZero_four_carriers_forced_zero
    (h h1 h2 delta eta r0 rW s0 sW cA cB1 cB2 cW : K)
    (hh : h ≠ 0) (hdelta : delta ≠ 0) (htwo : (2 : K) ≠ 0)
    (hconst :
      cA * h ^ 43 * delta +
        cB1 * h ^ 42 * (h * r0 - h1 * delta) +
        cB2 * h ^ 41 *
          (h ^ 2 * s0 - 2 * h * h1 * r0 +
            (2 * h1 ^ 2 - h * h2) * delta) = 0)
    (hR : cB1 * h ^ 43 + cB2 * h ^ 41 * (-2 * h * h1) = 0)
    (hS : cB2 * (2 * h ^ 43) = 0)
    (hW :
      cA * h ^ 43 * eta +
        cB1 * h ^ 42 * (h * rW - h1 * eta) +
        cB2 * h ^ 41 *
          (h ^ 2 * sW - 2 * h * h1 * rW +
            (2 * h1 ^ 2 - h * h2) * eta) +
        cW * h ^ 44 = 0) :
    cA = 0 ∧ cB1 = 0 ∧ cB2 = 0 ∧ cW = 0 := by
  have hp43 : h ^ 43 ≠ 0 := pow_ne_zero 43 hh
  have hp44 : h ^ 44 ≠ 0 := pow_ne_zero 44 hh
  have hcB2 : cB2 = 0 := by
    exact (mul_eq_zero.mp hS).resolve_right (mul_ne_zero htwo hp43)
  have hcB1 : cB1 = 0 := by
    rw [hcB2] at hR
    simp only [zero_mul, add_zero] at hR
    exact (mul_eq_zero.mp hR).resolve_right hp43
  have hcA : cA = 0 := by
    rw [hcB1, hcB2] at hconst
    simp only [zero_mul, add_zero] at hconst
    have hproduct : cA * (h ^ 43 * delta) = 0 := by
      simpa only [mul_assoc] using hconst
    exact (mul_eq_zero.mp hproduct).resolve_right
      (mul_ne_zero hp43 hdelta)
  have hcW : cW = 0 := by
    rw [hcA, hcB1, hcB2] at hW
    simp only [zero_mul, zero_add, add_zero] at hW
    exact (mul_eq_zero.mp hW).resolve_right hp44
  exact ⟨hcA, hcB1, hcB2, hcW⟩

/-- The first error-value CRT repair of each minimal carrier fits the target
X taper.  This is only the first epsilon equation, not a 44-layer proof. -/
theorem target_first_error_value_repairs_fit :
    43 * 180413 + 131071 + 81731 < 47 * 180413 ∧
      43 * 180413 + 131070 + 81731 < 47 * 180413 ∧
      43 * 180413 + 131069 + 81731 < 47 * 180413 ∧
      44 * 180413 + 81731 < 47 * 180413 := by
  norm_num

/-- Two exact cliffs any proposed 44-layer schedule must avoid: locator
grade 14 is illegal on `S*R*Y^43`, and positive locator grade is illegal on
`Y^64`.  The present audit does not claim that every schedule hits a cliff. -/
theorem target_known_error_value_recurrence_cliffs :
    47 * 180413 - 43 * 131071 - 131070 - 131069 <
        14 * 180413 + 81731 ∧
      47 * 180413 - 64 * 131071 < 180413 + 81731 := by
  norm_num

#print axioms targetLowHead_pureS
#print axioms targetLowHead_pureS_ne_zero
#print axioms pureS_not_mem_targetLowHead_ker
#print axioms error_epsZero_four_carriers_forced_zero
#print axioms target_first_error_value_repairs_fit
#print axioms target_known_error_value_recurrence_cliffs

end

end ProximityPrize.SubmissionLower.K0LowHeadRankThreeSpliceRed6900
