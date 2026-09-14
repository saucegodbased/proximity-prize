import HrsU0PCInteriorOrdering6900
import K0FilteredCrtGroebnerDual6900

/-!
# The actual adjacent-seed transpose equations for the high-Y repair

The finite F11 last-killer used complete raw bands `Y^5 Z^z`.  Its proposed
target analogue is `Y^48 Z^z`.  This file writes the literal PC transpose
equation for those bands, separates agreement and error nodes, and records
the exact filtered-CRT consequence.

The key obstruction is structural: multiplication by the passive seed only
shifts the outer polynomial degree.  Thus the `z=0,1,2` bands test three
successive, independent adjoint seed moments.  The honest polynomial seed
target has no order-three relation: an explicit coefficient functional kills
the first three shifts of every nonzero carrier and detects the fourth.
-/

namespace ProximityPrize.SubmissionLower.K0HighYAdjacentSeedStop6900

open scoped BigOperators
open Polynomial
open Order2SourceRank Order2PassiveSeedSource
open HrsU0PCInteriorOrdering6900
open HrsQuotientTopPairing6900
open K0FilteredCrtGroebnerDual6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-! ## Literal primal and transpose identities -/

/-- Raising the external passive-seed exponent is literally multiplication
by the outer polynomial variable.  No contact or PC coordinate is changed. -/
theorem passiveGlobalSourceMonomial_seed_succ
    (a y r s z : Nat) :
    passiveGlobalSourceMonomial K a y r s (z + 1) =
      Polynomial.X * passiveGlobalSourceMonomial K a y r s z := by
  unfold passiveGlobalSourceMonomial
  rw [← Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [pow_succ]
  ring

/-- The same shift after literal node localization. -/
theorem localSeedSubstitution_seed_succ
    (x u0 u1 : K) (a y r s z : Nat) :
    localSeedSubstitution K x u0 u1
        (passiveGlobalSourceMonomial K a y r s (z + 1)) =
      Polynomial.X *
        localSeedSubstitution K x u0 u1
          (passiveGlobalSourceMonomial K a y r s z) := by
  rw [passiveGlobalSourceMonomial_seed_succ]
  simp only [map_mul, localSeedSubstitution_X]

/-- Contact truncation acts coefficientwise in the passive seed, so it
commutes with the seed shift. -/
theorem seedContactTruncation_X_mul (m : Nat) (Q : SeedPoly K) :
    seedContactTruncation K m (Polynomial.X * Q) =
      Polynomial.X * seedContactTruncation K m Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
  | monomial k P =>
      rw [Polynomial.X_mul_monomial,
        seedContactTruncation_monomial,
        seedContactTruncation_monomial,
        Polynomial.X_mul_monomial]

/-- Complete transpose moment of one raw band, with agreement and error
contributions kept separate.  Each node functional may contain every local
contact coordinate; no scalar contact projection is made. -/
def splitBandMoment
    {G E : Type*} [Fintype G] [Fintype E]
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a y r s z : Nat) : K :=
  (∑ i : G,
      etaG i (localSeedSubstitution K (nodesG i) (u0G i) (u1G i)
        (passiveGlobalSourceMonomial K a y r s z))) +
    ∑ i : E,
      etaE i (localSeedSubstitution K (nodesE i) (u0E i) (u1E i)
        (passiveGlobalSourceMonomial K a y r s z))

/-- The literal complete-contact version of `splitBandMoment`.  A genuine
contact dual is evaluated only after the strict weighted contact
truncation. -/
def splitContactBandMoment
    {G E : Type*} [Fintype G] [Fintype E]
    (m : Nat)
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a y r s z : Nat) : K :=
  (∑ i : G,
      etaG i (seedContactTruncation K m
        (localSeedSubstitution K (nodesG i) (u0G i) (u1G i)
          (passiveGlobalSourceMonomial K a y r s z)))) +
    ∑ i : E,
      etaE i (seedContactTruncation K m
        (localSeedSubstitution K (nodesE i) (u0E i) (u1E i)
          (passiveGlobalSourceMonomial K a y r s z)))

/-- The exact PC expansion of the compatible-dual equation.  Notice that
the node-dependent powers of `u0` and `u1` remain inside
`passiveColumnTerm`; they are not replaced by independent shape scalars. -/
theorem splitBandMoment_eq_pc_expansion
    {G E : Type*} [Fintype G] [Fintype E]
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a y r s z : Nat) :
    splitBandMoment nodesG u0G u1G nodesE u0E u1E etaG etaE
        a y r s z =
      (∑ i : G,
        ∑ f ∈ Finset.range (y + 1),
          ∑ h ∈ Finset.range (y - f + 1),
            etaG i
              (passiveColumnTerm K (nodesG i) (u0G i) (u1G i)
                a y r s z f h)) +
      ∑ i : E,
        ∑ f ∈ Finset.range (y + 1),
          ∑ h ∈ Finset.range (y - f + 1),
            etaE i
              (passiveColumnTerm K (nodesE i) (u0E i) (u1E i)
                a y r s z f h) := by
  unfold splitBandMoment
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [localSeedSubstitution_passiveGlobalSourceMonomial_eq_sum]
    simp only [map_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [localSeedSubstitution_passiveGlobalSourceMonomial_eq_sum]
    simp only [map_sum]

/-- PC expansion of the actual contact-truncated transpose equation. -/
theorem splitContactBandMoment_eq_pc_expansion
    {G E : Type*} [Fintype G] [Fintype E]
    (m : Nat)
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a y r s z : Nat) :
    splitContactBandMoment m nodesG u0G u1G nodesE u0E u1E etaG etaE
        a y r s z =
      (∑ i : G,
        ∑ f ∈ Finset.range (y + 1),
          ∑ h ∈ Finset.range (y - f + 1),
            etaG i (seedContactTruncation K m
              (passiveColumnTerm K (nodesG i) (u0G i) (u1G i)
                a y r s z f h))) +
      ∑ i : E,
        ∑ f ∈ Finset.range (y + 1),
          ∑ h ∈ Finset.range (y - f + 1),
            etaE i (seedContactTruncation K m
              (passiveColumnTerm K (nodesE i) (u0E i) (u1E i)
                a y r s z f h)) := by
  unfold splitContactBandMoment
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [localSeedSubstitution_passiveGlobalSourceMonomial_eq_sum, map_sum]
    simp only [map_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [localSeedSubstitution_passiveGlobalSourceMonomial_eq_sum, map_sum]
    simp only [map_sum]

/-- Adjacent raw bands are consecutive Krylov tests for multiplication by
the passive seed.  Crucially, a merely K-linear contact dual does not let the
outer `X` pass through the functional. -/
theorem splitBandMoment_seed_succ
    {G E : Type*} [Fintype G] [Fintype E]
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a y r s z : Nat) :
    splitBandMoment nodesG u0G u1G nodesE u0E u1E etaG etaE
        a y r s (z + 1) =
      (∑ i : G,
        etaG i (Polynomial.X *
          localSeedSubstitution K (nodesG i) (u0G i) (u1G i)
            (passiveGlobalSourceMonomial K a y r s z))) +
      ∑ i : E,
        etaE i (Polynomial.X *
          localSeedSubstitution K (nodesE i) (u0E i) (u1E i)
            (passiveGlobalSourceMonomial K a y r s z)) := by
  unfold splitBandMoment
  simp_rw [localSeedSubstitution_seed_succ]

/-- The consecutive-Krylov identity survives the exact contact truncation. -/
theorem splitContactBandMoment_seed_succ
    {G E : Type*} [Fintype G] [Fintype E]
    (m : Nat)
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a y r s z : Nat) :
    splitContactBandMoment m nodesG u0G u1G nodesE u0E u1E etaG etaE
        a y r s (z + 1) =
      (∑ i : G,
        etaG i (Polynomial.X * seedContactTruncation K m
          (localSeedSubstitution K (nodesG i) (u0G i) (u1G i)
            (passiveGlobalSourceMonomial K a y r s z)))) +
      ∑ i : E,
        etaE i (Polynomial.X * seedContactTruncation K m
          (localSeedSubstitution K (nodesE i) (u0E i) (u1E i)
            (passiveGlobalSourceMonomial K a y r s z))) := by
  unfold splitContactBandMoment
  simp_rw [localSeedSubstitution_seed_succ, seedContactTruncation_X_mul]

/-- Literal PC transpose equations supplied by `Y^48`, `Y^48 Z`, and
`Y^48 Z^2`.  The agreement and error sums are both visible in the result. -/
theorem y48_three_adjacent_band_pc_transpose
    {G E : Type*} [Fintype G] [Fintype E]
    (nodesG u0G u1G : G → K) (nodesE u0E u1E : E → K)
    (etaG : G → Module.Dual K (SeedPoly K))
    (etaE : E → Module.Dual K (SeedPoly K))
    (a : Nat)
    (hbands : ∀ z : Fin 3,
      splitContactBandMoment 47 nodesG u0G u1G nodesE u0E u1E etaG etaE
        a 48 0 0 z.val = 0) :
    ∀ z : Fin 3,
      (∑ i : G,
        ∑ f ∈ Finset.range 49,
          ∑ h ∈ Finset.range (48 - f + 1),
            etaG i
              (seedContactTruncation K 47
                (passiveColumnTerm K (nodesG i) (u0G i) (u1G i)
                  a 48 0 0 z.val f h))) +
      ∑ i : E,
        ∑ f ∈ Finset.range 49,
          ∑ h ∈ Finset.range (48 - f + 1),
            etaE i
              (seedContactTruncation K 47
                (passiveColumnTerm K (nodesE i) (u0E i) (u1E i)
                  a 48 0 0 z.val f h)) = 0 := by
  intro z
  rw [← splitContactBandMoment_eq_pc_expansion]
  exact hbands z

/-! ## What the filtered quotient pairing actually gives -/

theorem y48_cost_and_window :
    m47WeightedCost 48 0 0 = 6291408 ∧
      47 * 180413 - m47WeightedCost 48 0 0 = 2188003 := by
  norm_num [m47WeightedCost]

/-- After the per-contact-shape CRT bridge and the earlier-PC elimination,
the three seed bands bound three *separate* quotient numerators.  There is no
cross-seed recurrence in the conclusion: each seed degree has its own dual
numerator. -/
theorem y48_three_band_filtered_quotient_iff
    (A : K[X]) (q U : Fin 3 → K[X])
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * 180413) :
    (∀ z : Fin 3, ∀ p : K[X], p.natDegree < 2188003 →
      quotientTopPairing A (q z) (U z * p) (47 * 180413) = 0) ↔
    ∀ z : Fin 3,
      ((q z * U z) %ₘ A = 0 ∨
        ((q z * U z) %ₘ A).natDegree < 6291408) := by
  constructor
  · intro hann z
    have hiff := m47_active_shape_cokernel
      A (q z) (U z) 180413 48 0 0 (by norm_num) (by norm_num)
        (by norm_num) hA hAdeg
    apply hiff.mp
    intro p hp
    apply hann z p
    norm_num [m47WeightedCost] at hp ⊢
    exact hp
  · intro hsmall z p hp
    have hiff := m47_active_shape_cokernel
      A (q z) (U z) 180413 48 0 0 (by norm_num) (by norm_num)
        (by norm_num) hA hAdeg
    apply hiff.mpr (by
      simpa only [m47WeightedCost] using hsmall z) p
    norm_num [m47WeightedCost] at hp ⊢
    exact hp

/-! ## Exact three-band non-closure -/

/-- Three consecutive passive-seed tests never imply the fourth for an
arbitrary contact dual.  Coefficient extraction just above the carrier's
leading degree annihilates the first three shifts and detects the fourth.

This is an algebraic obstruction in the honest polynomial seed variable,
not a dimension heuristic or a finite-field rank sample. -/
theorem exists_seed_dual_annihilating_three_shifts_not_fourth
    (V : K[X]) (hV : V ≠ 0) :
    ∃ ell : Module.Dual K K[X],
      ell V = 0 ∧
      ell (Polynomial.X * V) = 0 ∧
      ell (Polynomial.X ^ 2 * V) = 0 ∧
      ell (Polynomial.X ^ 3 * V) ≠ 0 := by
  let d := V.natDegree
  let ell : Module.Dual K K[X] := Polynomial.lcoeff K (d + 3)
  refine ⟨ell, ?_, ?_, ?_, ?_⟩
  · change V.coeff (d + 3) = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by dsimp [d]; omega)
  · change (Polynomial.X * V).coeff (d + 3) = 0
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hV,
      Polynomial.natDegree_X]
    dsimp [d]
    omega
  · change (Polynomial.X ^ 2 * V).coeff (d + 3) = 0
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_mul
      (pow_ne_zero 2 Polynomial.X_ne_zero) hV,
      Polynomial.natDegree_pow, Polynomial.natDegree_X]
    dsimp [d]
    omega
  · change (Polynomial.X ^ 3 * V).coeff (d + 3) ≠ 0
    have hcoeff :
        (V * Polynomial.X ^ 3).coeff (V.natDegree + 3) =
          V.leadingCoeff := by
      rw [Polynomial.coeff_mul_X_pow, Polynomial.coeff_natDegree]
    rw [mul_comm]
    simpa only [d] using
      (hcoeff ▸ Polynomial.leadingCoeff_ne_zero.mpr hV)

/-- All four shifts used by the non-closure witness remain legal under the
target seed cap. -/
theorem y48_four_seed_shifts_fit_target_cap :
    ∀ z : Fin 4, 48 + z.val ≤ 3757 := by
  intro z
  have hz := z.isLt
  omega

#print axioms passiveGlobalSourceMonomial_seed_succ
#print axioms splitBandMoment_eq_pc_expansion
#print axioms splitBandMoment_seed_succ
#print axioms splitContactBandMoment_eq_pc_expansion
#print axioms splitContactBandMoment_seed_succ
#print axioms y48_three_adjacent_band_pc_transpose
#print axioms y48_three_band_filtered_quotient_iff
#print axioms exists_seed_dual_annihilating_three_shifts_not_fourth

end

end ProximityPrize.SubmissionLower.K0HighYAdjacentSeedStop6900
