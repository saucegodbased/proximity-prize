import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum

/-!
# Rank STOP for the 30635 localized identity-core equations

After the 292-node localization, each of the two original recurrence blocks
has 30635 shifts.  Even if all `2 * 30635` rows are independent, they act on
the 81732 coefficients of the original recurrence polynomial.  Hence an
arbitrary such two-block system has kernel dimension at least 20462.

This is much larger than the 7459-dimensional subspace inherited from the
DataEleven leaf.  Thus the dimension/existence of localized equations is not
an independent constraint on the centre.  A useful consumer must prove a
nonzero or transverse projection of the *specified original recurrence
space*, not merely count the available shift equations.
-/

namespace ProximityPrize.SubmissionLower.SharpIdentity292LocalizedEquationRankStop6900

open Polynomial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

noncomputable section

/-- One localized block has 30635 rows, so its kernel on the original
81732-coefficient recurrence box is automatically at least 51097. -/
theorem arbitrary_one_block_localized_kernel_finrank_ge
    (K : Type*) [Field K]
    (tests : Polynomial.degreeLT K 81732 →ₗ[K] (Fin 30635 → K)) :
    51097 ≤ Module.finrank K (LinearMap.ker tests) := by
  have hdomain : Module.finrank K (Polynomial.degreeLT K 81732) = 81732 := by
    simpa using
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K 81732)
  have hcodomain : Module.finrank K (Fin 30635 → K) = 30635 := by
    rw [Module.finrank_pi_fintype]
    simp
  have hrange : Module.finrank K (LinearMap.range tests) ≤ 30635 := by
    calc
      Module.finrank K (LinearMap.range tests) ≤
          Module.finrank K (Fin 30635 → K) :=
        (LinearMap.range tests).finrank_le
      _ = 30635 := hcodomain
  have hsum := tests.finrank_range_add_finrank_ker
  rw [hdomain] at hsum
  omega

/-- Both original/Frobenius blocks together still leave an automatic kernel
of dimension at least `81732 - 2*30635 = 20462`. -/
theorem arbitrary_two_block_localized_kernel_finrank_ge
    (K : Type*) [Field K]
    (tests : Polynomial.degreeLT K 81732 →ₗ[K]
      (Fin 2 → Fin 30635 → K)) :
    20462 ≤ Module.finrank K (LinearMap.ker tests) := by
  have hdomain : Module.finrank K (Polynomial.degreeLT K 81732) = 81732 := by
    simpa using
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K 81732)
  have hcodomain :
      Module.finrank K (Fin 2 → Fin 30635 → K) = 61270 := by
    rw [Module.finrank_pi_fintype]
    simp only [Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
    have hinner : Module.finrank K (Fin 30635 → K) = 30635 := by
      rw [Module.finrank_pi_fintype]
      simp
    rw [hinner]
    norm_num
  have hrange : Module.finrank K (LinearMap.range tests) ≤ 61270 := by
    calc
      Module.finrank K (LinearMap.range tests) ≤
          Module.finrank K (Fin 2 → Fin 30635 → K) :=
        (LinearMap.range tests).finrank_le
      _ = 61270 := hcodomain
  have hsum := tests.finrank_range_add_finrank_ker
  rw [hdomain] at hsum
  omega

/-- The automatic two-block nullity exceeds the inherited target nullity by
13003 dimensions. -/
theorem localized_rank_vacuity_margin :
    2 * 30635 = 61270 ∧
      81732 - 61270 = 20462 ∧
      20462 - 7459 = 13003 ∧
      7459 < 20462 := by
  norm_num

/-- Best actual-degree cancellation from a 7459-dimensional subspace, and
the resulting fixed rational-agreement factorization ledger.  Even this
improves the residual degree only to 51673; it does not improve the direct
pair-intersection cap `W = 149485`. -/
theorem best_low_degree_localized_factor_ledger :
    81731 - (7459 - 1) = 74273 ∧
      74273 + 8328 = 82601 ∧
      82601 + 149485 = 232086 ∧
      232086 - 180413 = 51673 ∧
      180413 ^ 2 + 6594095651 = 261852 * 149485 := by
  norm_num

#print axioms arbitrary_one_block_localized_kernel_finrank_ge
#print axioms arbitrary_two_block_localized_kernel_finrank_ge
#print axioms localized_rank_vacuity_margin
#print axioms best_low_degree_localized_factor_ledger

end
end ProximityPrize.SubmissionLower.SharpIdentity292LocalizedEquationRankStop6900
