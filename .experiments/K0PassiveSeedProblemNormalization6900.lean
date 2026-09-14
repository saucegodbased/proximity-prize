import ConstantDirectionShearExactStrata6900
import K0PassiveSeedTranslationAlgebra6900
import Mathlib.Tactic.FinCases

/-!
# Problem-level normalization of the passive boundary seed

The raw-source coordinate translation is useful only if it respects the
actual bad-agreement input.  This file supplies that adapter.  Shear the
constant received row by `c*u1` and replace the seed `gamma` by `gamma-c`.
The selected polynomial and its agreement set do not change.  Moreover, on
any bad selected agreement set the direction row `u1` is itself bad, so the
sheared pair retains a bad-row witness.

Taking `c=gamma-1` therefore reduces every input to boundary seed one.  This
is still only a normalization theorem; the cap-3757 relative connecting-map
surjectivity must be proved for the normalized input.
-/

namespace ProximityPrize.SubmissionLower.K0PassiveSeedProblemNormalization6900

open Polynomial
open ProximityPrize.Benchmark
open ConstantDirectionShearExactStrata6900
open K0PassiveSeedTranslationAlgebra6900

noncomputable section
set_option autoImplicit false

variable {I K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field K] [Fintype K] [DecidableEq K]

/-- Shear only the constant row of the received affine line. -/
def shearConstantRow (c : K) (U : Fin 2 → I → K) : Fin 2 → I → K
  | 0, i => U 0 i + c * U 1 i
  | 1, i => U 1 i

@[simp] theorem shearConstantRow_zero
    (c : K) (U : Fin 2 → I → K) (i : I) :
    shearConstantRow c U 0 i = U 0 i + c * U 1 i := rfl

@[simp] theorem shearConstantRow_one
    (c : K) (U : Fin 2 → I → K) (i : I) :
    shearConstantRow c U 1 i = U 1 i := rfl

/-- Pointwise agreement is unchanged by the simultaneous row/seed shear. -/
theorem shearConstantRow_agreement_iff
    (domain : I ↪ K) (U : Fin 2 → I → K) (P : K[X])
    (gamma c : K) (i : I) :
    P.eval (domain i) =
        shearConstantRow c U 0 i +
          (gamma - c) * shearConstantRow c U 1 i ↔
      P.eval (domain i) = U 0 i + gamma * U 1 i := by
  simp only [shearConstantRow_zero, shearConstantRow_one]
  rw [receivedLine_seed_translation]

/-- Hence the same supplied agreement set remains an agreement set. -/
theorem shearConstantRow_preserves_agreement
    (domain : I ↪ K) (U : Fin 2 → I → K) (P : K[X])
    (A : Finset I) (gamma c : K)
    (hagreement : ∀ i ∈ A,
      P.eval (domain i) = U 0 i + gamma * U 1 i) :
    ∀ i ∈ A,
      P.eval (domain i) =
        shearConstantRow c U 0 i +
          (gamma - c) * shearConstantRow c U 1 i := by
  intro i hi
  exact (shearConstantRow_agreement_iff domain U P gamma c i).mpr
    (hagreement i hi)

/-- Once the unchanged direction row is known bad, it is also a bad-row
witness for the sheared received pair. -/
theorem shearConstantRow_pair_bad_of_direction_bad
    (domain : I ↪ K) (U : Fin 2 → I → K) (A : Finset I)
    (c : K) (w : Nat)
    (hbad : LinearCode.projectedWord (U 1) A ∉
      LinearCode.projectedCodeSubmod
        (ReedSolomon.code domain (w + 1)) A) :
  ∃ j : Fin 2,
      LinearCode.projectedWord (shearConstantRow c U j) A ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code domain (w + 1)) A := by
  refine ⟨1, ?_⟩
  have hrow : shearConstantRow c U 1 = U 1 := by
    funext i
    rfl
  rw [hrow]
  exact hbad

/-- Complete semantic normalization: every bad agreement instance is
equivalent to one with the same selected polynomial, the same agreement set,
the same bad direction row, and boundary seed exactly one. -/
theorem exists_seed_one_bad_agreement_normalization
    (domain : I ↪ K) (w : Nat) (U : Fin 2 → I → K)
    (A : Finset I) (gamma : K) (P : K[X])
    (hPdegree : P.natDegree ≤ w)
    (hagreement : ∀ i ∈ A,
      P.eval (domain i) = U 0 i + gamma * U 1 i)
    (hpairbad : ∃ j : Fin 2,
      LinearCode.projectedWord (U j) A ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code domain (w + 1)) A) :
    ∃ U' : Fin 2 → I → K,
      (∀ i, U' 1 i = U 1 i) ∧
      (∀ i ∈ A, P.eval (domain i) = U' 0 i + 1 * U' 1 i) ∧
      (∃ j : Fin 2,
        LinearCode.projectedWord (U' j) A ∉
          LinearCode.projectedCodeSubmod
            (ReedSolomon.code domain (w + 1)) A) := by
  let c : K := gamma - 1
  let U' := shearConstantRow c U
  have hdirection := direction_bad_of_pair_bad_and_selected
    domain U A P gamma w hPdegree hagreement hpairbad
  refine ⟨U', ?_, ?_, ?_⟩
  · intro i
    simp [U', shearConstantRow]
  · intro i hi
    have hshear := shearConstantRow_preserves_agreement
      domain U P A gamma c hagreement i hi
    have hseed : gamma - c = 1 := by
      simp [c]
    simpa only [U', hseed] using hshear
  · exact shearConstantRow_pair_bad_of_direction_bad
      domain U A c w hdirection

#print axioms shearConstantRow_agreement_iff
#print axioms shearConstantRow_preserves_agreement
#print axioms shearConstantRow_pair_bad_of_direction_bad
#print axioms exists_seed_one_bad_agreement_normalization

end

end ProximityPrize.SubmissionLower.K0PassiveSeedProblemNormalization6900
