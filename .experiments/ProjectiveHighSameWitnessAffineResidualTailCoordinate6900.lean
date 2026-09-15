import CanonicalHighTailCoefficientRank6900

/-!
# A same-witness affine coordinate in an agreement-residual high tail

This small adapter isolates the exact algebra used on the enriched
sharp/projective/high-E leaf without reopening that very large record during
experimentation.  Projective highness makes the canonical `U 1` interpolant
have a nonzero coefficient at some degree at least `133120`.  If the existing
agreement-residual theorem is supplied on the same retained family, then at
that one fixed coefficient every locator-residual product has value

`A + gamma * B`, with `B != 0`.

The result is deliberately only a producer.  It does not assert that this
coordinate belongs to the shallow source ideal or controls a different graph
coordinate.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighSameWitnessAffineResidualTailCoordinate6900

open Polynomial
open LowReceivedDirectionScalarSplit1331196900
open UniversalProjectiveHighDirectionEndpointCut6900
open CanonicalHighTailCoefficientRank6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- A projective-high two-row word plus the already-proved same-family
high-coefficient residual identity yields one fixed affine injective residual
coordinate.  In the exact leaf application, `H gamma` is its actual agreement
locator and `Good` is the sharp retained family. -/
theorem exists_same_witness_affine_residual_tail_coordinate
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K)
    (Good : Finset K) (H : K → K[X])
    (hhigh : CanonicalHighTailDirectionIndependent nodes U)
    (hresidual : ∀ gamma ∈ Good, ∃ R : K[X],
      R ≠ 0 ∧ R.natDegree ≤ 81730 ∧
      ∀ k : Nat, 131071 < k →
        (H gamma * R).coeff k =
          (canonicalReceivedInterpolant nodes U 0).coeff k +
            gamma * (canonicalReceivedInterpolant nodes U 1).coeff k) :
    let V0 : K[X] := canonicalReceivedInterpolant nodes U 0
    let V1 : K[X] := canonicalReceivedInterpolant nodes U 1
    ∃ k : Nat,
      133120 ≤ k ∧
      V1.coeff k ≠ 0 ∧
      Function.Injective (fun gamma : K ↦
        V0.coeff k + gamma * V1.coeff k) ∧
      ∀ gamma ∈ Good, ∃ R : K[X],
        R ≠ 0 ∧ R.natDegree ≤ 81730 ∧
        (H gamma * R).coeff k = V0.coeff k + gamma * V1.coeff k := by
  classical
  dsimp only
  let V0 : K[X] := canonicalReceivedInterpolant nodes U 0
  let V1 : K[X] := canonicalReceivedInterpolant nodes U 1
  have hV1degree : 133120 ≤ V1.natDegree := by
    have hdirection := hhigh 0 1 (Or.inr one_ne_zero)
    simpa only [zero_mul, one_mul, zero_add, V1,
      canonicalReceivedInterpolant] using hdirection
  have hV1ne : V1 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hV1degree
    omega
  let k : Nat := V1.natDegree
  let A : K := V0.coeff k
  let B : K := V1.coeff k
  have hB : B ≠ 0 := by
    dsimp only [B, k, V1]
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hV1ne
  have hinj : Function.Injective (fun gamma : K ↦ A + gamma * B) := by
    intro gamma delta heq
    have hmul : gamma * B = delta * B := add_left_cancel heq
    exact mul_right_cancel₀ hB hmul
  refine ⟨k, hV1degree, hB, ?_, ?_⟩
  · simpa only [A, B] using hinj
  intro gamma hgamma
  obtain ⟨R, hRne, hRdegree, hcoeff⟩ := hresidual gamma hgamma
  refine ⟨R, hRne, hRdegree, ?_⟩
  have hk : 131071 < k := by omega
  simpa only [V0, V1] using hcoeff k hk

#print axioms exists_same_witness_affine_residual_tail_coordinate

end
end ProximityPrize.SubmissionLower.ProjectiveHighSameWitnessAffineResidualTailCoordinate6900
