import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Universal three-shape local connector

For an arbitrary local graph factor `P`, project the three raw columns

`P^m`, `P^m * R`, `P^m * S`

to the constant, `R`, and `S` coefficients.  The resulting matrix is lower
triangular with diagonal `constantCoeff(P)^m`.  This is the local algebraic
block behind the observed `{pure,R,S}` connector.  It deliberately says
nothing about global coefficient windows, agreement CRT, or confluence of
successive passive-seed shifts.
-/

namespace ProximityPrize.SubmissionLower.ThreeShapeLocalConnector6900

open Matrix MvPolynomial

noncomputable section

set_option autoImplicit false
set_option Elab.async false

variable {A : Type*} [CommRing A]

abbrev LocalRS (A : Type*) [CommRing A] := MvPolynomial (Fin 2) A

def rowExponent : Fin 3 → (Fin 2 →₀ Nat) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1]

def columnFactor (A : Type*) [CommRing A] : Fin 3 → LocalRS A :=
  ![1, X 0, X 1]

def connectorMatrix (P : LocalRS A) (m : Nat) : Matrix (Fin 3) (Fin 3) A :=
  fun i j => coeff (rowExponent i) (P ^ m * columnFactor A j)

theorem coeff_zero_pow (P : LocalRS A) (m : Nat) :
    coeff 0 (P ^ m) = constantCoeff P ^ m := by
  change constantCoeff (P ^ m) = _
  exact map_pow constantCoeff P m

theorem coeff_zero_mul_X (P : LocalRS A) (i : Fin 2) :
    coeff 0 (P * X i) = 0 := by
  rw [coeff_mul_X']
  simp

theorem coeff_other_mul_X (P : LocalRS A) (i j : Fin 2) (hij : i ≠ j) :
    coeff (Finsupp.single j 1) (P * X i) = 0 := by
  rw [coeff_mul_X']
  simp [hij]

theorem coeff_same_mul_X (P : LocalRS A) (i : Fin 2) :
    coeff (Finsupp.single i 1) (P * X i) = coeff 0 P := by
  rw [coeff_mul_X']
  simp

theorem connectorMatrix_diagonal (P : LocalRS A) (m : Nat) (i : Fin 3) :
    connectorMatrix P m i i = constantCoeff P ^ m := by
  fin_cases i <;>
    simp [connectorMatrix, rowExponent, columnFactor, coeff_zero_pow,
      coeff_same_mul_X]

theorem connectorMatrix_above_zero (P : LocalRS A) (m : Nat)
    (i j : Fin 3) (hij : i < j) :
    connectorMatrix P m i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [connectorMatrix, rowExponent, columnFactor,
      coeff_zero_mul_X, coeff_other_mul_X]

theorem connectorMatrix_det (P : LocalRS A) (m : Nat) :
    (connectorMatrix P m).det = (constantCoeff P ^ m) ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [connectorMatrix, rowExponent, columnFactor, coeff_zero_pow,
    coeff_zero_mul_X, coeff_other_mul_X, coeff_same_mul_X, pow_succ', mul_assoc]

theorem connectorMatrix_isUnit {K : Type*} [Field K]
    (P : LocalRS K) (m : Nat) (hP : constantCoeff P ≠ 0) :
    IsUnit (connectorMatrix P m) := by
  rw [Matrix.isUnit_iff_isUnit_det, connectorMatrix_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ hP))

theorem connectorMatrix_mulVec_surjective {K : Type*} [Field K]
    (P : LocalRS K) (m : Nat) (hP : constantCoeff P ≠ 0) :
    Function.Surjective (connectorMatrix P m).mulVec := by
  rw [Matrix.mulVec_surjective_iff_isUnit]
  exact connectorMatrix_isUnit P m hP

/-! ## Conditional causal repetition

Here the coefficient ring of the local `R,S` polynomial is itself a
one-variable polynomial ring.  Taking each passive-seed coefficient gives a
sequence of `3 x 3` blocks.  Once every carrier has been normalized to the
same delay and these really are the complete three state channels, the
finite convolution matrix is lower triangular with the nonzero local pivot
on every diagonal entry.  The hypotheses deliberately expose the
complete-state condition which is not supplied by a selected-row argument.
-/

def polynomialConnectorBlock {K : Type*} [Field K]
    (P : LocalRS (Polynomial K)) (m k : Nat) :
    Matrix (Fin 3) (Fin 3) K :=
  fun i j => (connectorMatrix P m i j).coeff k

theorem polynomialConnectorBlock_diagonal {K : Type*} [Field K]
    (P : LocalRS (Polynomial K)) (m k : Nat) (i : Fin 3) :
    polynomialConnectorBlock P m k i i =
      (constantCoeff P ^ m).coeff k := by
  rw [polynomialConnectorBlock, connectorMatrix_diagonal]

theorem polynomialConnectorBlock_above_zero {K : Type*} [Field K]
    (P : LocalRS (Polynomial K)) (m k : Nat) (i j : Fin 3) (hij : i < j) :
    polynomialConnectorBlock P m k i j = 0 := by
  rw [polynomialConnectorBlock, connectorMatrix_above_zero P m i j hij]
  exact Polynomial.coeff_zero k

abbrev CausalIndex (n : Nat) := Fin n ×ₗ Fin 3

def causalBlockToeplitz {K : Type*} [Field K]
    (B : Nat → Matrix (Fin 3) (Fin 3) K) (n : Nat) :
    Matrix (CausalIndex n) (CausalIndex n) K :=
  fun i j =>
    if (ofLex j).1 ≤ (ofLex i).1 then
      B ((ofLex i).1.val - (ofLex j).1.val)
        (ofLex i).2 (ofLex j).2
    else 0

theorem causalBlockToeplitz_lowerTriangular {K : Type*} [Field K]
    (B : Nat → Matrix (Fin 3) (Fin 3) K)
    (hupper : ∀ i j, i < j → B 0 i j = 0) (n : Nat) :
    (causalBlockToeplitz B n).BlockTriangular OrderDual.toDual := by
  intro i j hji
  have hij : i < j := by simpa using hji
  rw [Prod.Lex.lt_iff] at hij
  rcases hij with htime | ⟨htime, hchannel⟩
  · simp [causalBlockToeplitz, Fin.not_le.mpr htime]
  · simp [causalBlockToeplitz, htime, hupper _ _ hchannel]

theorem causalBlockToeplitz_diagonal {K : Type*} [Field K]
    (B : Nat → Matrix (Fin 3) (Fin 3) K) (n : Nat) (i : CausalIndex n) :
    causalBlockToeplitz B n i i =
      B 0 (ofLex i).2 (ofLex i).2 := by
  simp [causalBlockToeplitz]

theorem causalBlockToeplitz_det {K : Type*} [Field K]
    (B : Nat → Matrix (Fin 3) (Fin 3) K)
    (d : K) (hupper : ∀ i j, i < j → B 0 i j = 0)
    (hdiag : ∀ i, B 0 i i = d) (n : Nat) :
    (causalBlockToeplitz B n).det = ∏ _i : CausalIndex n, d := by
  rw [Matrix.det_of_lowerTriangular _
    (causalBlockToeplitz_lowerTriangular B hupper n)]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [causalBlockToeplitz_diagonal, hdiag]

theorem causalBlockToeplitz_mulVec_surjective {K : Type*} [Field K]
    (B : Nat → Matrix (Fin 3) (Fin 3) K)
    (d : K) (hupper : ∀ i j, i < j → B 0 i j = 0)
    (hdiag : ∀ i, B 0 i i = d) (hd : d ≠ 0) (n : Nat) :
    Function.Surjective (causalBlockToeplitz B n).mulVec := by
  rw [Matrix.mulVec_surjective_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det,
    causalBlockToeplitz_det B d hupper hdiag n]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => hd))

theorem polynomialConnectorCausal_surjective {K : Type*} [Field K]
    (P : LocalRS (Polynomial K)) (m n : Nat)
    (hlead : (constantCoeff P ^ m).coeff 0 ≠ 0) :
    Function.Surjective
      (causalBlockToeplitz (polynomialConnectorBlock P m) n).mulVec := by
  apply causalBlockToeplitz_mulVec_surjective
      (polynomialConnectorBlock P m)
      ((constantCoeff P ^ m).coeff 0)
  · exact fun i j hij => polynomialConnectorBlock_above_zero P m 0 i j hij
  · exact fun i => polynomialConnectorBlock_diagonal P m 0 i
  · exact hlead

/-! ## Why this does not make the centered `R,S` carriers universally legal

The hypothesis `degree Q < g` alone permits `degree Q = g - 1`.  If the
weight of `R` is written `m + excess + 1`, then the `Q^m R` corner of the
centered `R` carrier has cost `m*g + excess`; strict source width already
fails even when `excess = 0`.  The analogous `S` statement has weight
`m + excess + 2` because `S` has weight `w - 2`.
-/

theorem penultimateDegree_R_topCost (m g excess : Nat) (hg : 1 ≤ g) :
    m * (g - 1) + ((m + excess + 1) - 1) = m * g + excess := by
  rw [Nat.add_sub_cancel]
  calc
    m * (g - 1) + (m + excess) =
        (m * (g - 1) + m) + excess := by omega
    _ = m * ((g - 1) + 1) + excess := by
      rw [Nat.mul_add, Nat.mul_one]
    _ = m * g + excess := by rw [Nat.sub_add_cancel hg]

theorem penultimateDegree_S_topCost (m g excess : Nat) (hg : 1 ≤ g) :
    m * (g - 1) + ((m + excess + 2) - 2) = m * g + excess := by
  rw [Nat.add_sub_cancel]
  calc
    m * (g - 1) + (m + excess) =
        (m * (g - 1) + m) + excess := by omega
    _ = m * ((g - 1) + 1) + excess := by
      rw [Nat.mul_add, Nat.mul_one]
    _ = m * g + excess := by rw [Nat.sub_add_cancel hg]

theorem full187_penultimateDegree_R_topCost :
    60 * (180413 - 1) + (131071 - 1) = 10824780 + 131010 := by
  norm_num

theorem full187_penultimateDegree_S_topCost :
    60 * (180413 - 1) + (131071 - 2) = 10824780 + 131009 := by
  norm_num

#print axioms connectorMatrix_diagonal
#print axioms connectorMatrix_above_zero
#print axioms connectorMatrix_det
#print axioms connectorMatrix_mulVec_surjective
#print axioms causalBlockToeplitz_det
#print axioms causalBlockToeplitz_mulVec_surjective
#print axioms polynomialConnectorCausal_surjective
#print axioms penultimateDegree_R_topCost
#print axioms penultimateDegree_S_topCost
#print axioms full187_penultimateDegree_R_topCost
#print axioms full187_penultimateDegree_S_topCost

end

end ProximityPrize.SubmissionLower.ThreeShapeLocalConnector6900
