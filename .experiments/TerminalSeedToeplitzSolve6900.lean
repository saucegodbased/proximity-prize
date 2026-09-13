import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Causal seed-shift Toeplitz block

If one contact carrier has a nonzero lowest-seed coefficient `a 0`, its
successive `Z` shifts give a lower-triangular Toeplitz block.  The determinant
is `(a 0)^n`, so every finite seed prefix is solvable.  This is the abstract
iteration step isolated by the F101 order-four compound-carrier experiment;
it does not construct that carrier or prove its coefficient-degree bounds.
-/

namespace ProximityPrize.Experiments.TerminalSeedToeplitzSolve6900

open Matrix

set_option autoImplicit false
set_option Elab.async false

noncomputable section

variable {K : Type*} [Field K]

/-- The first `n` output seed coefficients of convolution by `a`, after
removing the common lowest-seed monomial. -/
def causalToeplitz (a : Nat → K) (n : Nat) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦ if j ≤ i then a (i - j : Nat) else 0

theorem causalToeplitz_blockTriangular (a : Nat → K) (n : Nat) :
    (causalToeplitz a n).BlockTriangular OrderDual.toDual := by
  intro i j hji
  have hij : i < j := by simpa using hji
  simp [causalToeplitz, Fin.not_le.mpr hij]

theorem causalToeplitz_diagonal (a : Nat → K) (n : Nat) (i : Fin n) :
    causalToeplitz a n i i = a 0 := by
  simp [causalToeplitz]

/-- Every finite shifted-carrier block has the expected power determinant. -/
theorem causalToeplitz_det (a : Nat → K) (n : Nat) :
    (causalToeplitz a n).det = (a 0) ^ n := by
  rw [Matrix.det_of_lowerTriangular _
    (causalToeplitz_blockTriangular a n)]
  simp [causalToeplitz_diagonal]

/-- A nonzero leading contact coefficient makes the entire finite seed
trellis onto, independently of the higher-seed tail of the carrier. -/
theorem causalToeplitz_mulVec_surjective
    (a : Nat → K) (n : Nat) (ha : a 0 ≠ 0) :
    Function.Surjective (causalToeplitz a n).mulVec := by
  rw [Matrix.mulVec_surjective_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, causalToeplitz_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero n ha)

#print axioms causalToeplitz_blockTriangular
#print axioms causalToeplitz_det
#print axioms causalToeplitz_mulVec_surjective

end

end ProximityPrize.Experiments.TerminalSeedToeplitzSolve6900
