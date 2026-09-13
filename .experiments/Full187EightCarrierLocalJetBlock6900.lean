import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Local unit for the order-four eight-carrier terminal block

The eight carrier indices, in lower-triangular order, are

  (a,c) = (0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0).

For `m=r+4`, the selected coefficient of

  Lambda^a V^(m-a-2c) J1^c Z^(b+a+c)

at a simple error is `Lambda^(a+c) * delta^(m-a-2c)`.  The Python
companion checks the complete literal 24 by 24 matrix, including arbitrary
direction offsets.  This file certifies the determinant and global Hermite
dimension arithmetic without finite evaluation tactics.
-/

namespace ProximityPrize.SubmissionLower.Full187EightCarrierLocalJetBlock6900

set_option autoImplicit false

/-- Product of the eight diagonal entries, writing `m=r+4` so every
exponent is manifestly nonnegative. -/
def oneLayerDiagonalProduct {K : Type*} [CommRing K]
    (lambda delta : K) (r : Nat) : K :=
  delta ^ (r + 4) *
  (lambda * delta ^ (r + 2)) *
  (lambda * delta ^ (r + 3)) *
  (lambda ^ 2 * delta ^ (r + 1)) *
  (lambda ^ 2 * delta ^ (r + 2)) *
  (lambda ^ 3 * delta ^ r) *
  (lambda ^ 3 * delta ^ (r + 1)) *
  (lambda ^ 4 * delta ^ r)

theorem oneLayerDiagonalProduct_eq {K : Type*} [CommRing K]
    (lambda delta : K) (r : Nat) :
    oneLayerDiagonalProduct lambda delta r =
      lambda ^ 16 * delta ^ (r * 8 + 13) := by
  simp only [oneLayerDiagonalProduct, pow_add, pow_mul]
  ring

/-- The local block is a unit over a field whenever the locator and received
value residual are nonzero. -/
theorem oneLayerDiagonalProduct_ne_zero {K : Type*} [Field K]
    (lambda delta : K) (r : Nat)
    (hlambda : lambda ≠ 0) (hdelta : delta ≠ 0) :
    oneLayerDiagonalProduct lambda delta r ≠ 0 := by
  rw [oneLayerDiagonalProduct_eq]
  exact mul_ne_zero (pow_ne_zero _ hlambda) (pow_ne_zero _ hdelta)

/-- Three coefficient-Hasse layers repeat the same diagonal block. -/
theorem threeLayerDiagonalProduct_ne_zero {K : Type*} [Field K]
    (lambda delta : K) (r : Nat)
    (hlambda : lambda ≠ 0) (hdelta : delta ≠ 0) :
    (oneLayerDiagonalProduct lambda delta r) ^ 3 ≠ 0 := by
  exact pow_ne_zero 3
    (oneLayerDiagonalProduct_ne_zero lambda delta r hlambda hdelta)

/-- With caps `deg p[a,c] <= 3e-1-a-c`, the eight coefficient spaces have
dimensions `3e-(a+c)`.  Their total is `24e-16`. -/
theorem bounded_threeJet_coefficient_dimension (e : Nat) (he : 2 ≤ e) :
    (3 * e) +
      (3 * e - 1) + (3 * e - 1) +
      (3 * e - 2) + (3 * e - 2) +
      (3 * e - 3) + (3 * e - 3) +
      (3 * e - 4) = 24 * e - 16 := by
  omega

/-- Therefore these bounded multipliers miss sixteen dimensions of arbitrary
three-jet data at `e` errors.  Local invertibility is not, by itself, global
Hermite surjectivity. -/
theorem bounded_threeJet_global_deficit (e : Nat) (he : 2 ≤ e) :
    24 * e -
      ((3 * e) +
       (3 * e - 1) + (3 * e - 1) +
       (3 * e - 2) + (3 * e - 2) +
       (3 * e - 3) + (3 * e - 3) +
       (3 * e - 4)) = 16 := by
  omega

theorem f101_dimension_receipt :
    (9 + 8 + 8 + 7 + 7 + 6 + 6 + 5 = 56) ∧
      8 * 3 * 3 = 72 ∧ 72 - 56 = 16 := by
  norm_num

#print axioms oneLayerDiagonalProduct_eq
#print axioms oneLayerDiagonalProduct_ne_zero
#print axioms threeLayerDiagonalProduct_ne_zero
#print axioms bounded_threeJet_coefficient_dimension
#print axioms bounded_threeJet_global_deficit
#print axioms f101_dimension_receipt

end ProximityPrize.SubmissionLower.Full187EightCarrierLocalJetBlock6900
