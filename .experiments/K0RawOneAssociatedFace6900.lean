import K0SRTinyContactCore6900
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Associated passive grade of the raw-1 last face

Give each of the passive/local variables `R,S,T,Z` degree one and give the
outer contact parameter `epsilon` degree zero.  For a last-face raw monomial

`X^a Y^y Z^z`, with `y+z=L`,

the degree-`L` contacted term is exactly

`(x+epsilon)^a (u1*Z + epsilon*R - epsilon^2*S + epsilon^3*T)^y Z^z`.

All terms containing `u0` have smaller passive degree.  Reorganizing this top
term as a polynomial in `(R,S,T,Z)` over `K[epsilon]` exposes a weighted
bivariate Hasse/Hermite evaluation in `(x,u1)`.  This file proves the exact
algebraic identities.  It deliberately makes no claim that a kernel of the
associated map lifts through the complete cap-`L-1` contact image.
-/

namespace ProximityPrize.SubmissionLower.K0RawOneAssociatedFace6900

open scoped BigOperators
open Polynomial
open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

/-! ## Exact top-face splitting in the literal flattened contact ring -/

def contactedDirection (u1 : K) : FlatContact K :=
  MvPolynomial.C u1 * localZ + eps * localR - eps ^ 2 * localS +
    eps ^ 3 * localT

theorem contactedY_eq_constant_add_direction (u0 u1 : K) :
    contactedY u0 u1 = MvPolynomial.C u0 + contactedDirection u1 := by
  simp only [contactedY, contactedDirection]
  ring

/-- The exact binomial decomposition by passive degree.  The summand indexed
by `j` has passive degree `z+j`; hence only `j=y` survives in associated total
degree `y+z`. -/
theorem rawOneContactColumn_binomial
    (x u0 u1 : K) (a y z : Nat) :
    rawContactColumn x u0 u1 a 0 y 0 z =
      (MvPolynomial.C x + eps) ^ a *
        (∑ j ∈ Finset.range (y + 1),
          (MvPolynomial.C u0) ^ j * contactedDirection u1 ^ (y - j) *
            (y.choose j : FlatContact K)) * localZ ^ z := by
  simp only [rawContactColumn, pow_zero, mul_one,
    contactedY_eq_constant_add_direction]
  have hpow :
      (MvPolynomial.C u0 + contactedDirection u1) ^ y =
        ∑ j ∈ Finset.range (y + 1),
          (MvPolynomial.C u0) ^ j * contactedDirection u1 ^ (y - j) *
            (y.choose j : FlatContact K) :=
    add_pow (MvPolynomial.C u0) (contactedDirection u1) y
  rw [hpow]

/-- The unique top-passive-degree summand of the preceding expansion. -/
def rawOneAssociatedFaceColumn
    (x u1 : K) (a y z : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * contactedDirection u1 ^ y * localZ ^ z

theorem rawOneAssociatedFaceColumn_is_last_binomial_term
    (x u0 u1 : K) (a y z : Nat) :
    (MvPolynomial.C x + eps) ^ a *
          ((MvPolynomial.C u0) ^ 0 * contactedDirection u1 ^ (y - 0) *
            (y.choose 0 : FlatContact K)) * localZ ^ z =
      rawOneAssociatedFaceColumn x u1 a y z := by
  simp [rawOneAssociatedFaceColumn]

/-! ## Reorganization over `K[epsilon]` and weighted Hermite factorization -/

/-- Variables are ordered `(R,S,T,Z)`; coefficients are in `K[epsilon]`. -/
abbrev AssociatedTarget (K : Type*) [Field K] :=
  MvPolynomial (Fin 4) K[X]

def directionCoefficient (u1 : K) : Fin 4 → K[X] :=
  ![Polynomial.X, -(Polynomial.X ^ 2), Polynomial.X ^ 3, Polynomial.C u1]

def associatedDirection (u1 : K) : AssociatedTarget K :=
  ∑ i, directionCoefficient u1 i • MvPolynomial.X i

theorem associatedDirection_eq (u1 : K) :
    associatedDirection u1 =
      MvPolynomial.C Polynomial.X * MvPolynomial.X 0 -
        MvPolynomial.C (Polynomial.X ^ 2) * MvPolynomial.X 1 +
        MvPolynomial.C (Polynomial.X ^ 3) * MvPolynomial.X 2 +
        MvPolynomial.C (Polynomial.C u1) * MvPolynomial.X 3 := by
  simp [associatedDirection, directionCoefficient, Fin.sum_univ_four,
    MvPolynomial.smul_eq_C_mul]
  ring

def innerShape (y r s t : Nat) : Fin 4 →₀ Nat :=
  Finsupp.equivFunOnFinite.symm ![r, s, t, y - (r + s + t)]

def seedShape (z : Nat) : Fin 4 →₀ Nat := Finsupp.single 3 z

@[simp] theorem innerShape_apply_zero (y r s t : Nat) :
    innerShape y r s t 0 = r := by simp [innerShape]

@[simp] theorem innerShape_apply_one (y r s t : Nat) :
    innerShape y r s t 1 = s := by simp [innerShape]

@[simp] theorem innerShape_apply_two (y r s t : Nat) :
    innerShape y r s t 2 = t := by simp [innerShape]

@[simp] theorem innerShape_apply_three (y r s t : Nat) :
    innerShape y r s t 3 = y - (r + s + t) := by simp [innerShape]

theorem innerShape_total (y r s t : Nat) (h : r + s + t ≤ y) :
    (innerShape y r s t).sum (fun _ n ↦ n) = y := by
  classical
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_four, h]
  · intro i
    rfl

/-- The shape product is one explicit inner-Hasse weight times the outer
epsilon shift `r+2s+3t`. -/
theorem innerShape_directionProduct
    (u1 : K) (y r s t : Nat) :
    (innerShape y r s t).prod
        (fun i n ↦ directionCoefficient u1 i ^ n) =
      Polynomial.X ^ r * (-(Polynomial.X ^ 2)) ^ s *
        (Polynomial.X ^ 3) ^ t *
          (Polynomial.C u1) ^ (y - (r + s + t)) := by
  classical
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four, directionCoefficient]
  · intro i
    simp

/-- The associated raw-1 column, now represented over `K[epsilon]`. -/
def associatedRawOneColumn
    (x u1 : K) (a y z : Nat) : AssociatedTarget K :=
  MvPolynomial.C ((Polynomial.C x + Polynomial.X) ^ a) *
    associatedDirection u1 ^ y * MvPolynomial.monomial (seedShape z) 1

/-- Exact coefficient formula.  `innerShape.multinomial` is the shape weight;
the product contains `u1^(y-r-s-t)` and
`epsilon^(r+2s+3t)`.  Multiplication by `(x+epsilon)^a` is precisely outer
Hasse evaluation at `x`. -/
theorem coeff_associatedRawOneColumn
    (x u1 : K) (a y z r s t : Nat) (h : r + s + t ≤ y) :
    MvPolynomial.coeff (innerShape y r s t + seedShape z)
        (associatedRawOneColumn x u1 a y z) =
      (Polynomial.C x + Polynomial.X) ^ a *
        ((innerShape y r s t).multinomial : K[X]) *
        (innerShape y r s t).prod
          (fun i n ↦ directionCoefficient u1 i ^ n) := by
  classical
  simp only [associatedRawOneColumn, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_mul_monomial, mul_one]
  unfold associatedDirection
  rw [MvPolynomial.coeff_linearCombination_X_pow_of_fintype]
  rw [if_pos (innerShape_total y r s t h)]
  ring

/-- Expanded weighted-Hermite form of the coefficient.  The only dependence
on the node is through `(x+epsilon)^a` and
`u1^(y-r-s-t)`; the remaining factors depend solely on the derivative shape.
-/
theorem coeff_associatedRawOneColumn_Hermite
    (x u1 : K) (a y z r s t : Nat) (h : r + s + t ≤ y) :
    MvPolynomial.coeff (innerShape y r s t + seedShape z)
        (associatedRawOneColumn x u1 a y z) =
      (Polynomial.C x + Polynomial.X) ^ a *
        ((innerShape y r s t).multinomial : K[X]) *
        (Polynomial.X ^ r * (-(Polynomial.X ^ 2)) ^ s *
          (Polynomial.X ^ 3) ^ t *
            (Polynomial.C u1) ^ (y - (r + s + t))) := by
  rw [coeff_associatedRawOneColumn x u1 a y z r s t h,
    innerShape_directionProduct]

/-- Literal source legality of every target raw-1 last-face coordinate. -/
theorem target_rawOne_lastFace_legal
    (a y : Nat) (hy : y ≤ 64)
    (ha : a + 131071 * y < 47 * 180413) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a 0 y 0 (3757 - y) := by
  unfold rawShapeLegal
  omega

/-- Exact target size of the raw-1 last-face domain. -/
theorem target_rawOne_lastFace_column_count :
    (∑ y ∈ Finset.range 65, (47 * 180413 - 131071 * y)) = 278534035 := by
  norm_num [Finset.sum_range_succ]

/-- The universal bivariate jet target has 1128 coordinates per node. -/
theorem target_bivariate_Hermite_rows_per_node :
    47 * (47 + 1) / 2 = 1128 := by norm_num

/-- Raw-1 alone is below the all-node bivariate-Hermite row cap.  Therefore
the associated factorization does not provide a dimension-forced target
kernel; other derivative shapes or special interpolation structure are
load-bearing. -/
theorem target_rawOne_below_Hermite_row_cap :
    278534035 + 17164397 = 262144 * 1128 := by norm_num

/-! ## Exact structural gain from buying one layer above the active cap -/

/-- Once `U ≤ L`, every genuinely new cap-`L+1` column has positive passive
seed exponent and is the passive successor of a cap-`L` column.  This is the
precise source-theoretic benefit of moving the target from 3757 to 3758.  It
does not assert that the successor contact is old-correctable. -/
theorem new_layer_is_passive_successor_of_active_cap
    (D w L B sCap U a s y r z : Nat) (hUL : U ≤ L)
    (hnew : rawShapeLegal D w (L + 1) B sCap U a s y r z)
    (hold : ¬ rawShapeLegal D w L B sCap U a s y r z) :
    0 < z ∧ rawShapeLegal D w L B sCap U a s y r (z - 1) := by
  unfold rawShapeLegal at hnew hold ⊢
  constructor
  · omega
  · omega

/-- Literal target specialization: the entire 3758\3757 face is passive. -/
theorem target_L3758_new_layer_is_passive_successor
    (a s y r z : Nat)
    (hnew : rawShapeLegal (47 * 180413) 131071 3758 16 8 64
      a s y r z)
    (hold : ¬ rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      a s y r z) :
    0 < z ∧
      rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        a s y r (z - 1) := by
  exact new_layer_is_passive_successor_of_active_cap
    (47 * 180413) 131071 3757 16 8 64 a s y r z (by norm_num) hnew hold

#print axioms contactedY_eq_constant_add_direction
#print axioms rawOneContactColumn_binomial
#print axioms rawOneAssociatedFaceColumn_is_last_binomial_term
#print axioms associatedDirection_eq
#print axioms innerShape_total
#print axioms innerShape_directionProduct
#print axioms coeff_associatedRawOneColumn
#print axioms coeff_associatedRawOneColumn_Hermite
#print axioms target_rawOne_lastFace_legal
#print axioms target_rawOne_lastFace_column_count
#print axioms target_rawOne_below_Hermite_row_cap
#print axioms new_layer_is_passive_successor_of_active_cap
#print axioms target_L3758_new_layer_is_passive_successor

end
end ProximityPrize.SubmissionLower.K0RawOneAssociatedFace6900
