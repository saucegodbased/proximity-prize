import Fin4GenericFibreRegularPointBridge6900

/-!
# A quadratic height-three cut need not satisfy the regular Fin-3 consumer

The rank-two-plus-quadratic escape interface permits the literal local model
`(Y, R, S^2)`.  Its radical is the height-three coordinate prime
`(Y, R, S)`, but the ordinary three-row Jacobian determinant is `2*S`, hence
lies in that prime.  This is the exact double-component obstruction: local
height three alone cannot manufacture the `hminor` premise of the existing
Fin-3/Fin-4 regular-point aggregate adapters.

The theorem below is deliberately characteristic-free.  In characteristic
two the displayed determinant is zero, which only strengthens the
obstruction.
-/

namespace ProximityPrize.SubmissionLower.K0T2HeightThreeConsumerCounterexample6900

open scoped Matrix
open Fin4GenericPrimeExtension6900
open Fin4FixedTripleGenericFibre6900
open Fin4GenericFibreRegularPointBridge6900

noncomputable section
set_option autoImplicit false

variable (K : Type) [Field K]

def yCoord : Poly4 K := MvPolynomial.X (zIndex.succAbove 0)
def rCoord : Poly4 K := MvPolynomial.X (zIndex.succAbove 1)
def sCoord : Poly4 K := MvPolynomial.X (zIndex.succAbove 2)

/-- The radical coordinate ideal `(Y,R,S)`.  Algebraically its quotient is
`K[Z]`, so this is the standard height-three coordinate prime. -/
def coordinateRadical : Ideal (Poly4 K) :=
  Ideal.span ({yCoord K, rCoord K, sCoord K} : Set (Poly4 K))

theorem yCoord_mem_coordinateRadical : yCoord K ∈ coordinateRadical K := by
  exact Ideal.subset_span (by simp)

theorem rCoord_mem_coordinateRadical : rCoord K ∈ coordinateRadical K := by
  exact Ideal.subset_span (by simp)

theorem sCoord_mem_coordinateRadical : sCoord K ∈ coordinateRadical K := by
  exact Ideal.subset_span (by simp)

/-- The literal rank-two plus nonzero quadratic escape model. -/
def doubleComponentRows : Fin 3 → Poly4 K :=
  ![yCoord K, rCoord K, sCoord K ^ 2]

/-- Its ordinary three-coordinate Jacobian determinant is not a unit: it is
the nilpotent transverse coordinate, with multiplicity two. -/
theorem doubleComponentRows_jacobian_det :
    (ordinaryDerivativeMinorPolynomial (doubleComponentRows K)).det =
      (2 : Poly4 K) * MvPolynomial.X (zIndex.succAbove 2) := by
  simp [ordinaryDerivativeMinorPolynomial, doubleComponentRows,
    yCoord, rCoord, sCoord, Matrix.det_fin_three]

/-- In particular the determinant belongs to every ideal containing the
third coordinate.  Thus the current aggregate consumer's nonmembership gate
does not follow from the height-three conclusion of quadratic escape. -/
theorem doubleComponentRows_jacobian_det_mem
    (P : Ideal (Poly4 K))
    (hS : MvPolynomial.X (zIndex.succAbove 2) ∈ P) :
    (ordinaryDerivativeMinorPolynomial (doubleComponentRows K)).det ∈ P := by
  rw [doubleComponentRows_jacobian_det]
  exact P.mul_mem_left _ hS

/-- Every row in the nonreduced ideal `(Y,R,S^2)` has zero `S`
differential modulo its radical `(Y,R,S)`. -/
def generatedDoubleRow (a b c : Poly4 K) : Poly4 K :=
  a * yCoord K + b * rCoord K + c * sCoord K ^ 2

@[simp] theorem pderiv_s_yCoord :
    MvPolynomial.pderiv (zIndex.succAbove 2) (yCoord K) = 0 := by
  simp [yCoord]

@[simp] theorem pderiv_s_rCoord :
    MvPolynomial.pderiv (zIndex.succAbove 2) (rCoord K) = 0 := by
  simp [rCoord]

@[simp] theorem pderiv_s_sCoord :
    MvPolynomial.pderiv (zIndex.succAbove 2) (sCoord K) = 1 := by
  simp [sCoord]

theorem generatedDoubleRow_pderiv_s_mem (a b c : Poly4 K) :
    MvPolynomial.pderiv (zIndex.succAbove 2) (generatedDoubleRow K a b c) ∈
      coordinateRadical K := by
  let P := coordinateRadical K
  have hy : yCoord K ∈ P := yCoord_mem_coordinateRadical K
  have hr : rCoord K ∈ P := rCoord_mem_coordinateRadical K
  have hs : sCoord K ∈ P := sCoord_mem_coordinateRadical K
  have hs2 : sCoord K ^ 2 ∈ P := P.pow_mem_of_mem hs 2 (by omega)
  have hdy :
      MvPolynomial.pderiv (zIndex.succAbove 2) (a * yCoord K) ∈ P := by
    rw [MvPolynomial.pderiv_mul, pderiv_s_yCoord, mul_zero, add_zero]
    exact P.mul_mem_left _ hy
  have hdr :
      MvPolynomial.pderiv (zIndex.succAbove 2) (b * rCoord K) ∈ P := by
    rw [MvPolynomial.pderiv_mul, pderiv_s_rCoord, mul_zero, add_zero]
    exact P.mul_mem_left _ hr
  have hds2 :
      MvPolynomial.pderiv (zIndex.succAbove 2) (sCoord K ^ 2) ∈ P := by
    rw [MvPolynomial.pderiv_pow, pderiv_s_sCoord, mul_one]
    simpa using P.mul_mem_left (2 : Poly4 K) hs
  have hdc :
      MvPolynomial.pderiv (zIndex.succAbove 2) (c * sCoord K ^ 2) ∈ P := by
    rw [MvPolynomial.pderiv_mul]
    exact P.add_mem (P.mul_mem_left _ hs2) (P.mul_mem_left _ hds2)
  rw [generatedDoubleRow, map_add, map_add]
  exact P.add_mem (P.add_mem hdy hdr) hdc

/-- A determinant whose whole column belongs to an ideal belongs to the
ideal.  This quotient proof avoids any coordinate-specific expansion. -/
theorem det_mem_of_column_mem
    (P : Ideal (Poly4 K)) (A : Matrix (Fin 3) (Fin 3) (Poly4 K)) (j : Fin 3)
    (hcol : ∀ i, A i j ∈ P) : A.det ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [(Ideal.Quotient.mk P).map_det]
  exact Matrix.det_eq_zero_of_column_eq_zero j
    (fun i ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hcol i))

/-- The obstruction survives *all* changes of three generators inside
`(Y,R,S^2)`: no such triple can satisfy the ordinary-minor nonmembership
premise at the radical component. -/
theorem all_generated_triples_jacobian_det_mem
    (a b c : Fin 3 → Poly4 K) :
    (ordinaryDerivativeMinorPolynomial
      (fun i ↦ generatedDoubleRow K (a i) (b i) (c i))).det ∈
      coordinateRadical K := by
  apply det_mem_of_column_mem K (coordinateRadical K) _ 2
  intro i
  exact generatedDoubleRow_pderiv_s_mem K (a i) (b i) (c i)

end

end ProximityPrize.SubmissionLower.K0T2HeightThreeConsumerCounterexample6900

#print axioms ProximityPrize.SubmissionLower.K0T2HeightThreeConsumerCounterexample6900.all_generated_triples_jacobian_det_mem
