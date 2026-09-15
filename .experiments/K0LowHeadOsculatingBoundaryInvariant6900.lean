import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# The four osculating low-head carriers have a triangular fresh boundary

This is the boundary-only invariant behind the proposed `m=47` low-head
repair.  At a point where the agreement locator has nonzero value `h`, the
four carriers

```
H^43 A,  H^42 B1,  H^41 B2,  H^44 Z
```

have a triangular boundary matrix.  Its diagonal is
`(h^43,h^43,2*h^43,h^44)`, hence its determinant is `2*h^173`.

The result is deliberately local at the fresh boundary point.  It does not
claim that the first three carriers have zero old head at error nodes; that
is the remaining global correction/annihilator problem.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadOsculatingBoundaryInvariant6900

open MvPolynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

abbrev BoundaryPoly := MvPolynomial (Fin 4) K

def coordY : BoundaryPoly (K := K) := MvPolynomial.X 0
def coordR : BoundaryPoly (K := K) := MvPolynomial.X 1
def coordS : BoundaryPoly (K := K) := MvPolynomial.X 2
def coordZ : BoundaryPoly (K := K) := MvPolynomial.X 3

def centeredValue (p q gamma : K) : BoundaryPoly (K := K) :=
  coordY - C p - (coordZ - C gamma) * C q

def centeredSlope (p1 q1 gamma : K) : BoundaryPoly (K := K) :=
  coordR - C p1 - (coordZ - C gamma) * C q1

/-- Hasse-normalized curvature residual.  The factor two is the one used by
the literal `-epsilon^2*S` contact convention. -/
def centeredCurvature (p2 q2 gamma : K) : BoundaryPoly (K := K) :=
  2 * (coordS - C p2 - (coordZ - C gamma) * C q2)

def firstOsculating
    (h h1 p q p1 q1 gamma : K) : BoundaryPoly (K := K) :=
  C h * centeredSlope p1 q1 gamma - C h1 * centeredValue p q gamma

def secondOsculating
    (h h1 h2 p q p1 q1 p2 q2 gamma : K) : BoundaryPoly (K := K) :=
  C (h ^ 2) * centeredCurvature p2 q2 gamma -
    C (2 * h * h1) * centeredSlope p1 q1 gamma +
      C (2 * h1 ^ 2 - h * h2) * centeredValue p q gamma

def graphEval (p p1 p2 gamma : K) (F : BoundaryPoly (K := K)) : K :=
  MvPolynomial.eval ![p, p1, p2, gamma] F

/-- Boundary coordinate order is `(Y,R,S,Z)`. -/
def boundaryJet (p p1 p2 gamma : K)
    (F : BoundaryPoly (K := K)) : Fin 4 → K :=
  fun i => graphEval p p1 p2 gamma (MvPolynomial.pderiv i F)

def carrierValue
    (h p q gamma : K) : BoundaryPoly (K := K) :=
  C (h ^ 43) * centeredValue p q gamma

def carrierFirst
    (h h1 p q p1 q1 gamma : K) : BoundaryPoly (K := K) :=
  C (h ^ 42) * firstOsculating h h1 p q p1 q1 gamma

def carrierSecond
    (h h1 h2 p q p1 q1 p2 q2 gamma : K) : BoundaryPoly (K := K) :=
  C (h ^ 41) * secondOsculating h h1 h2 p q p1 q1 p2 q2 gamma

def carrierSeed (h : K) : BoundaryPoly (K := K) :=
  C (h ^ 44) * coordZ

def carrierFamily
    (h h1 h2 p q p1 q1 p2 q2 gamma : K) :
    Fin 4 → BoundaryPoly (K := K) := ![
  carrierValue h p q gamma,
  carrierFirst h h1 p q p1 q1 gamma,
  carrierSecond h h1 h2 p q p1 q1 p2 q2 gamma,
  carrierSeed h]

theorem boundaryJet_carrierValue
    (h p q p1 p2 gamma : K) :
    boundaryJet p p1 p2 gamma (carrierValue h p q gamma) =
      ![h ^ 43, 0, 0, -(h ^ 43) * q] := by
  funext i
  fin_cases i <;>
    simp [boundaryJet, graphEval, carrierValue, centeredValue,
      coordY, coordR, coordS, coordZ, MvPolynomial.pderiv_mul,
      Pi.single_apply] <;> ring

theorem boundaryJet_carrierFirst
    (h h1 p q p1 q1 p2 gamma : K) :
    boundaryJet p p1 p2 gamma
        (carrierFirst h h1 p q p1 q1 gamma) =
      ![-(h ^ 42) * h1, h ^ 43, 0,
        h ^ 42 * (h1 * q - h * q1)] := by
  funext i
  fin_cases i <;>
    simp [boundaryJet, graphEval, carrierFirst, firstOsculating,
      centeredValue, centeredSlope, coordY, coordR, coordS, coordZ,
      MvPolynomial.pderiv_mul, Pi.single_apply] <;> ring <;> simp

theorem boundaryJet_carrierSecond
    (h h1 h2 p q p1 q1 p2 q2 gamma : K) :
    boundaryJet p p1 p2 gamma
        (carrierSecond h h1 h2 p q p1 q1 p2 q2 gamma) =
      ![h ^ 41 * (2 * h1 ^ 2 - h * h2),
        -(2 * h ^ 42 * h1),
        2 * h ^ 43,
        h ^ 41 *
          (-2 * h ^ 2 * q2 + 2 * h * h1 * q1 -
            (2 * h1 ^ 2 - h * h2) * q)] := by
  funext i
  fin_cases i <;>
    simp [boundaryJet, graphEval, carrierSecond, secondOsculating,
      centeredValue, centeredSlope, centeredCurvature,
      coordY, coordR, coordS, coordZ, MvPolynomial.pderiv_mul,
      Pi.single_apply] <;> ring <;> simp

theorem boundaryJet_carrierSeed
    (h p p1 p2 gamma : K) :
    boundaryJet p p1 p2 gamma (carrierSeed h) =
      ![0, 0, 0, h ^ 44] := by
  funext i
  fin_cases i <;>
    simp [boundaryJet, graphEval, carrierSeed,
      coordY, coordR, coordS, coordZ, MvPolynomial.pderiv_mul,
      Pi.single_apply]

/-- The scalar boundary matrix after the four displayed coefficient
computations.  Columns correspond to `(H^43*A,H^42*B1,H^41*B2,H^44*Z)`;
rows are `(Y,R,S,Z)`. -/
def osculatingBoundaryMap
    (h h1 h2 q q1 q2 : K) (c : Fin 4 → K) : Fin 4 → K := ![
  h ^ 43 * c 0 - h ^ 42 * h1 * c 1 +
    h ^ 41 * (2 * h1 ^ 2 - h * h2) * c 2,
  h ^ 43 * c 1 - 2 * h ^ 42 * h1 * c 2,
  2 * h ^ 43 * c 2,
  -(h ^ 43) * q * c 0 + h ^ 42 * (h1 * q - h * q1) * c 1 +
    h ^ 41 * (-2 * h ^ 2 * q2 + 2 * h * h1 * q1 -
      (2 * h1 ^ 2 - h * h2) * q) * c 2 + h ^ 44 * c 3]

def carrierBoundaryMap
    (h h1 h2 p q p1 q1 p2 q2 gamma : K)
    (c : Fin 4 → K) : Fin 4 → K := fun i =>
  ∑ j, c j * boundaryJet p p1 p2 gamma
    (carrierFamily h h1 h2 p q p1 q1 p2 q2 gamma j) i

theorem carrierBoundaryMap_eq_osculatingBoundaryMap
    (h h1 h2 p q p1 q1 p2 q2 gamma : K) (c : Fin 4 → K) :
    carrierBoundaryMap h h1 h2 p q p1 q1 p2 q2 gamma c =
      osculatingBoundaryMap h h1 h2 q q1 q2 c := by
  rw [show carrierBoundaryMap h h1 h2 p q p1 q1 p2 q2 gamma c =
      fun i => ∑ j, c j * boundaryJet p p1 p2 gamma
        (carrierFamily h h1 h2 p q p1 q1 p2 q2 gamma j) i from rfl]
  funext i
  fin_cases i <;>
    simp [Fin.sum_univ_four, carrierFamily,
      boundaryJet_carrierValue, boundaryJet_carrierFirst,
      boundaryJet_carrierSecond, boundaryJet_carrierSeed,
      osculatingBoundaryMap] <;> ring

/-- The boundary invariant is independent of every candidate/tangent jet:
only `h != 0` and characteristic not two are needed. -/
theorem osculatingBoundaryMap_injective
    (h h1 h2 q q1 q2 : K) (hh : h ≠ 0) (htwo : (2 : K) ≠ 0) :
    Function.Injective (osculatingBoundaryMap h h1 h2 q q1 q2) := by
  intro c d hcd
  have hS := congrFun hcd 2
  have hc2 : c 2 = d 2 := by
    simpa [osculatingBoundaryMap, htwo, hh] using hS
  have hR := congrFun hcd 1
  have hc1 : c 1 = d 1 := by
    simpa [osculatingBoundaryMap, hc2, hh] using hR
  have hY := congrFun hcd 0
  have hc0 : c 0 = d 0 := by
    simpa [osculatingBoundaryMap, hc1, hc2, hh] using hY
  have hZ := congrFun hcd 3
  have hc3 : c 3 = d 3 := by
    simpa [osculatingBoundaryMap, hc0, hc1, hc2, hh] using hZ
  funext i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

/-- Consequently the four literal carrier boundary jets are linearly
independent.  This is the exact rank-four fresh-boundary statement; all
remaining work is old-head cancellation at error nodes. -/
theorem carrierBoundaryMap_injective
    (h h1 h2 p q p1 q1 p2 q2 gamma : K)
    (hh : h ≠ 0) (htwo : (2 : K) ≠ 0) :
    Function.Injective
      (carrierBoundaryMap h h1 h2 p q p1 q1 p2 q2 gamma) := by
  intro c d hcd
  apply osculatingBoundaryMap_injective h h1 h2 q q1 q2 hh htwo
  rw [← carrierBoundaryMap_eq_osculatingBoundaryMap
      h h1 h2 p q p1 q1 p2 q2 gamma c,
    ← carrierBoundaryMap_eq_osculatingBoundaryMap
      h h1 h2 p q p1 q1 p2 q2 gamma d]
  exact hcd

/-- The product of the four triangular pivots.  This is the determinant of
the displayed boundary matrix: `2*h^173`. -/
theorem osculatingBoundary_pivot_product
    (h : K) :
    h ^ 43 * h ^ 43 * (2 * h ^ 43) * h ^ 44 = 2 * h ^ 173 := by
  ring

#print axioms boundaryJet_carrierValue
#print axioms boundaryJet_carrierFirst
#print axioms boundaryJet_carrierSecond
#print axioms boundaryJet_carrierSeed
#print axioms osculatingBoundaryMap_injective
#print axioms carrierBoundaryMap_injective
#print axioms osculatingBoundary_pivot_product

end

end ProximityPrize.SubmissionLower.K0LowHeadOsculatingBoundaryInvariant6900
