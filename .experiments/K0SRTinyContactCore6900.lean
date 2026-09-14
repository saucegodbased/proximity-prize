import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Tiny standalone contact core for the k0 SR seam

These are literal copies of the flattened definitions in
`K0RawRSConnectionTranspose6900`, isolated behind narrow Mathlib imports so
the three SR proof modules can be checked independently below 2 GiB RSS.
-/

namespace ProximityPrize.SubmissionLower.K0SRTinyContactCore6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

abbrev FlatContact (K : Type*) [Field K] := MvPolynomial (Fin 5) K

def eps : FlatContact K := MvPolynomial.X 0
def localS : FlatContact K := MvPolynomial.X 1
def localT : FlatContact K := MvPolynomial.X 2
def localR : FlatContact K := MvPolynomial.X 3
def localZ : FlatContact K := MvPolynomial.X 4

def contactedY (u0 u1 : K) : FlatContact K :=
  MvPolynomial.C u0 + MvPolynomial.C u1 * localZ +
    eps * localR - eps ^ 2 * localS + eps ^ 3 * localT

def rawContactColumn
    (x u0 u1 : K) (a s y r z : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * localS ^ s *
    contactedY u0 u1 ^ y * localR ^ r * localZ ^ z

def localConnection (P : FlatContact K) : FlatContact K :=
  MvPolynomial.pderiv 0 P +
    2 * localS * MvPolynomial.pderiv 3 P +
    3 * localT * MvPolynomial.pderiv 1 P

def rawShapeLegal
    (D w L B sCap U a s y r z : Nat) : Prop :=
  2 * s + r ≤ B ∧ s ≤ sCap ∧ s + y + r ≤ U ∧
    s + y + r + z ≤ L ∧
    a + w * y + (w - 1) * r + (w - 2) * s < D

def rawBoundaryScalar
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K)
    (s y r z : Nat) : K :=
  lambdaS * (s : K) * S0 ^ (s - 1) * Y0 ^ y * R0 ^ r * gamma ^ z +
  lambdaY * (y : K) * S0 ^ s * Y0 ^ (y - 1) * R0 ^ r * gamma ^ z +
  lambdaR * (r : K) * S0 ^ s * Y0 ^ y * R0 ^ (r - 1) * gamma ^ z +
  lambdaZ * (z : K) * S0 ^ s * Y0 ^ y * R0 ^ r * gamma ^ (z - 1)

def rawBoundaryRHS
    (xi S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K)
    (s y r z : Nat) (p : K[X]) : K :=
  rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
      s y r z * p.eval xi

end


end ProximityPrize.SubmissionLower.K0SRTinyContactCore6900
