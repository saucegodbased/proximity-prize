import K0SRTinyContactCore6900
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Compressed second-jet rows versus the formal flattened K0 contact

The finite `higher_jet_literal_matrix` model has variables `(epsilon,E,R,S,Z)`
and contact

`u0+u1*Z+E+epsilon*R-(1/2)*epsilon^2*S`.

The formal K0 contact has variables `(epsilon,S,T,R,Z)` and replaces
`E` by `epsilon^3*T`, while using the rescaled curvature variable.  This file
records the exact monomial injection and the source-column scaling.  It
justifies complete-contact rank calculations made with the compressed oracle;
it does *not* justify selecting a head by the compressed epsilon exponent
alone.  The formal epsilon order is `q+3*b` when the compressed E exponent is
`b`.
-/

namespace ProximityPrize.SubmissionLower.K0CompressedFormalContactEquiv6900

open K0SRTinyContactCore6900
open MvPolynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

abbrev CompressedContact (K : Type*) [Field K] :=
  MvPolynomial (Fin 5) K

def compressedEps : CompressedContact K := MvPolynomial.X 0
def compressedE : CompressedContact K := MvPolynomial.X 1
def compressedR : CompressedContact K := MvPolynomial.X 2
def compressedS : CompressedContact K := MvPolynomial.X 3
def compressedZ : CompressedContact K := MvPolynomial.X 4

def compressedY (u0 u1 : K) : CompressedContact K :=
  MvPolynomial.C u0 + MvPolynomial.C u1 * compressedZ + compressedE +
    compressedEps * compressedR -
      MvPolynomial.C (2 : K)⁻¹ * compressedEps ^ 2 * compressedS

/-- Row substitution: `E -> epsilon^3*T` and compressed curvature
`S_compressed -> 2*S_formal`. -/
def compressedToFormal : CompressedContact K →ₐ[K] FlatContact K :=
  MvPolynomial.aeval
    ![eps, eps ^ 3 * localT, localR,
      MvPolynomial.C (2 : K) * localS, localZ]

@[simp] theorem compressedToFormal_C (c : K) :
    compressedToFormal (K := K) (MvPolynomial.C c) =
      MvPolynomial.C c := by
  simp [compressedToFormal]

@[simp] theorem compressedToFormal_eps :
    compressedToFormal (K := K) compressedEps = eps := by
  simp [compressedToFormal, compressedEps]

@[simp] theorem compressedToFormal_E :
    compressedToFormal (K := K) compressedE = eps ^ 3 * localT := by
  simp [compressedToFormal, compressedE]

@[simp] theorem compressedToFormal_R :
    compressedToFormal (K := K) compressedR = localR := by
  simp [compressedToFormal, compressedR]

@[simp] theorem compressedToFormal_S :
    compressedToFormal (K := K) compressedS =
      MvPolynomial.C (2 : K) * localS := by
  simp [compressedToFormal, compressedS]

@[simp] theorem compressedToFormal_Z :
    compressedToFormal (K := K) compressedZ = localZ := by
  simp [compressedToFormal, compressedZ]

theorem compressedY_maps_to_contactedY
    (u0 u1 : K) (htwo : (2 : K) ≠ 0) :
    compressedToFormal (K := K) (compressedY u0 u1) =
      contactedY u0 u1 := by
  simp only [compressedY, map_add, map_sub, map_mul, map_pow,
    compressedToFormal_C, compressedToFormal_eps, compressedToFormal_E,
    compressedToFormal_R, compressedToFormal_S, compressedToFormal_Z,
    contactedY]
  have hscale :
      (MvPolynomial.C ((2 : K)⁻¹) : FlatContact K) *
          MvPolynomial.C (2 : K) = 1 := by
    rw [← MvPolynomial.C_mul]
    simp [htwo]
  calc
    _ = MvPolynomial.C u0 + MvPolynomial.C u1 * localZ +
          eps * localR - eps ^ 2 *
            (MvPolynomial.C ((2 : K)⁻¹) * MvPolynomial.C (2 : K)) * localS +
          eps ^ 3 * localT := by ring
    _ = contactedY u0 u1 := by rw [hscale]; simp [contactedY]

def compressedRawContactColumn
    (x u0 u1 : K) (a s y r z : Nat) : CompressedContact K :=
  (MvPolynomial.C x + compressedEps) ^ a * compressedS ^ s *
    compressedY u0 u1 ^ y * compressedR ^ r * compressedZ ^ z

/-- Each raw source curvature exponent contributes only the invertible
column factor `2^s`; all other changes are row relabelings/scalings. -/
theorem compressedRawContactColumn_maps_to_formal
    (x u0 u1 : K) (a s y r z : Nat) (htwo : (2 : K) ≠ 0) :
    compressedToFormal (K := K)
        (compressedRawContactColumn x u0 u1 a s y r z) =
      MvPolynomial.C ((2 : K) ^ s) *
        rawContactColumn x u0 u1 a s y r z := by
  simp only [compressedRawContactColumn, map_mul, map_pow, map_add,
    compressedToFormal_C, compressedToFormal_eps, compressedToFormal_R, compressedToFormal_S,
    compressedToFormal_Z, compressedY_maps_to_contactedY u0 u1 htwo,
    rawContactColumn]
  rw [mul_pow]
  rw [← MvPolynomial.C_pow]
  ring

structure CompressedIndex where
  q : Nat
  b : Nat
  r : Nat
  s : Nat
  z : Nat
deriving DecidableEq

structure FormalIndex where
  epsilon : Nat
  s : Nat
  t : Nat
  r : Nat
  z : Nat
deriving DecidableEq

/-- Literal exponent relabeling on monomial rows. -/
def compressedIndexMap (i : CompressedIndex) : FormalIndex where
  epsilon := i.q + 3 * i.b
  s := i.s
  t := i.b
  r := i.r
  z := i.z

theorem compressedIndexMap_injective :
    Function.Injective compressedIndexMap := by
  intro i j h
  cases i with
  | mk iq ib ir is iz =>
    cases j with
    | mk jq jb jr js jz =>
      simp only [compressedIndexMap, FormalIndex.mk.injEq] at h
      simp only [CompressedIndex.mk.injEq]
      omega

theorem compressed_truncation_is_formal_truncation
    (q b m : Nat) :
    q + 3 * b < m ↔ (compressedIndexMap
      ⟨q, b, 0, 0, 0⟩).epsilon < m := by
  rfl

theorem compressed_curvature_column_scale_ne_zero
    (s : Nat) (htwo : (2 : K) ≠ 0) :
    (2 : K) ^ s ≠ 0 := by
  exact pow_ne_zero s htwo

/-- The corrected selector for the formal high head. -/
theorem compressed_row_is_in_formal_head
    (q b : Nat) :
    3 ≤ (compressedIndexMap ⟨q, b, 0, 0, 0⟩).epsilon ↔
      3 ≤ q + 3 * b := by
  rfl

#print axioms compressedY_maps_to_contactedY
#print axioms compressedRawContactColumn_maps_to_formal
#print axioms compressedIndexMap_injective
#print axioms compressed_truncation_is_formal_truncation
#print axioms compressed_curvature_column_scale_ne_zero
#print axioms compressed_row_is_in_formal_head

end
end ProximityPrize.SubmissionLower.K0CompressedFormalContactEquiv6900
