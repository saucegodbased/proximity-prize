import K0ZeroCostPureSeedDualEdge6900
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# Literal raw R/S connection and its filtered quotient transpose

Flatten the complete m47 contact target in coordinate order
`(epsilon,S,T,R,Z)`.  The contacted received-value coordinate is

```text
V = u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

The local connection

```text
delta = d/depsilon + 2 S d/dR + 3 T d/dS
```

satisfies `delta V=R` and `delta R=2S`.  Consequently the complete raw
`{1,R}` and `S` columns obey two sparse identities.  They are the literal
primal identities behind the first and second Spencer steps; no selected
contact projection is used.

The second half records what the tapered quotient pairing gives before a
global connection/confluence theorem is supplied.  An isolated raw R strip
leaves a degree-`<w-1` defect, and an isolated raw S strip leaves a
degree-`<w-2` defect.  Thus the local connection identifies the desired
coupling, but does not by itself prove that a compatible dual is stable under
the transposed connection.
-/

namespace ProximityPrize.SubmissionLower.K0RawRSConnectionTranspose6900

open scoped BigOperators
open Polynomial
open HrsQuotientTopPairing6900
open K0FilteredCrtGroebnerDual6900
open K0ZeroCostPureSeedDualEdge6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-! ## Literal flattened contact algebra -/

abbrev FlatContact (K : Type*) [Field K] := MvPolynomial (Fin 5) K

def eps : FlatContact K := MvPolynomial.X 0
def localS : FlatContact K := MvPolynomial.X 1
def localT : FlatContact K := MvPolynomial.X 2
def localR : FlatContact K := MvPolynomial.X 3
def localZ : FlatContact K := MvPolynomial.X 4

def contactedY (u0 u1 : K) : FlatContact K :=
  MvPolynomial.C u0 + MvPolynomial.C u1 * localZ +
    eps * localR - eps ^ 2 * localS + eps ^ 3 * localT

/-- The exact flattened contact image of the global raw monomial in
coordinate order `(X,S,Y,R,Z)`. -/
def rawContactColumn
    (x u0 u1 : K) (a s y r z : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * localS ^ s *
    contactedY u0 u1 ^ y * localR ^ r * localZ ^ z

/-- Hasse-normalized local jet connection. -/
def localConnection (P : FlatContact K) : FlatContact K :=
  MvPolynomial.pderiv 0 P +
    2 * localS * MvPolynomial.pderiv 3 P +
    3 * localT * MvPolynomial.pderiv 1 P

theorem localConnection_add (P Q : FlatContact K) :
    localConnection (P + Q) = localConnection P + localConnection Q := by
  simp [localConnection]
  ring

theorem localConnection_mul (P Q : FlatContact K) :
    localConnection (P * Q) =
      localConnection P * Q + P * localConnection Q := by
  simp [localConnection, MvPolynomial.pderiv_mul]
  ring

theorem localConnection_eps : localConnection (eps (K := K)) = 1 := by
  simp [localConnection, eps, localS, localT, localR, Pi.single_apply]

theorem localConnection_localS :
    localConnection (localS (K := K)) =
      3 * localT := by
  simp [localConnection, eps, localS, localT, localR, Pi.single_apply]

theorem localConnection_localR :
    localConnection (localR (K := K)) =
      2 * localS := by
  simp [localConnection, eps, localS, localT, localR, Pi.single_apply]

theorem localConnection_localZ :
    localConnection (localZ (K := K)) = 0 := by
  simp [localConnection, eps, localS, localT, localR, localZ,
    Pi.single_apply]

/-- The key exact cancellation: the `-epsilon^2 S` and `epsilon^3 T`
terms are precisely what makes the contacted value differentiate to R. -/
theorem localConnection_contactedY (u0 u1 : K) :
    localConnection (contactedY (K := K) u0 u1) = localR := by
  simp [localConnection, contactedY, eps, localS, localT, localR, localZ,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, Pi.single_apply]
  ring

/-! ## Sparse raw-column recurrences -/

/-- First Spencer step.  Differentiating a raw base/Y column uses only the
same base shape and the raw R shape. -/
theorem localConnection_raw_base_to_R
    (x u0 u1 : K) (a y z : Nat) :
    localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 (y + 1) 0 z) =
      ((a + 1 : Nat) : K) •
          rawContactColumn x u0 u1 a 0 (y + 1) 0 z +
        ((y + 1 : Nat) : K) •
          rawContactColumn x u0 u1 (a + 1) 0 y 1 z := by
  simp [rawContactColumn, localConnection, contactedY, eps, localS, localT,
    localR, localZ, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.smul_eq_C_mul, map_natCast, Pi.single_apply]
  ring

/-- Second Spencer step at Y-degree zero.  This is the clean R--S edge seen
in the stable raw-layer experiment; no R^2 column is present. -/
theorem localConnection_raw_R_to_S
    (x u0 u1 : K) (a z : Nat) :
    localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 0 1 z) =
      ((a + 1 : Nat) : K) •
          rawContactColumn x u0 u1 a 0 0 1 z +
        rawContactColumn x u0 u1 (a + 1) 1 0 0 z +
        rawContactColumn x u0 u1 (a + 1) 1 0 0 z := by
  simp [rawContactColumn, localConnection, contactedY, eps, localS, localT,
    localR, localZ, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.smul_eq_C_mul, map_natCast, Pi.single_apply]
  ring

/-- At positive Y-degree the same second step also produces R^2.  This
explains why `R^2` appears in the complete filtration even though the finite
ablation shows that it does not supply a new boundary direction. -/
theorem localConnection_raw_YR_to_R2S
    (x u0 u1 : K) (a y z : Nat) :
    localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 (y + 1) 1 z) =
      ((a + 1 : Nat) : K) •
          rawContactColumn x u0 u1 a 0 (y + 1) 1 z +
        ((y + 1 : Nat) : K) •
          rawContactColumn x u0 u1 (a + 1) 0 y 2 z +
        rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 0 z +
        rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 0 z := by
  simp [rawContactColumn, localConnection, contactedY, eps, localS, localT,
    localR, localZ, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.smul_eq_C_mul, map_natCast, Pi.single_apply]
  ring

/-! ## Profile-parametric source legality

The relaxed source has four independent shape bounds in addition to the
weighted X cutoff.  Packaging those literal inequalities makes clear that
the connection needs only `B >= 2` and one S layer.  It preserves both the
active-degree cap `U` and the passive cap `L` exactly, so none of the proofs
below hard-code `(s,L)=(8,3757)` or `(6,5107)`. -/

def rawShapeLegal
    (D w L B sCap U a s y r z : Nat) : Prop :=
  2 * s + r ≤ B ∧ s ≤ sCap ∧ s + y + r ≤ U ∧
    s + y + r + z ≤ L ∧
    a + w * y + (w - 1) * r + (w - 2) * s < D

theorem rawShapeLegal_base_to_R
    (D w L B sCap U a y z : Nat) (hw : 2 ≤ w) (hB : 1 ≤ B)
    (hlegal : rawShapeLegal D w L B sCap U (a + 1) 0 (y + 1) 0 z) :
    rawShapeLegal D w L B sCap U a 0 (y + 1) 0 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 0 y 1 z := by
  unfold rawShapeLegal at hlegal ⊢
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    Nat.mul_succ] at hlegal ⊢
  omega

theorem rawShapeLegal_R_to_S
    (D w L B sCap U a z : Nat) (hw : 2 ≤ w)
    (hB : 2 ≤ B) (hs : 1 ≤ sCap)
    (hlegal : rawShapeLegal D w L B sCap U (a + 1) 0 0 1 z) :
    rawShapeLegal D w L B sCap U a 0 0 1 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 1 0 0 z := by
  unfold rawShapeLegal at hlegal ⊢
  omega

theorem rawShapeLegal_YR_to_R2S
    (D w L B sCap U a y z : Nat) (hw : 2 ≤ w)
    (hB : 2 ≤ B) (hs : 1 ≤ sCap)
    (hlegal : rawShapeLegal D w L B sCap U (a + 1) 0 (y + 1) 1 z) :
    rawShapeLegal D w L B sCap U a 0 (y + 1) 1 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 0 y 2 z ∧
      rawShapeLegal D w L B sCap U (a + 1) 1 (y + 1) 0 z := by
  unfold rawShapeLegal at hlegal ⊢
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add,
    Nat.mul_succ] at hlegal ⊢
  omega

/-! Applying an arbitrary complete-contact dual gives the literal transpose
equations.  These lemmas do not assume that the dual composed with
`localConnection` is again represented by legal global source columns. -/

theorem dual_localConnection_raw_base_to_R
    (ell : Module.Dual K (FlatContact K))
    (x u0 u1 : K) (a y z : Nat) :
    ell (localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 (y + 1) 0 z)) =
      ((a + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 a 0 (y + 1) 0 z) +
        ((y + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 (a + 1) 0 y 1 z) := by
  rw [localConnection_raw_base_to_R, map_add]
  simp

theorem dual_localConnection_raw_R_to_S
    (ell : Module.Dual K (FlatContact K))
    (x u0 u1 : K) (a z : Nat) :
    ell (localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 0 1 z)) =
      ((a + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 a 0 0 1 z) +
        (2 : K) *
          ell (rawContactColumn x u0 u1 (a + 1) 1 0 0 z) := by
  rw [localConnection_raw_R_to_S]
  simp
  ring

theorem dual_localConnection_raw_YR_to_R2S
    (ell : Module.Dual K (FlatContact K))
    (x u0 u1 : K) (a y z : Nat) :
    ell (localConnection
        (rawContactColumn x u0 u1 (a + 1) 0 (y + 1) 1 z)) =
      ((a + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 a 0 (y + 1) 1 z) +
        ((y + 1 : Nat) : K) *
          ell (rawContactColumn x u0 u1 (a + 1) 0 y 2 z) +
        (2 : K) *
          ell (rawContactColumn x u0 u1 (a + 1) 1 (y + 1) 0 z) := by
  rw [localConnection_raw_YR_to_R2S]
  simp
  ring

/-! ## Literal boundary right sides -/

/-- Pairing of a boundary tangent `(lambdaS,lambdaY,lambdaR,lambdaZ)` with
the gradient of `X^a S^s Y^y R^r Z^z` at
`(xi,S0,Y0,R0,gamma)`. -/
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

theorem rawBoundaryScalar_pureSeed
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) (z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        0 0 0 z = pureSeedBoundaryScalar gamma lambdaZ z := by
  simp [rawBoundaryScalar, pureSeedBoundaryScalar]
  ring

theorem rawBoundaryScalar_pureSeed_one
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        0 0 0 1 = lambdaZ := by
  simp [rawBoundaryScalar]

theorem rawBoundaryScalar_R
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) (z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        0 0 1 z =
      lambdaR * gamma ^ z +
        lambdaZ * (z : K) * R0 * gamma ^ (z - 1) := by
  simp [rawBoundaryScalar]

theorem rawBoundaryScalar_R_zero
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        0 0 1 0 = lambdaR := by
  simp [rawBoundaryScalar]

/-- The R boundary coordinate is an affine translate of the pure-Z seed
coordinate.  This is the literal coupling seen by the quotient numerators. -/
theorem rawBoundaryScalar_R_eq_pureSeed_translate
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) (z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        0 0 1 z =
      lambdaR * gamma ^ z +
        R0 * pureSeedBoundaryScalar gamma lambdaZ z := by
  rw [rawBoundaryScalar_R]
  simp [pureSeedBoundaryScalar]
  ring

theorem rawBoundaryScalar_S
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) (z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        1 0 0 z =
      lambdaS * gamma ^ z +
        lambdaZ * (z : K) * S0 * gamma ^ (z - 1) := by
  simp [rawBoundaryScalar]

theorem rawBoundaryScalar_S_zero
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        1 0 0 0 = lambdaS := by
  simp [rawBoundaryScalar]

/-- The S boundary coordinate has the same affine pure-seed translate,
with `S0` in place of `R0`. -/
theorem rawBoundaryScalar_S_eq_pureSeed_translate
    (S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ : K) (z : Nat) :
    rawBoundaryScalar S0 Y0 R0 gamma lambdaS lambdaY lambdaR lambdaZ
        1 0 0 z =
      lambdaS * gamma ^ z +
        S0 * pureSeedBoundaryScalar gamma lambdaZ z := by
  rw [rawBoundaryScalar_S]
  simp [pureSeedBoundaryScalar]
  ring

/-! ## Filtered quotient consequence and exact remaining defect -/

/-- Scalar multiplication of the canonical quotient numerator represents
the corresponding scalar multiple of evaluation. -/
theorem quotientTopPairing_smul_evalNumerator
    (A : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M)
    (xi scalar : K) (p : K[X]_M) :
    quotientTopPairing A
        (scalar • (quotientEvalNumerator A M hM hA hAM xi).val)
        p.val M = scalar * p.val.eval xi := by
  have hmap :
      quotientTopDualMap A M
          (scalar • quotientEvalNumerator A M hM hA hAM xi) =
        scalar • boundedEvalFunctional M xi := by
    rw [map_smul, quotientEvalNumerator_spec]
  have h := LinearMap.congr_fun hmap p
  exact h

/-- A tapered evaluation equation determines a quotient numerator only up
to the complementary low-degree defect. -/
theorem filtered_window_eval_iff_low_degree_defect
    (A q : K[X]) (M c : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M)
    (hc0 : 0 < c) (hcM : c < M) (xi scalar : K) :
    (∀ p : K[X], p.natDegree < M - c →
      quotientTopPairing A q p M = scalar * p.eval xi) ↔
    ((q - scalar •
        (quotientEvalNumerator A M hM hA hAM xi).val) %ₘ A = 0 ∨
      ((q - scalar •
        (quotientEvalNumerator A M hM hA hAM xi).val) %ₘ A).natDegree < c) := by
  let e := quotientEvalNumerator A M hM hA hAM xi
  have hbase :
      (∀ p : K[X], p.natDegree < M - c →
          quotientTopPairing A (q - scalar • e.val) p M = 0) ↔
        (q - scalar • e.val) %ₘ A = 0 ∨
          ((q - scalar • e.val) %ₘ A).natDegree < c := by
    simpa only [one_mul, mul_one] using
      (annihilates_cost_window_iff_remainder_below_cost
        A (q - scalar • e.val) 1 M c hM hA hAM hc0 hcM)
  have hsub (p : K[X]) :
      quotientTopPairing A (q - scalar • e.val) p M =
        quotientTopPairing A q p M -
          quotientTopPairing A (scalar • e.val) p M := by
    simp only [quotientTopPairing, sub_mul, Polynomial.sub_modByMonic,
      Polynomial.coeff_sub]
  constructor
  · intro heval
    apply hbase.mp
    intro p hp
    have hpM : p.natDegree < M := by omega
    let pb : K[X]_M :=
      ⟨p, by
        rw [Polynomial.mem_degreeLT]
        by_cases hp0 : p = 0
        · rw [hp0, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe _
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).1 hpM⟩
    rw [hsub, heval p hp]
    have hscaled := quotientTopPairing_smul_evalNumerator
      A M hM hA hAM xi scalar pb
    simpa only [e, pb, sub_self] using congrArg
      (fun t : K ↦ scalar * p.eval xi - t) hscaled
  · intro hdefect p hp
    have hzero := hbase.mpr hdefect p hp
    have hpM : p.natDegree < M := by omega
    let pb : K[X]_M :=
      ⟨p, by
        rw [Polynomial.mem_degreeLT]
        by_cases hp0 : p = 0
        · rw [hp0, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe _
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).1 hpM⟩
    rw [hsub] at hzero
    have hscaled := quotientTopPairing_smul_evalNumerator
      A M hM hA hAM xi scalar pb
    rw [show quotientTopPairing A (scalar • e.val) p M =
        scalar * p.eval xi by simpa only [e, pb] using hscaled,
      sub_eq_zero] at hzero
    exact hzero

/-- Exact obstruction to reading a global jet relation from one tapered
strip: every prescribed evaluation scalar has a representative with a
nonzero complementary defect. -/
theorem exists_filtered_eval_packet_with_nonzero_defect
    (A : K[X]) (M c : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M)
    (hc0 : 0 < c) (hcM : c < M) (xi scalar : K) :
    ∃ q : K[X],
      (∀ p : K[X], p.natDegree < M - c →
        quotientTopPairing A q p M = scalar * p.eval xi) ∧
      (q - scalar •
          (quotientEvalNumerator A M hM hA hAM xi).val) %ₘ A ≠ 0 := by
  let e := quotientEvalNumerator A M hM hA hAM xi
  let q : K[X] := scalar • e.val + 1
  have honeMod : (1 : K[X]) %ₘ A = 1 := by
    apply (Polynomial.modByMonic_eq_self_iff hA).2
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hA.ne_zero, hAM]
    exact_mod_cast hM
  have hdefect :
      (q - scalar • e.val) %ₘ A = 1 := by
    simp [q, honeMod]
  refine ⟨q, ?_, ?_⟩
  · apply (filtered_window_eval_iff_low_degree_defect
      A q M c hM hA hAM hc0 hcM xi scalar).2
    right
    rw [hdefect, Polynomial.natDegree_one]
    exact hc0
  · rw [hdefect]
    exact one_ne_zero

/-- Target m47 raw-R strip.  Before coupling to the Y tower, its entire
unresolved quotient obstruction has degree `<131070 = w-1`. -/
theorem m47_raw_R_strip_iff_low_degree_defect
    (A q : K[X]) (g : Nat) (hg : 180413 ≤ g)
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * g)
    (xi scalar : K) :
    (∀ p : K[X], p.natDegree < 47 * g - 131070 →
      quotientTopPairing A q p (47 * g) = scalar * p.eval xi) ↔
    ((q - scalar •
        (quotientEvalNumerator A (47 * g) (by omega) hA hAdeg xi).val) %ₘ A = 0 ∨
      ((q - scalar •
        (quotientEvalNumerator A (47 * g) (by omega) hA hAdeg xi).val) %ₘ A).natDegree <
          131070) := by
  exact filtered_window_eval_iff_low_degree_defect
    A q (47 * g) 131070 (by omega) hA hAdeg (by norm_num) (by omega)
      xi scalar

/-- Target m47 raw-S strip.  Its isolated obstruction has degree
`<131069 = w-2`. -/
theorem m47_raw_S_strip_iff_low_degree_defect
    (A q : K[X]) (g : Nat) (hg : 180413 ≤ g)
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * g)
    (xi scalar : K) :
    (∀ p : K[X], p.natDegree < 47 * g - 131069 →
      quotientTopPairing A q p (47 * g) = scalar * p.eval xi) ↔
    ((q - scalar •
        (quotientEvalNumerator A (47 * g) (by omega) hA hAdeg xi).val) %ₘ A = 0 ∨
      ((q - scalar •
        (quotientEvalNumerator A (47 * g) (by omega) hA hAdeg xi).val) %ₘ A).natDegree <
          131069) := by
  exact filtered_window_eval_iff_low_degree_defect
    A q (47 * g) 131069 (by omega) hA hAdeg (by norm_num) (by omega)
      xi scalar

#print axioms localConnection_contactedY
#print axioms localConnection_raw_base_to_R
#print axioms localConnection_raw_R_to_S
#print axioms localConnection_raw_YR_to_R2S
#print axioms rawShapeLegal_base_to_R
#print axioms rawShapeLegal_R_to_S
#print axioms rawShapeLegal_YR_to_R2S
#print axioms dual_localConnection_raw_base_to_R
#print axioms dual_localConnection_raw_R_to_S
#print axioms dual_localConnection_raw_YR_to_R2S
#print axioms rawBoundaryScalar_pureSeed
#print axioms filtered_window_eval_iff_low_degree_defect
#print axioms exists_filtered_eval_packet_with_nonzero_defect
#print axioms m47_raw_R_strip_iff_low_degree_defect
#print axioms m47_raw_S_strip_iff_low_degree_defect

end

end ProximityPrize.SubmissionLower.K0RawRSConnectionTranspose6900
