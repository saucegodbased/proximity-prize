import ProximityPrize.SubmissionLower.LowerGeometry

/-!
# The ordinary low contact head already contains the boundary four-jet

For the literal second-jet contact substitution

`(X,S,Y,R,Z) -> (x+e,S,u0+u1*Z+e*R-e^2*S+e^3*T,R,Z)`,

the apparently transverse `Y` derivative is visible in the ordinary contact
block: it is the `e^3` coefficient of the derivative in the local `T`
coordinate.  The other three boundary derivatives are read at `e=0`, with
the elementary `u1*dY` correction in the `Z` coordinate.

This file proves the polynomial chain identities underlying that readout.
It is local algebra only; it does not assert that the global capped source is
surjective onto the old heads together with this four-scalar probe.
-/

namespace ProximityPrize.SubmissionLower.K0LowHeadContactBoundaryReadout6900

open MvPolynomial
open SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

abbrev Poly := MvPolynomial (Fin 5) K

/-- The literal contact at a node, in flat coordinates `(e,S,T,R,Z)`. -/
def contactAt (x u0 u1 : K) : Poly (K := K) →ₐ[K] Poly (K := K) :=
  (substitute (K := K)).comp (localize x u0 u1)

private theorem localize_chain_Y_X (x u0 u1 : K) (j : Fin 5) :
    pderiv 2 (localize x u0 u1 (MvPolynomial.X j)) =
      MvPolynomial.X 0 * localize x u0 u1
        (pderiv 2 (MvPolynomial.X j)) := by
  fin_cases j <;>
    simp [localize, pderiv_mul, Pi.single_apply] <;> ring

/-- Differentiating the localized polynomial in its local `A` coordinate
pulls out one epsilon and differentiates the global `Y` coordinate. -/
theorem localize_chain_Y (x u0 u1 : K) (P : Poly (K := K)) :
    pderiv 2 (localize x u0 u1 P) =
      MvPolynomial.X 0 * localize x u0 u1 (pderiv 2 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [localize]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add]
  | mul_X P j hP =>
      have hX := localize_chain_Y_X (K := K) x u0 u1 j
      simp only [map_mul, pderiv_mul, map_add, hP, hX]
      ring

private theorem substitute_chain_T_X (j : Fin 5) :
    pderiv 2 (substitute (K := K) (MvPolynomial.X j)) =
      MvPolynomial.X 0 ^ 2 * substitute (K := K)
        (pderiv 2 (MvPolynomial.X j)) := by
  fin_cases j <;>
    simp [substitute, pderiv_mul, pderiv_pow, Pi.single_apply] <;> ring

/-- Differentiating the flattened contact in local `T` pulls out `e^2` and
differentiates the pre-flattened local `A` coordinate. -/
theorem substitute_chain_T (P : Poly (K := K)) :
    pderiv 2 (substitute (K := K) P) =
      MvPolynomial.X 0 ^ 2 * substitute (K := K) (pderiv 2 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add]
  | mul_X P j hP =>
      have hX := substitute_chain_T_X (K := K) j
      simp only [map_mul, pderiv_mul, map_add, hP, hX]
      ring

/-- Exact transverse chain rule for the combined literal contact.  It is the
reason no augmented ambient-Y probe is needed once epsilon order three is
retained. -/
theorem contactAt_chain_T (x u0 u1 : K) (P : Poly (K := K)) :
    pderiv 2 (contactAt x u0 u1 P) =
      MvPolynomial.X 0 ^ 3 * contactAt x u0 u1 (pderiv 2 P) := by
  change pderiv 2 (substitute (K := K) (localize x u0 u1 P)) =
    MvPolynomial.X 0 ^ 3 *
      substitute (K := K) (localize x u0 u1 (pderiv 2 P))
  rw [substitute_chain_T, localize_chain_Y, map_mul]
  have he : substitute (K := K) (MvPolynomial.X 0) = MvPolynomial.X 0 := by
    simp [substitute]
  rw [he]
  ring

private theorem contactAt_chain_R_X (x u0 u1 : K) (j : Fin 5) :
    pderiv 3 (contactAt x u0 u1 (MvPolynomial.X j)) =
      contactAt x u0 u1 (pderiv 3 (MvPolynomial.X j)) +
        MvPolynomial.X 0 * contactAt x u0 u1
          (pderiv 2 (MvPolynomial.X j)) := by
  fin_cases j <;>
    simp [contactAt, localize, substitute, pderiv_mul, pderiv_pow,
      Pi.single_apply] <;> ring

/-- The local `R` derivative differs from the global `R` derivative by an
epsilon multiple of the global `Y` derivative. -/
theorem contactAt_chain_R (x u0 u1 : K) (P : Poly (K := K)) :
    pderiv 3 (contactAt x u0 u1 P) =
      contactAt x u0 u1 (pderiv 3 P) +
        MvPolynomial.X 0 * contactAt x u0 u1 (pderiv 2 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [contactAt, localize, substitute]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, add_assoc, add_left_comm,
      add_comm]
  | mul_X P j hP =>
      have hX := contactAt_chain_R_X (K := K) x u0 u1 j
      simp only [map_mul, pderiv_mul, map_add, hP, hX]
      ring

private theorem contactAt_chain_S_X (x u0 u1 : K) (j : Fin 5) :
    pderiv 1 (contactAt x u0 u1 (MvPolynomial.X j)) =
      contactAt x u0 u1 (pderiv 1 (MvPolynomial.X j)) -
        MvPolynomial.X 0 ^ 2 * contactAt x u0 u1
          (pderiv 2 (MvPolynomial.X j)) := by
  fin_cases j <;>
    simp [contactAt, localize, substitute, pderiv_mul, pderiv_pow,
      Pi.single_apply] <;> ring

/-- The local `S` derivative differs from the global `S` derivative by an
epsilon-squared multiple of the global `Y` derivative. -/
theorem contactAt_chain_S (x u0 u1 : K) (P : Poly (K := K)) :
    pderiv 1 (contactAt x u0 u1 P) =
      contactAt x u0 u1 (pderiv 1 P) -
        MvPolynomial.X 0 ^ 2 * contactAt x u0 u1 (pderiv 2 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [contactAt, localize, substitute]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, mul_add]
      ring
  | mul_X P j hP =>
      have hX := contactAt_chain_S_X (K := K) x u0 u1 j
      simp only [map_mul, pderiv_mul, map_add, hP, hX]
      ring

private theorem contactAt_chain_Z_X (x u0 u1 : K) (j : Fin 5) :
    pderiv 4 (contactAt x u0 u1 (MvPolynomial.X j)) =
      contactAt x u0 u1 (pderiv 4 (MvPolynomial.X j)) +
        MvPolynomial.C u1 * contactAt x u0 u1
          (pderiv 2 (MvPolynomial.X j)) := by
  fin_cases j <;>
    simp [contactAt, localize, substitute, pderiv_mul, pderiv_pow,
      Pi.single_apply] <;> ring

/-- The local `Z` derivative is `global-Z + u1 * global-Y`. -/
theorem contactAt_chain_Z (x u0 u1 : K) (P : Poly (K := K)) :
    pderiv 4 (contactAt x u0 u1 P) =
      contactAt x u0 u1 (pderiv 4 P) +
        MvPolynomial.C u1 * contactAt x u0 u1 (pderiv 2 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [contactAt, localize, substitute]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add, add_assoc, add_left_comm,
      add_comm]
  | mul_X P j hP =>
      have hX := contactAt_chain_Z_X (K := K) x u0 u1 j
      simp only [map_mul, pderiv_mul, map_add, hP, hX]
      ring

def epsCoeff (d : Nat) (P : Poly (K := K)) : MvPolynomial (Fin 4) K :=
  ((MvPolynomial.finSuccEquiv K 4) P).coeff d

/-- The epsilon-three coefficient after local `T` differentiation is exactly
the epsilon-zero contact of the global `Y` derivative. -/
theorem epsCoeff_three_pderiv_T_contactAt (x u0 u1 : K)
    (P : Poly (K := K)) :
    epsCoeff 3 (pderiv 2 (contactAt x u0 u1 P)) =
      epsCoeff 0 (contactAt x u0 u1 (pderiv 2 P)) := by
  have h := congrArg
    (fun Q : Poly (K := K) => ((MvPolynomial.finSuccEquiv K 4) Q).coeff 3)
    (contactAt_chain_T x u0 u1 P)
  simpa [epsCoeff, map_mul, MvPolynomial.finSuccEquiv_X_zero,
    Polynomial.coeff_X_pow_mul'] using h

/-- Setting local epsilon to zero in the contact is evaluation of the global
polynomial at `(x,S,u0+u1*Z,R,Z)`. -/
theorem eval_contactAt_zero (x u0 u1 s t r z : K)
    (P : Poly (K := K)) :
    MvPolynomial.eval ![0, s, t, r, z] (contactAt x u0 u1 P) =
      MvPolynomial.eval ![x, s, u0 + u1*z, r, z] P := by
  have h : (MvPolynomial.aeval ![0, s, t, r, z]).comp
      (contactAt x u0 u1) =
        MvPolynomial.aeval ![x, s, u0 + u1*z, r, z] := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [contactAt, localize, substitute] <;> ring
  exact DFunLike.congr_fun h P

/-- Evaluating at epsilon zero is the same as evaluating the epsilon-zero
coefficient in the remaining four variables. -/
theorem eval_epsCoeff_zero (s t r z : K) (Q : Poly (K := K)) :
    MvPolynomial.eval ![s, t, r, z] (epsCoeff 0 Q) =
      MvPolynomial.eval ![0, s, t, r, z] Q := by
  have h := MvPolynomial.eval_eq_eval_mv_eval'
    (R := K) ![s, t, r, z] 0 Q
  rw [Polynomial.eval_zero_map] at h
  rw [epsCoeff, Polynomial.coeff_zero_eq_eval_zero]
  exact h.symm

/-- The first scalar of the readout: the coefficient of `e^3*T` recovers
the global `Y` derivative at the compatible boundary point. -/
theorem recover_Y (x u0 u1 s t r z : K) (P : Poly (K := K)) :
    MvPolynomial.eval ![s, t, r, z]
        (epsCoeff 3 (pderiv 2 (contactAt x u0 u1 P))) =
      MvPolynomial.eval ![x, s, u0 + u1*z, r, z] (pderiv 2 P) := by
  rw [epsCoeff_three_pderiv_T_contactAt]
  rw [eval_epsCoeff_zero]
  exact eval_contactAt_zero x u0 u1 s t r z (pderiv 2 P)

/-- The epsilon-zero local `R` derivative is the global `R` derivative. -/
theorem recover_R (x u0 u1 s t r z : K) (P : Poly (K := K)) :
    MvPolynomial.eval ![0, s, t, r, z]
        (pderiv 3 (contactAt x u0 u1 P)) =
      MvPolynomial.eval ![x, s, u0 + u1*z, r, z] (pderiv 3 P) := by
  rw [contactAt_chain_R, map_add, map_mul]
  rw [eval_contactAt_zero, eval_contactAt_zero]
  simp

/-- The epsilon-zero local `S` derivative is the global `S` derivative. -/
theorem recover_S (x u0 u1 s t r z : K) (P : Poly (K := K)) :
    MvPolynomial.eval ![0, s, t, r, z]
        (pderiv 1 (contactAt x u0 u1 P)) =
      MvPolynomial.eval ![x, s, u0 + u1*z, r, z] (pderiv 1 P) := by
  rw [contactAt_chain_S, map_sub, map_mul]
  rw [eval_contactAt_zero, eval_contactAt_zero]
  simp

/-- Correcting the epsilon-zero local `Z` derivative by `u1*Y` recovers the
global `Z` derivative. -/
theorem recover_Z (x u0 u1 s t r z : K) (P : Poly (K := K)) :
    MvPolynomial.eval ![0, s, t, r, z]
          (pderiv 4 (contactAt x u0 u1 P)) -
        u1 * MvPolynomial.eval ![s, t, r, z]
          (epsCoeff 3 (pderiv 2 (contactAt x u0 u1 P))) =
      MvPolynomial.eval ![x, s, u0 + u1*z, r, z] (pderiv 4 P) := by
  rw [contactAt_chain_Z, map_add, map_mul]
  rw [eval_contactAt_zero, eval_contactAt_zero, recover_Y]
  simp

/-- The smallest useful extra-node probe: four scalar functionals of the
ordinary contact block, not an augmented ambient jet and not the entire local
block.  Coordinates are `(Y,R,S,Z)`. -/
def probeReadout (u1 s t r z : K) (Q : Poly (K := K)) : Fin 4 → K := ![
  MvPolynomial.eval ![s, t, r, z] (epsCoeff 3 (pderiv 2 Q)),
  MvPolynomial.eval ![0, s, t, r, z] (pderiv 3 Q),
  MvPolynomial.eval ![0, s, t, r, z] (pderiv 1 Q),
  MvPolynomial.eval ![0, s, t, r, z] (pderiv 4 Q) -
    u1 * MvPolynomial.eval ![s, t, r, z]
      (epsCoeff 3 (pderiv 2 Q))]

def boundaryReadout (x y s r z : K) (P : Poly (K := K)) : Fin 4 → K := ![
  MvPolynomial.eval ![x, s, y, r, z] (pderiv 2 P),
  MvPolynomial.eval ![x, s, y, r, z] (pderiv 3 P),
  MvPolynomial.eval ![x, s, y, r, z] (pderiv 1 P),
  MvPolynomial.eval ![x, s, y, r, z] (pderiv 4 P)]

/-- The literal four-boundary map factors through the ordinary low contact
head as soon as epsilon order three is present. -/
theorem probeReadout_contactAt (x u0 u1 s t r z : K)
    (P : Poly (K := K)) :
    probeReadout u1 s t r z (contactAt x u0 u1 P) =
      boundaryReadout x (u0 + u1*z) s r z P := by
  funext i
  fin_cases i
  · exact recover_Y x u0 u1 s t r z P
  · exact recover_R x u0 u1 s t r z P
  · exact recover_S x u0 u1 s t r z P
  · exact recover_Z x u0 u1 s t r z P

/-- A four-dimensional explicit section of the readout inside the ordinary
local polynomial space.  The `u1*Z` term is what cancels the `Z` correction
for the pure `Y` axis. -/
def readoutSection (u1 : K) (v : Fin 4 → K) : Poly (K := K) :=
  (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 2 +
      MvPolynomial.C u1 * MvPolynomial.X 4) *
        MvPolynomial.C (v 0) +
    MvPolynomial.C (v 1) * MvPolynomial.X 3 +
    MvPolynomial.C (v 2) * MvPolynomial.X 1 +
    MvPolynomial.C (v 3) * MvPolynomial.X 4

theorem probeReadout_readoutSection (u1 s t r z : K) (v : Fin 4 → K) :
    probeReadout u1 s t r z (readoutSection u1 v) = v := by
  have hcoeff (a : K) :
      MvPolynomial.eval ![s, t, r, z]
          ((((MvPolynomial.finSuccEquiv K 4)
            (MvPolynomial.C a)) * Polynomial.X ^ 3).coeff 3) = a := by
    rw [mul_comm, Polynomial.coeff_X_pow_mul]
    change MvPolynomial.eval ![s, t, r, z]
      (((MvPolynomial.finSuccEquiv K 4)
        (algebraMap K (Poly (K := K)) a)).coeff 0) = a
    rw [(MvPolynomial.finSuccEquiv K 4).commutes]
    simp
  funext i
  fin_cases i <;>
    simp [probeReadout, readoutSection, epsCoeff, pderiv_mul, pderiv_pow,
      MvPolynomial.finSuccEquiv_X_zero,
      MvPolynomial.finSuccEquiv_X_succ,
      Polynomial.coeff_X_pow_mul', hcoeff] <;> ring

theorem probeReadout_surjective (u1 s t r z : K) :
    Function.Surjective (probeReadout (K := K) u1 s t r z) := by
  intro v
  exact ⟨readoutSection u1 v, probeReadout_readoutSection u1 s t r z v⟩

#print axioms epsCoeff_three_pderiv_T_contactAt
#print axioms eval_contactAt_zero
#print axioms recover_Y
#print axioms recover_R
#print axioms recover_S
#print axioms recover_Z
#print axioms probeReadout_contactAt
#print axioms probeReadout_readoutSection
#print axioms probeReadout_surjective

#print axioms localize_chain_Y
#print axioms substitute_chain_T
#print axioms contactAt_chain_T
#print axioms contactAt_chain_R
#print axioms contactAt_chain_S
#print axioms contactAt_chain_Z

end

end ProximityPrize.SubmissionLower.K0LowHeadContactBoundaryReadout6900
