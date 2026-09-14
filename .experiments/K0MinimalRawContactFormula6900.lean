import K0RawIndexContactCore6900

/-!
# Literal raw-monomial formula over the minimal k0 contact core

This exposes the exact polynomial seen by the m47 contact map without
re-importing `LowerGeometry`.  Variables in the global source are ordered
`(X,S,Y,R,Z)` and variables in the complete local target are ordered
`(S,T,R,Z)`.  Hence the received-value coordinate becomes

```text
u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

The theorem is the algebraic input to the 47-coordinate top-shell
observability gate.  It makes no rank or confluence claim.
-/

namespace ProximityPrize.SubmissionLower.K0MinimalRawContactFormula6900

open MvPolynomial
open K0RawIndexContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

def rawMonomial (a s y r z : Nat) : FlatPoly K :=
  (MvPolynomial.X 0) ^ a * (MvPolynomial.X 1) ^ s *
    (MvPolynomial.X 2) ^ y * (MvPolynomial.X 3) ^ r *
      (MvPolynomial.X 4) ^ z

def contactedY (u0 u1 : K) : Target K :=
  Polynomial.C (MvPolynomial.C u0) +
    Polynomial.C (MvPolynomial.C u1) *
      Polynomial.C (MvPolynomial.X (3 : Fin 4)) +
    Polynomial.X * Polynomial.C (MvPolynomial.X (2 : Fin 4)) -
    Polynomial.X ^ 2 * Polynomial.C (MvPolynomial.X (0 : Fin 4)) +
    Polynomial.X ^ 3 * Polynomial.C (MvPolynomial.X (1 : Fin 4))

theorem flatEquiv_X (j : Fin 5) :
    flatEquiv (K := K) (MvPolynomial.X j) =
      ![Polynomial.X, Polynomial.C Polynomial.X,
        Polynomial.C (Polynomial.C (MvPolynomial.X 0)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 1)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 2))] j := by
  have h0 : flatEquiv (K := K) (MvPolynomial.X 0) = Polynomial.X := by
    change Polynomial.map _
      ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0)) = _
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  have hs (i : Fin 4) :
      flatEquiv (K := K) (MvPolynomial.X i.succ) =
        Polynomial.C ((MvPolynomial.finSuccEquiv K 3)
          (MvPolynomial.X i)) := by
    change Polynomial.map _
      ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X i.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    rfl
  fin_cases j
  · exact h0
  · change flatEquiv (K := K) (MvPolynomial.X (0 : Fin 4).succ) =
      Polynomial.C Polynomial.X
    rw [hs, MvPolynomial.finSuccEquiv_X_zero]
  · change flatEquiv (K := K)
      (MvPolynomial.X ((0 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K)
      (MvPolynomial.X ((1 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K)
      (MvPolynomial.X ((2 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl

@[simp] theorem flatEquiv_C (c : K) :
    flatEquiv (K := K) (MvPolynomial.C c) =
      Polynomial.C (Polynomial.C (MvPolynomial.C c)) := by
  change flatEquiv (K := K) (algebraMap K (FlatPoly K) c) =
    algebraMap K (Jet K) c
  exact (flatEquiv (K := K)).commutes c

@[simp] theorem contact_X :
    contact (K := K) Polynomial.X = Polynomial.X := by
  simp [contact]

@[simp] theorem contact_C_C (p : LocalBase K) :
    contact (K := K) (Polynomial.C (Polynomial.C p)) =
      baseEval (K := K) p := by
  simp [contact, innerEval]

@[simp] theorem contact_C_X :
    contact (K := K) (Polynomial.C Polynomial.X) =
      Polynomial.C (MvPolynomial.X 0) := by
  simp [contact, innerEval]

@[simp] theorem contact_flatEquiv_C (c : K) :
    contact (K := K) (flatEquiv (K := K) (MvPolynomial.C c)) =
      Polynomial.C (MvPolynomial.C c) := by
  rw [flatEquiv_C, contact_C_C]
  change baseEval (K := K) (algebraMap K (LocalBase K) c) =
    algebraMap K (Target K) c
  exact (baseEval (K := K)).commutes c

theorem algebraMap_target (c : K) :
    algebraMap K (Target K) c =
      Polynomial.C (MvPolynomial.C c) := by
  rfl

theorem localize_X0 (x u0 u1 : K) :
    localize x u0 u1 (MvPolynomial.X 0) =
      MvPolynomial.C x + MvPolynomial.X 0 := by
  simp [localize]

theorem localize_X1 (x u0 u1 : K) :
    localize x u0 u1 (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [localize]

theorem localize_X2 (x u0 u1 : K) :
    localize x u0 u1 (MvPolynomial.X 2) =
      MvPolynomial.C u0 + MvPolynomial.C u1 * MvPolynomial.X 4 +
        MvPolynomial.X 0 * MvPolynomial.X 2 := by
  simp [localize]

theorem localize_X3 (x u0 u1 : K) :
    localize x u0 u1 (MvPolynomial.X 3) = MvPolynomial.X 3 := by
  simp [localize]

theorem localize_X4 (x u0 u1 : K) :
    localize x u0 u1 (MvPolynomial.X 4) = MvPolynomial.X 4 := by
  simp [localize]

theorem contact_flatEquiv_localize_X0 (x u0 u1 : K) :
    contact (K := K)
        (flatEquiv (K := K) (localize x u0 u1 (MvPolynomial.X 0))) =
      Polynomial.C (MvPolynomial.C x) + Polynomial.X := by
  rw [localize_X0, map_add, map_add, contact_flatEquiv_C]
  simp [flatEquiv_X]

theorem contact_flatEquiv_localize_X1 (x u0 u1 : K) :
    contact (K := K)
        (flatEquiv (K := K) (localize x u0 u1 (MvPolynomial.X 1))) =
      Polynomial.C (MvPolynomial.X (0 : Fin 4)) := by
  rw [localize_X1]
  simp [flatEquiv_X]

theorem contact_flatEquiv_localize_X2 (x u0 u1 : K) :
    contact (K := K)
        (flatEquiv (K := K) (localize x u0 u1 (MvPolynomial.X 2))) =
      contactedY (K := K) u0 u1 := by
  rw [localize_X2]
  simp only [map_add, map_mul, flatEquiv_C, flatEquiv_X,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    contact_C_C, contact_C_X, contact_X, baseEval,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, algebraMap_target]
  simp only [contactedY]
  ring

theorem contact_flatEquiv_localize_X3 (x u0 u1 : K) :
    contact (K := K)
        (flatEquiv (K := K) (localize x u0 u1 (MvPolynomial.X 3))) =
      Polynomial.C (MvPolynomial.X (2 : Fin 4)) := by
  rw [localize_X3]
  simp [flatEquiv_X, baseEval]

theorem contact_flatEquiv_localize_X4 (x u0 u1 : K) :
    contact (K := K)
        (flatEquiv (K := K) (localize x u0 u1 (MvPolynomial.X 4))) =
      Polynomial.C (MvPolynomial.X (3 : Fin 4)) := by
  rw [localize_X4]
  simp [flatEquiv_X, baseEval]

theorem contact_flatEquiv_localize_rawMonomial
    (x u0 u1 : K) (a s y r z : Nat) :
    contact (K := K)
        (flatEquiv (K := K)
          (localize x u0 u1 (rawMonomial (K := K) a s y r z))) =
      (Polynomial.C (MvPolynomial.C x) + Polynomial.X) ^ a *
        Polynomial.C (MvPolynomial.X (0 : Fin 4)) ^ s *
        contactedY (K := K) u0 u1 ^ y *
        Polynomial.C (MvPolynomial.X (2 : Fin 4)) ^ r *
        Polynomial.C (MvPolynomial.X (3 : Fin 4)) ^ z := by
  simp only [rawMonomial, map_mul, map_pow,
    contact_flatEquiv_localize_X0, contact_flatEquiv_localize_X1,
    contact_flatEquiv_localize_X2, contact_flatEquiv_localize_X3,
    contact_flatEquiv_localize_X4]

#print axioms contact_flatEquiv_localize_X0
#print axioms contact_flatEquiv_localize_X1
#print axioms contact_flatEquiv_localize_X2
#print axioms contact_flatEquiv_localize_X3
#print axioms contact_flatEquiv_localize_X4
#print axioms contact_flatEquiv_localize_rawMonomial

end

end ProximityPrize.SubmissionLower.K0MinimalRawContactFormula6900
