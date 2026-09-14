import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Exact countergate for the proposed Full187 top-curvature carrier extraction.

This file deliberately rebuilds only the six definitions needed from the
order-two source scaffold.  That keeps this falsifier independent of the
large experimental import chain while using literally the same formulas.

The local substitution fixes the formal curvature variable `S`, but its image
of the source variable `Y` also contains `-(Z^2 / 2) S`.  Consequently inner
`S`-differentiation does not commute with local substitution.

At the actual Full187 contact order, the source polynomial

  `Q = X^57 * (Y - X*R + (X^2/2)*S)`

specializes at the zero node to `Z^57 E`, which has contact weight `60`.
Its (top) first curvature derivative is `(1/2) X^59`; after specialization
this has contact weight `59`, so the same order-60 contact condition is false.
-/

namespace ProximityPrize.Experiments.Full187TopCurvatureCarrierStop6900

open MvPolynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

abbrev Poly4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

def zVar (K : Type*) [CommRing K] : Poly4 K := X 0
def eVar (K : Type*) [CommRing K] : Poly4 K := X 1
def rVar (K : Type*) [CommRing K] : Poly4 K := X 2
def sVar (K : Type*) [CommRing K] : Poly4 K := X 3

def halfZSquared (K : Type*) [Field K] : Poly4 K :=
  (2 : K)⁻¹ • zVar K ^ 2

def contactY (K : Type*) [Field K] : Poly4 K :=
  eVar K + zVar K * rVar K - halfZSquared K * sVar K

private def localVariables (K : Type*) [Field K]
    (x u : K) (i : Fin 4) : Poly4 K :=
  if i = 0 then C x + zVar K
  else if i = 1 then C u + contactY K
  else if i = 2 then rVar K
  else sVar K

def localSubstitution (K : Type*) [Field K]
    (x u : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (localVariables K x u)

def sourceLiftedE (K : Type*) [Field K] : Poly4 K :=
  eVar K - zVar K * rVar K + halfZSquared K * sVar K

def counterexampleQ (K : Type*) [Field K] : Poly4 K :=
  zVar K ^ 57 * sourceLiftedE K

@[simp] theorem localSubstitution_zVar
    (K : Type*) [Field K] (x u : K) :
    localSubstitution K x u (zVar K) = C x + zVar K := by
  simp [localSubstitution, localVariables, zVar]

@[simp] theorem localSubstitution_eVar
    (K : Type*) [Field K] (x u : K) :
    localSubstitution K x u (eVar K) = C u + contactY K := by
  simp [localSubstitution, localVariables, eVar]

@[simp] theorem localSubstitution_rVar
    (K : Type*) [Field K] (x u : K) :
    localSubstitution K x u (rVar K) = rVar K := by
  simp [localSubstitution, localVariables, rVar]

@[simp] theorem localSubstitution_sVar
    (K : Type*) [Field K] (x u : K) :
    localSubstitution K x u (sVar K) = sVar K := by
  simp [localSubstitution, localVariables, sVar]

@[simp] theorem localSubstitution_halfZSquared
    (K : Type*) [Field K] (x u : K) :
    localSubstitution K x u (halfZSquared K) =
      (2 : K)⁻¹ • (C x + zVar K) ^ 2 := by
  simp [halfZSquared, Algebra.smul_def]

@[simp] theorem local_zero_sourceLiftedE {K : Type*} [Field K] :
    localSubstitution K 0 0 (sourceLiftedE K) = eVar K := by
  simp only [sourceLiftedE, map_add, map_sub, map_mul,
    localSubstitution_zVar, localSubstitution_eVar,
    localSubstitution_rVar, localSubstitution_sVar,
    localSubstitution_halfZSquared, map_zero, zero_add]
  simp [contactY, halfZSquared, Algebra.smul_def]
  ring

theorem local_zero_counterexampleQ {K : Type*} [Field K] :
    localSubstitution K 0 0 (counterexampleQ K) =
      zVar K ^ 57 * eVar K := by
  simp [counterexampleQ]

@[simp] theorem pderiv_s_zVar {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (zVar K) = 0 := by
  simp [zVar]

@[simp] theorem pderiv_s_eVar {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (eVar K) = 0 := by
  simp [eVar]

@[simp] theorem pderiv_s_rVar {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (rVar K) = 0 := by
  simp [rVar]

@[simp] theorem pderiv_s_sVar {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (sVar K) = 1 := by
  simp [sVar]

@[simp] theorem pderiv_s_halfZSquared {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (halfZSquared K) = 0 := by
  simp [halfZSquared, Algebra.smul_def]

theorem pderiv_s_sourceLiftedE {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (sourceLiftedE K) =
      halfZSquared K := by
  simp [sourceLiftedE]

theorem pderiv_s_counterexampleQ {K : Type*} [Field K] :
    MvPolynomial.pderiv (3 : Fin 4) (counterexampleQ K) =
      (2 : K)⁻¹ • zVar K ^ 59 := by
  rw [counterexampleQ, MvPolynomial.pderiv_mul, pderiv_s_sourceLiftedE]
  simp [halfZSquared, Algebra.smul_def]
  ring

theorem local_zero_top_derivative {K : Type*} [Field K] :
    localSubstitution K 0 0
        (MvPolynomial.pderiv (3 : Fin 4) (counterexampleQ K)) =
      (2 : K)⁻¹ • zVar K ^ 59 := by
  rw [pderiv_s_counterexampleQ]
  simp

/-! Literal copy of the contact weight and its low-weight truncation. -/

def shiftedContactWeight (d : Fin 4 →₀ Nat) : Nat := d 0 + 3 * d 1

noncomputable def contactTruncation {K : Type*} [Field K]
    (m : Nat) (P : Poly4 K) : Poly4 K :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.filter (fun d : Fin 4 →₀ Nat => shiftedContactWeight d < m)
      (AddMonoidAlgebra.coeff P))

theorem coeff_contactTruncation {K : Type*} [Field K]
    (m : Nat) (P : Poly4 K) (d : Fin 4 →₀ Nat) :
    MvPolynomial.coeff d (contactTruncation m P) =
      if shiftedContactWeight d < m then MvPolynomial.coeff d P else 0 := by
  classical
  change (Finsupp.filter
      (fun e : Fin 4 →₀ Nat => shiftedContactWeight e < m)
      (AddMonoidAlgebra.coeff P)) d = _
  rw [Finsupp.filter_apply]
  rfl

def expZE (a b : Nat) : Fin 4 →₀ Nat :=
  Finsupp.single 0 a + Finsupp.single 1 b

theorem z_pow_mul_e_pow_eq_monomial {K : Type*} [Field K]
    (a b : Nat) :
    zVar K ^ a * eVar K ^ b =
      MvPolynomial.monomial (expZE a b) 1 := by
  simp [zVar, eVar, expZE, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul]

theorem shiftedContactWeight_expZE (a b : Nat) :
    shiftedContactWeight (expZE a b) = a + 3 * b := by
  simp [shiftedContactWeight, expZE]

theorem original_contact_order_sixty {K : Type*} [Field K] :
    contactTruncation 60
      (localSubstitution K 0 0 (counterexampleQ K)) = 0 := by
  rw [local_zero_counterexampleQ]
  have hmono := z_pow_mul_e_pow_eq_monomial (K := K) 57 1
  simp only [pow_one] at hmono
  rw [hmono]
  ext d
  rw [coeff_contactTruncation]
  by_cases hd : d = expZE 57 1
  · subst d
    simp [shiftedContactWeight_expZE]
  · have hne : expZE 57 1 ≠ d := Ne.symm hd
    simp [MvPolynomial.coeff_monomial, hne]

theorem extracted_contact_order_sixty_fails {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) :
    contactTruncation 60
      (localSubstitution K 0 0
        (MvPolynomial.pderiv (3 : Fin 4) (counterexampleQ K))) ≠ 0 := by
  rw [local_zero_top_derivative]
  intro hzero
  have hcoeff := congrArg
    (MvPolynomial.coeff (expZE 59 0)) hzero
  rw [coeff_contactTruncation] at hcoeff
  have hw : shiftedContactWeight (expZE 59 0) < 60 := by
    rw [shiftedContactWeight_expZE]
    norm_num
  rw [if_pos hw] at hcoeff
  have hzpow : zVar K ^ 59 =
      MvPolynomial.monomial (expZE 59 0) 1 := by
    simpa only [pow_zero, mul_one] using
      (z_pow_mul_e_pow_eq_monomial (K := K) 59 0)
  rw [hzpow] at hcoeff
  simp [MvPolynomial.coeff_monomial] at hcoeff
  exact h2 hcoeff

/-! Every monomial in `Q` lies in the literal Full187 source support. -/

def Full187Admissible (a y r s seed : Nat) : Prop :=
  y + r + s ≤ 82 ∧ r + s ≤ 21 ∧ s ≤ 10 ∧
    seed + y + r + s ≤ 2703 ∧
    a + 131071 * y + 131070 * r + 131069 * s < 10824780

theorem y_term_admissible : Full187Admissible 57 1 0 0 0 := by
  norm_num [Full187Admissible]

theorem r_term_admissible : Full187Admissible 58 0 1 0 0 := by
  norm_num [Full187Admissible]

theorem s_term_admissible : Full187Admissible 59 0 0 1 0 := by
  norm_num [Full187Admissible]

/-! If one differentiates `d > 0` times and grants the best general contact
loss `60-d`, the weighted-degree saving is still too small for root forcing.
The deficit is `49344*d`. -/

theorem extracted_degree_budget_identity (d : Nat) (hd : d ≤ 10) :
    (60 - d) * 180413 + 49344 * d = 10824780 - 131069 * d := by
  omega

theorem extracted_root_forcing_budget_fails (d : Nat)
    (hdpos : 0 < d) (hd : d ≤ 10) :
    (60 - d) * 180413 < 10824780 - 131069 * d := by
  have hid := extracted_degree_budget_identity d hd
  omega

theorem counterexampleQ_three_terms {K : Type*} [Field K] :
    counterexampleQ K =
      zVar K ^ 57 * eVar K - zVar K ^ 58 * rVar K +
        (2 : K)⁻¹ • (zVar K ^ 59 * sVar K) := by
  simp [counterexampleQ, sourceLiftedE, halfZSquared, Algebra.smul_def]
  ring

#print axioms local_zero_counterexampleQ
#print axioms pderiv_s_counterexampleQ
#print axioms original_contact_order_sixty
#print axioms extracted_contact_order_sixty_fails
#print axioms y_term_admissible
#print axioms r_term_admissible
#print axioms s_term_admissible
#print axioms extracted_degree_budget_identity
#print axioms extracted_root_forcing_budget_fails

end
end ProximityPrize.Experiments.Full187TopCurvatureCarrierStop6900
