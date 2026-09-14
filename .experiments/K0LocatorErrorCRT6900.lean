import HrsCrtPairingBridge6900

/-!
# Agreement-locator / error-CRT bridge for the k0 route

This file separates two facts which must not be conflated.

* A locator grade `Lambda_G^q * V`, with `deg V < |E|`, can prescribe an
  arbitrary **value** independently at every error while its agreement
  Hasse coefficients of orders `< q` vanish.  Consequently the 47 locator
  grades can be used triangularly; one does not pay for 47 error jets in one
  polynomial.
* Prescribing all depth-`m` error jets at once is also possible, but costs
  `q*|G| + m*|E|` X-degree.  This cost is too large in the critical target
  SR windows.  Thus a proof which treats `q = 1` as killing all agreement
  jets, or which hides full Hermite interpolation in one source column, is
  invalid.

The results are pure polynomial/CRT statements.  They make no claim that the
universal local contact-kernel correction lifts through the tapered global
source; that is the remaining Schur/confluence theorem.
-/

namespace ProximityPrize.SubmissionLower.K0LocatorErrorCRT6900

open scoped BigOperators
open Polynomial
open BivariateTaylorJets6900
open HrsCrtPairingBridge6900
open HrsU0PoleCancellation6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

variable {K G E : Type*} [Field K]
  [Fintype G] [DecidableEq G] [Fintype E] [DecidableEq E]

/-- The squarefree locator of the agreement nodes (squarefreeness itself is
not needed below). -/
def agreementLocator (nodesG : G → K) : K[X] :=
  ∏ i, ((Polynomial.X : K[X]) - Polynomial.C (nodesG i))

theorem agreementLocator_monic (nodesG : G → K) :
    (agreementLocator nodesG).Monic := by
  classical
  unfold agreementLocator
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_sub_C (nodesG i)

theorem agreementLocator_natDegree (nodesG : G → K) :
    (agreementLocator nodesG).natDegree = Fintype.card G := by
  classical
  unfold agreementLocator
  rw [Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one]
  · intro i hi
    exact Polynomial.X_sub_C_ne_zero (nodesG i)

/-- The agreement locator is a unit at every error node. -/
theorem agreementLocator_eval_error_ne_zero
    (nodesG : G → K) (nodesE : E → K)
    (hcross : ∀ i j, nodesG i ≠ nodesE j) (j : E) :
    (agreementLocator nodesG).eval (nodesE j) ≠ 0 := by
  classical
  unfold agreementLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (Ne.symm (hcross i j))

/-- The agreement locator is coprime to the full depth-`m` error-jet
denominator.  This is the algebraic reason locator multiplication is
invertible on every error jet, not merely on values. -/
theorem agreementLocator_isCoprime_errorJetDenominator
    (nodesG : G → K) (nodesE : E → K)
    (hcross : ∀ i j, nodesG i ≠ nodesE j) (m : Nat) :
    IsCoprime (agreementLocator nodesG)
      (jetDenominator nodesE (fun _ ↦ m)) := by
  classical
  unfold agreementLocator jetDenominator
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero_of_ne (hcross i j)).isUnit).pow_right

/-- A locator grade has zero agreement Hasse coordinates strictly below its
locator order.  Notice the strict inequality `j < q`: a single locator does
not erase a depth-47 agreement jet. -/
theorem hasseAt_agreementLocator_pow_mul_eq_zero
    (nodesG : G → K) (q : Nat) (V : K[X]) (i : G) (j : Nat)
    (hj : j < q) :
    hasseAt (nodesG i) ((agreementLocator nodesG) ^ q * V) j = 0 := by
  classical
  have hfactor :
      ((Polynomial.X : K[X]) - Polynomial.C (nodesG i)) ∣
        agreementLocator nodesG := by
    unfold agreementLocator
    exact Finset.dvd_prod_of_mem
      (fun x : G ↦ (Polynomial.X : K[X]) - Polynomial.C (nodesG x))
      (Finset.mem_univ i)
  have hpow :
      ((Polynomial.X : K[X]) - Polynomial.C (nodesG i)) ^ q ∣
        (agreementLocator nodesG) ^ q :=
    pow_dvd_pow_of_dvd hfactor q
  have hwhole :
      ((Polynomial.X : K[X]) - Polynomial.C (nodesG i)) ^ q ∣
        (agreementLocator nodesG) ^ q * V :=
    hpow.trans (dvd_mul_right _ _)
  have heq := hasseAt_eq_of_node_pow_dvd_sub
    (nodesG i) q ((agreementLocator nodesG) ^ q * V) 0
      (by simpa using hwhole) j hj
  simpa [hasseAt] using heq

/-- Simultaneous error-value interpolation in one locator grade.  The
residual polynomial costs only `|E|` coefficients, while the locator grade
costs `q*|G|`.  This is the target-scalable primitive used one Hasse level at
a time. -/
theorem exists_locatorGrade_for_error_values
    (nodesG : G → K) (nodesE : E → K)
    (hnodesE : Function.Injective nodesE)
    (hcross : ∀ i j, nodesG i ≠ nodesE j)
    (q : Nat) (values : E → K) :
    ∃ V : K[X],
      V.degree < (Fintype.card E : Nat) ∧
      (∀ j : E,
        (((agreementLocator nodesG) ^ q * V).eval (nodesE j)) = values j) ∧
      (∀ i : G, ∀ j < q,
        hasseAt (nodesG i) ((agreementLocator nodesG) ^ q * V) j = 0) := by
  let depth : E → Nat := fun _ ↦ 1
  let scaled : JetSpace K E depth := fun j _ ↦
    values j / ((agreementLocator nodesG).eval (nodesE j)) ^ q
  let W : Polynomial.degreeLT K (totalDepth depth) :=
    (hasseJetEquiv nodesE depth hnodesE).symm scaled
  have hWjet : hasseJetMap nodesE depth W = scaled :=
    (hasseJetEquiv nodesE depth hnodesE).apply_symm_apply scaled
  refine ⟨W.1, ?_, ?_, ?_⟩
  · have hdegree := Polynomial.mem_degreeLT.mp W.2
    simpa [depth, totalDepth] using hdegree
  · intro j
    have hcoord := congrFun (congrFun hWjet j) (0 : Fin 1)
    have hWvalue : W.1.eval (nodesE j) =
        values j / ((agreementLocator nodesG).eval (nodesE j)) ^ q := by
      simpa [hasseJetMap_apply, hasseAt, depth, scaled,
        Polynomial.taylor_coeff] using hcoord
    rw [Polynomial.eval_mul, Polynomial.eval_pow, hWvalue]
    field_simp [agreementLocator_eval_error_ne_zero
      nodesG nodesE hcross j]
  · intro i j hj
    exact hasseAt_agreementLocator_pow_mul_eq_zero nodesG q W.1 i j hj

/-- Full error Hermite interpolation after multiplication by a locator
grade.  This theorem is useful as a guardrail: it is exact, but its
`m*|E|` residual-degree cost is often too expensive for a tapered source.
-/
theorem exists_locatorGrade_for_error_jets
    (nodesG : G → K) (nodesE : E → K)
    (hnodesE : Function.Injective nodesE)
    (hcross : ∀ i j, nodesG i ≠ nodesE j)
    (q m : Nat) (values : JetSpace K E (fun _ ↦ m)) :
    ∃ V : K[X],
      V.degree < (m * Fintype.card E : Nat) ∧
      (∀ i : E, ∀ j : Fin m,
        hasseAt (nodesE i) ((agreementLocator nodesG) ^ q * V) j.val =
          values i j) ∧
      (∀ i : G, ∀ j < q,
        hasseAt (nodesG i) ((agreementLocator nodesG) ^ q * V) j = 0) := by
  let depth : E → Nat := fun _ ↦ m
  let J : K[X] := jetDenominator nodesE depth
  let W : Polynomial.degreeLT K (totalDepth depth) :=
    (hasseJetEquiv nodesE depth hnodesE).symm values
  have hWjet : hasseJetMap nodesE depth W = values :=
    (hasseJetEquiv nodesE depth hnodesE).apply_symm_apply values
  have hcoprime : IsCoprime ((agreementLocator nodesG) ^ q) J := by
    exact (agreementLocator_isCoprime_errorJetDenominator
      nodesG nodesE hcross m).pow_left
  rcases hcoprime with ⟨u, v, huv⟩
  let V : K[X] := (u * W.1) %ₘ J
  have hJmonic : J.Monic := by
    exact jetDenominator_monic nodesE depth
  have hVdegree : V.degree < (m * Fintype.card E : Nat) := by
    have hdegree := Polynomial.degree_modByMonic_lt (u * W.1) hJmonic
    rw [Polynomial.degree_eq_natDegree hJmonic.ne_zero,
      jetDenominator_natDegree nodesE depth] at hdegree
    simpa [depth, totalDepth, Nat.mul_comm] using hdegree
  have hmod : J ∣ V - u * W.1 := by
    exact Polynomial.dvd_modByMonic_sub (u * W.1) J
  have hbezout :
      (agreementLocator nodesG) ^ q * u * W.1 - W.1 =
        J * (-(v * W.1)) := by
    have hcoefficient :
        (agreementLocator nodesG) ^ q * u - 1 = -(v * J) := by
      calc
        (agreementLocator nodesG) ^ q * u - 1 =
            u * (agreementLocator nodesG) ^ q - 1 := by ring
        _ = u * (agreementLocator nodesG) ^ q -
              (u * (agreementLocator nodesG) ^ q + v * J) := by rw [huv]
        _ = -(v * J) := by ring
    calc
      (agreementLocator nodesG) ^ q * u * W.1 - W.1 =
          (((agreementLocator nodesG) ^ q * u) - 1) * W.1 := by ring
      _ = (-(v * J)) * W.1 := by rw [hcoefficient]
      _ = J * (-(v * W.1)) := by ring
  have hdifference :
      J ∣ (agreementLocator nodesG) ^ q * V - W.1 := by
    rcases hmod with ⟨t, ht⟩
    refine ⟨(agreementLocator nodesG) ^ q * t - v * W.1, ?_⟩
    calc
      (agreementLocator nodesG) ^ q * V - W.1 =
          (agreementLocator nodesG) ^ q * (V - u * W.1) +
            ((agreementLocator nodesG) ^ q * u * W.1 - W.1) := by ring
      _ = (agreementLocator nodesG) ^ q * (J * t) +
            J * (-(v * W.1)) := by rw [ht, hbezout]
      _ = J * ((agreementLocator nodesG) ^ q * t - v * W.1) := by ring
  refine ⟨V, hVdegree, ?_, ?_⟩
  · intro i j
    have hfactor :
        ((Polynomial.X : K[X]) - Polynomial.C (nodesE i)) ^ m ∣ J := by
      unfold J depth jetDenominator
      exact Finset.dvd_prod_of_mem
        (fun x : E ↦
          ((Polynomial.X : K[X]) - Polynomial.C (nodesE x)) ^ m)
        (Finset.mem_univ i)
    have heq := hasseAt_eq_of_node_pow_dvd_sub
      (nodesE i) m ((agreementLocator nodesG) ^ q * V) W.1
        (hfactor.trans hdifference) j.val j.isLt
    rw [heq]
    have hcoord := congrFun (congrFun hWjet i) j
    simpa [hasseJetMap_apply, depth] using hcoord
  · intro i j hj
    exact hasseAt_agreementLocator_pow_mul_eq_zero nodesG q V i j hj

/-! ## Exact lower-6900 taper arithmetic -/

theorem target_error_lt_agreement : 81731 < 180413 := by norm_num

theorem target_error_residual_lt_w : 81731 < 131071 := by norm_num

/-- Every locator grade through `q=46` plus an error-value interpolant fits
under the untapered cutoff `47*g`. -/
theorem target_valueCRT_fits_full_cutoff (q : Nat) (hq : q ≤ 46) :
    q * 180413 + 81731 < 47 * 180413 := by omega

/-- The four finite-Schur witness heights scale to the `SR*Y^43` target
window with locator grade 13 and value interpolation still legal. -/
theorem target_valueCRT_q13_fits_SR_Y43 :
    13 * 180413 + 81731 <
      47 * 180413 - 43 * 131071 - 131070 - 131069 := by norm_num

/-- The same grade remains legal for `SR*Y^44`. -/
theorem target_valueCRT_q13_fits_SR_Y44 :
    13 * 180413 + 81731 <
      47 * 180413 - 44 * 131071 - 131070 - 131069 := by norm_num

/-- Locator grade 14 is the first grade which does not fit at `SR*Y^43`.
Together with the preceding lemmas this gives the exact grade cap 13 on both
finite-witness-height analogues. -/
theorem target_valueCRT_q14_does_not_fit_SR_Y43 :
    47 * 180413 - 43 * 131071 - 131070 - 131069 <
      14 * 180413 + 81731 := by norm_num

/-- The last `Y` layer of the base family has just enough room for error
values at locator grade zero. -/
theorem target_valueCRT_q0_fits_one_Y64 :
    81731 < 47 * 180413 - 64 * 131071 := by norm_num

/-- It has no room for locator grade one. -/
theorem target_valueCRT_q1_does_not_fit_one_Y64 :
    47 * 180413 - 64 * 131071 < 180413 + 81731 := by norm_num

/-- The last `R` layer behaves identically up to one unit: grade zero fits. -/
theorem target_valueCRT_q0_fits_R_Y63 :
    81731 < 47 * 180413 - 63 * 131071 - 131070 := by norm_num

/-- The last `R` layer also cannot carry locator grade one. -/
theorem target_valueCRT_q1_does_not_fit_R_Y63 :
    47 * 180413 - 63 * 131071 - 131070 < 180413 + 81731 := by norm_num

/-- On the last subcritical `S*Y^46` layer the exact locator-grade cap for
error-value interpolation is 12. -/
theorem target_valueCRT_q12_fits_S_Y46 :
    12 * 180413 + 81731 <
      47 * 180413 - 46 * 131071 - 131069 := by norm_num

theorem target_valueCRT_q13_does_not_fit_S_Y46 :
    47 * 180413 - 46 * 131071 - 131069 <
      13 * 180413 + 81731 := by norm_num

/-- Even with no agreement locator, one-shot interpolation of all 47 error
jets cannot fit in the `SR*Y^43` source window.  The target proof therefore
must use the triangular locator-grade recurrence. -/
theorem target_fullErrorJetCRT_does_not_fit_SR_Y43 :
    47 * 180413 - 43 * 131071 - 131070 - 131069 < 47 * 81731 := by
  norm_num

#print axioms agreementLocator_monic
#print axioms agreementLocator_natDegree
#print axioms agreementLocator_eval_error_ne_zero
#print axioms agreementLocator_isCoprime_errorJetDenominator
#print axioms hasseAt_agreementLocator_pow_mul_eq_zero
#print axioms exists_locatorGrade_for_error_values
#print axioms exists_locatorGrade_for_error_jets
#print axioms target_valueCRT_fits_full_cutoff
#print axioms target_valueCRT_q13_fits_SR_Y43
#print axioms target_valueCRT_q0_fits_one_Y64
#print axioms target_valueCRT_q12_fits_S_Y46
#print axioms target_fullErrorJetCRT_does_not_fit_SR_Y43

end

end ProximityPrize.SubmissionLower.K0LocatorErrorCRT6900
