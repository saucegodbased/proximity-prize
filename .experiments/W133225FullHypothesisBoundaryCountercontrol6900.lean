import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full downstream-hypothesis boundary for the W=133225 two-fibre control

This is a small exact algebraic control, scaled from the target constants to
seven nodes.  It simultaneously carries:

* two selected polynomials and their agreement supports;
* badness of the second received row against degree-zero polynomials;
* a canonical-interpolant projective-high statement for **every** nonzero
  received-row direction;
* monic agreement-locator factorizations with nonzero short residuals;
* the fixed-scalar residual equations and two different scalar top values;
* the literal cross equation and all four literal source equations for
  `E=X^2+1, L=1, M=-1, c=1, d=0, N=-1`;
* scaled content/grade inequalities.

Thus the downstream identities named above do not force one top fibre.  The
control deliberately does not claim the target `DataNine`, primitive-conic,
or `Realizes` provenance, nor target-scale agreement/cardinality.  Those are
the first remaining hypothesis class from which a genuine target off-fibre
mass theorem would have to extract new information.
-/

namespace ProximityPrize.SubmissionLower.W133225FullHypothesisBoundaryCountercontrol6900

open Polynomial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev K7 := ZMod 7
abbrev I7 := Fin 7

def nodeValue7 : I7 → K7 := ![0, 1, 2, 3, 4, 5, 6]

theorem nodeValue7_injective : Function.Injective nodeValue7 := by
  have heq : nodeValue7 = (ZMod.finEquiv 7 : Fin 7 → ZMod 7) := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact (ZMod.finEquiv 7).injective

def node7 : I7 ↪ K7 := ⟨nodeValue7, nodeValue7_injective⟩

def E7 : K7[X] := (X : K7[X]) ^ 2 + C 1
def P0 : K7[X] := 0
def P5 : K7[X] := 1
def B0 : K7[X] := 0
def B5 : K7[X] := E7 + C 5

def S0 : Finset I7 := {0, 1, 2, 6}
def S5 : Finset I7 := {1, 3, 4, 6}

def explicitU0 : K7[X] :=
  C 2 * X ^ 2 + X ^ 4 + C 4 * X ^ 6

def explicitU1 : K7[X] :=
  C 6 + C 4 * X ^ 2 + C 3 * X ^ 4 + C 4 * X ^ 6

def centre7 : I7 → K7 := ![0, 0, 0, 1, 1, 0, 0]
def u0 : I7 → K7 := ![0, 0, 0, 5, 5, 0, 0]
def u1 : I7 → K7 := ![6, 3, 4, 2, 2, 4, 3]

def interpolant7 (v : I7 → K7) : K7[X] :=
  Lagrange.interpolate Finset.univ node7 v

theorem interpolant7_eval (v : I7 → K7) (i : I7) :
    (interpolant7 v).eval (node7 i) = v i := by
  exact Lagrange.eval_interpolate_at_node v node7.injective.injOn
    (Finset.mem_univ i)

theorem interpolant7_degree_le_six (v : I7 → K7) :
    (interpolant7 v).natDegree ≤ 6 := by
  have hdeg := Lagrange.degree_interpolate_lt (s := Finset.univ)
    v node7.injective.injOn
  have hcard : Fintype.card I7 = 7 := by norm_num [I7]
  rw [Finset.card_univ, hcard] at hdeg
  by_cases hzero : interpolant7 v = 0
  · simp [hzero]
  · have hlt : (interpolant7 v).natDegree < 7 :=
      (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdeg
    omega

def explicitDirection (a b : K7) : K7[X] :=
  C a * explicitU0 + C b * explicitU1

theorem explicitU0_eval (i : I7) :
    explicitU0.eval (node7 i) = u0 i := by
  fin_cases i <;>
    norm_num [explicitU0, node7, nodeValue7, u0] <;> decide

theorem explicitU1_eval (i : I7) :
    explicitU1.eval (node7 i) = u1 i := by
  fin_cases i <;>
    norm_num [explicitU1, node7, nodeValue7, u1] <;> decide

theorem explicitDirection_eval (a b : K7) (i : I7) :
    (explicitDirection a b).eval (node7 i) = a * u0 i + b * u1 i := by
  simp [explicitDirection, explicitU0_eval, explicitU1_eval]

theorem explicitDirection_natDegree_le_six (a b : K7) :
    (explicitDirection a b).natDegree ≤ 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hm2 : m ≠ 2 := by omega
  have hm4 : m ≠ 4 := by omega
  have hm6 : m ≠ 6 := by omega
  simp [explicitDirection, explicitU0, explicitU1, coeff_add, coeff_C_mul,
    coeff_X_pow, coeff_C, hm0, hm2, hm4, hm6]

theorem interpolant7_direction_eq_explicit (a b : K7) :
    interpolant7 (fun i ↦ a * u0 i + b * u1 i) = explicitDirection a b := by
  symm
  change explicitDirection a b =
    Lagrange.interpolate Finset.univ node7 (fun i ↦ a * u0 i + b * u1 i)
  apply Lagrange.eq_interpolate_of_eval_eq
      (fun i ↦ a * u0 i + b * u1 i) node7.injective.injOn
  · rw [Finset.card_univ]
    exact Polynomial.degree_le_natDegree.trans_lt (by
      exact_mod_cast (explicitDirection_natDegree_le_six a b).trans_lt
        (by norm_num))
  · intro i _hi
    exact explicitDirection_eval a b i

theorem explicitDirection_coeff_six (a b : K7) :
    (explicitDirection a b).coeff 6 = 4 * a + 4 * b := by
  simp [explicitDirection, explicitU0, explicitU1]
  ring

theorem explicitDirection_coeff_four (a b : K7) :
    (explicitDirection a b).coeff 4 = a + 3 * b := by
  simp [explicitDirection, explicitU0, explicitU1]
  ring

theorem explicitDirection_natDegree_ge_four (a b : K7)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    4 ≤ (explicitDirection a b).natDegree := by
  by_cases h6 : 4 * a + 4 * b = 0
  · have habzero : a + b = 0 := by
      have hmul : (4 : K7) * (a + b) = 0 := by
        linear_combination h6
      exact (mul_eq_zero.mp hmul).resolve_left (by decide)
    have hb : b = -a := by
      linear_combination habzero
    have ha : a ≠ 0 := by
      intro ha
      rcases hab with ha' | hb'
      · exact ha' ha
      · apply hb'
        rw [hb, ha, neg_zero]
    apply Polynomial.le_natDegree_of_ne_zero
    rw [explicitDirection_coeff_four, hb]
    intro hz
    apply ha
    have hzmul : (-2 : K7) * a = 0 := by
      linear_combination hz
    exact (mul_eq_zero.mp hzmul).resolve_left (by decide)
  · apply (show 4 ≤ 6 by norm_num).trans
    apply Polynomial.le_natDegree_of_ne_zero
    rw [explicitDirection_coeff_six]
    exact h6

/-- Every projective received-row direction is high at the scaled cutoff. -/
theorem scaled_canonical_projectiveHigh :
    ∀ a b : K7, (a ≠ 0 ∨ b ≠ 0) →
      4 ≤ (interpolant7 (fun i ↦ a * u0 i + b * u1 i)).natDegree := by
  intro a b hab
  rw [interpolant7_direction_eq_explicit]
  exact explicitDirection_natDegree_ge_four a b hab

theorem residual_at_zero : E7 * P0 = C 0 * C (-1) + B0 := by
  simp [P0, B0]

theorem residual_at_five : E7 * P5 = C 5 * C (-1) + B5 := by
  simp [P5, B5]

theorem scalar_zero_agrees :
    ∀ i ∈ S0, B0.eval (node7 i) = centre7 i := by
  intro i hi
  fin_cases i <;> simp_all [S0, B0, centre7]

theorem scalar_five_agrees :
    ∀ i ∈ S5, B5.eval (node7 i) = centre7 i := by
  intro i hi
  fin_cases i <;>
    simp_all [S5, B5, E7, centre7, node7, nodeValue7] <;>
    decide

theorem selected_zero_agrees :
    ∀ i ∈ S0, P0.eval (node7 i) = u0 i + 0 * u1 i := by
  intro i hi
  fin_cases i <;> simp_all [S0, P0, u0, u1]

theorem selected_five_agrees :
    ∀ i ∈ S5, P5.eval (node7 i) = u0 i + 5 * u1 i := by
  intro i hi
  fin_cases i <;> simp_all [S5, P5, u0, u1] <;> decide

theorem both_identity_rows_zero_everywhere (i : I7) :
    E7.eval (node7 i) * u0 i - centre7 i = 0 ∧
      E7.eval (node7 i) * u1 i - (-1) = 0 := by
  fin_cases i <;>
    norm_num [u0, u1, centre7, E7, node7, nodeValue7] <;> decide

theorem top_coefficients_differ : B0.coeff 2 ≠ B5.coeff 2 := by
  simpa only [B0, B5, E7, coeff_zero, coeff_add, coeff_X_pow,
    coeff_one, coeff_C, if_pos, if_neg (by norm_num : (2 : Nat) ≠ 0),
    zero_add, add_zero] using
    (zero_ne_one : (0 : K7) ≠ 1)

/-- Direct polynomial form of scaled selected badness.  This avoids hiding
the relevant content behind a coding-theory wrapper: no degree-zero
polynomial restricts to the second received row on either agreement set. -/
def DegreeZeroBadOn (S : Finset I7) : Prop :=
  ¬ ∃ P : K7[X], P.natDegree ≤ 0 ∧
    ∀ i ∈ S, P.eval (node7 i) = u1 i

theorem second_row_bad_on_S0 : DegreeZeroBadOn S0 := by
  rintro ⟨P, hP, hval⟩
  have hconst : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero hP
  have h0 := hval 0 (by norm_num [S0])
  have h1 := hval 1 (by norm_num [S0])
  rw [hconst] at h0 h1
  simp only [eval_C] at h0 h1
  have heq : u1 0 = u1 1 := h0.symm.trans h1
  have hne : u1 0 ≠ u1 1 := by
    simp [u1]
    change (6 : Fin 7) ≠ 3
    decide
  exact hne heq

theorem second_row_bad_on_S5 : DegreeZeroBadOn S5 := by
  rintro ⟨P, hP, hval⟩
  have hconst : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero hP
  have h1 := hval 1 (by norm_num [S5])
  have h3 := hval 3 (by norm_num [S5])
  rw [hconst] at h1 h3
  simp only [eval_C] at h1 h3
  have heq : u1 1 = u1 3 := h1.symm.trans h3
  have hne : u1 1 ≠ u1 3 := by
    simp [u1]
    change (3 : Fin 7) ≠ 2
    decide
  exact hne heq

def locator7 (S : Finset I7) : K7[X] :=
  ∏ i ∈ S, (X - C (node7 i))

theorem locator7_monic (S : Finset I7) : (locator7 S).Monic := by
  simpa [locator7] using
    (Polynomial.monic_prod_X_sub_C (b := fun i ↦ node7 i) (s := S))

theorem locator7_natDegree (S : Finset I7) :
    (locator7 S).natDegree = S.card := by
  have h := Polynomial.natDegree_prod_of_monic S
    (fun i : I7 ↦ (X - C (node7 i) : K7[X]))
    (by
      intro i hi
      simpa using Polynomial.monic_X_sub_C (node7 i))
  simpa [locator7] using h

theorem locator7_dvd_of_eval_zero (S : Finset I7) (F : K7[X])
    (hzero : ∀ i ∈ S, F.eval (node7 i) = 0) :
    locator7 S ∣ F := by
  rw [locator7]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C node7.injective hij
  · intro i hi
    exact Polynomial.dvd_iff_isRoot.mpr (hzero i hi)

def Q7 (gamma : K7) : K7[X] :=
  interpolant7 (fun i ↦ u0 i + gamma * u1 i)

def D7 (gamma : K7) (P : K7[X]) : K7[X] := Q7 gamma - P

theorem Q7_eval (gamma : K7) (i : I7) :
    (Q7 gamma).eval (node7 i) = u0 i + gamma * u1 i := by
  exact interpolant7_eval _ i

theorem Q7_degree_le_six (gamma : K7) : (Q7 gamma).natDegree ≤ 6 :=
  interpolant7_degree_le_six _

theorem short_nonzero_locator_residual
    (gamma : K7) (P : K7[X]) (S : Finset I7)
    (hcard : S.card = 4) (hP : P.natDegree ≤ 0)
    (hagrees : ∀ i ∈ S, P.eval (node7 i) = u0 i + gamma * u1 i)
    (hwitness : ∃ i : I7, P.eval (node7 i) ≠ u0 i + gamma * u1 i) :
    ∃ R : K7[X], R ≠ 0 ∧ D7 gamma P = locator7 S * R ∧
      R.natDegree ≤ 2 := by
  have hDne : D7 gamma P ≠ 0 := by
    intro hzero
    obtain ⟨i, hi⟩ := hwitness
    apply hi
    have he := congrArg (fun T : K7[X] ↦ T.eval (node7 i)) hzero
    simp only [D7, eval_sub, Q7_eval, eval_zero, sub_eq_zero] at he
    exact he.symm
  have hdiv : locator7 S ∣ D7 gamma P := by
    apply locator7_dvd_of_eval_zero
    intro i hi
    simp only [D7, eval_sub, Q7_eval]
    exact sub_eq_zero.mpr (hagrees i hi).symm
  obtain ⟨R, hfactor⟩ := hdiv
  have hHne : locator7 S ≠ 0 := (locator7_monic S).ne_zero
  have hRne : R ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hDne hfactor
  have hDdegree : (D7 gamma P).natDegree ≤ 6 := by
    unfold D7
    exact (natDegree_sub_le _ _).trans
      (max_le (Q7_degree_le_six gamma) (hP.trans (by omega)))
  have hsum : (locator7 S).natDegree + R.natDegree ≤ 6 := by
    rw [← natDegree_mul hHne hRne, ← hfactor]
    exact hDdegree
  refine ⟨R, hRne, hfactor, ?_⟩
  rw [locator7_natDegree, hcard] at hsum
  omega

theorem residual_factor_zero :
    ∃ R : K7[X], R ≠ 0 ∧ D7 0 P0 = locator7 S0 * R ∧
      R.natDegree ≤ 2 := by
  apply short_nonzero_locator_residual 0 P0 S0 (by decide)
  · simp [P0]
  · exact selected_zero_agrees
  · refine ⟨3, ?_⟩
    norm_num [P0, u0, u1, node7, nodeValue7] <;> decide

theorem residual_factor_five :
    ∃ R : K7[X], R ≠ 0 ∧ D7 5 P5 = locator7 S5 * R ∧
      R.natDegree ≤ 2 := by
  apply short_nonzero_locator_residual 5 P5 S5 (by decide)
  · simp [P5]
  · exact selected_five_agrees
  · refine ⟨0, ?_⟩
    norm_num [P5, u0, u1, node7, nodeValue7] <;> decide

/-- Literal scaled aligned-cross tuple.  The four source equations use the
identity as coefficient Frobenius, exactly as appropriate over `ZMod 7`. -/
theorem literal_cross_and_four_sources :
    (∀ i : I7,
      E7.eval (node7 i) * (0 * u0 i - 1 * u1 i) = (1 : K7)) ∧
    (∀ i : I7,
      (E7 * 1 * 1).eval (node7 i) * u0 i +
        (E7 * (-1) * 1).eval (node7 i) * u0 i + 0 = 0) ∧
    (∀ i : I7,
      (E7 * 1 * 1).eval (node7 i) * u1 i +
        (E7 * (-1) * 0).eval (node7 i) * u0 i + 1 = 0) ∧
    (∀ i : I7,
      (E7 * 1 * 0).eval (node7 i) * u0 i +
        (E7 * (-1) * 1).eval (node7 i) * u1 i - 1 = 0) ∧
    (∀ i : I7,
      (E7 * 1 * 0).eval (node7 i) * u1 i +
        (E7 * (-1) * 0).eval (node7 i) * u1 i + 0 = 0) := by
  constructor
  · intro i
    have h := (both_identity_rows_zero_everywhere i).2
    simp only [zero_mul, one_mul, zero_sub]
    linear_combination -h
  constructor
  · intro i
    simp only [eval_mul, eval_one, eval_neg]
    ring
  constructor
  · intro i
    have h := (both_identity_rows_zero_everywhere i).2
    simp only [eval_mul, eval_one, eval_zero, mul_one, mul_zero, zero_mul,
      add_zero]
    simpa only [sub_neg_eq_add] using h
  constructor
  · intro i
    have h := (both_identity_rows_zero_everywhere i).2
    simp only [eval_mul, eval_one, eval_zero, eval_neg, mul_one, mul_zero,
      zero_mul, add_zero]
    linear_combination -h
  · intro i
    simp only [eval_mul, eval_one, eval_zero, mul_one, mul_zero, zero_mul,
      add_zero]

theorem scaled_grade_and_content_bounds :
    E7.natDegree = 2 ∧
      E7.natDegree +
          max (1 : K7[X]).natDegree (0 : K7[X]).natDegree +
          max (1 : K7[X]).natDegree (-1 : K7[X]).natDegree = 2 ∧
      E7.natDegree < 16000 ∧ E7.natDegree ≤ 24932 := by
  have hE : E7.natDegree = 2 := by
    rw [E7, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  rw [hE]
  norm_num

/-- The checked STOP certificate: every downstream hypothesis class named in
the audit coexists with two scalar top fibres. -/
theorem downstream_full_payload_still_has_two_top_fibres :
    (∀ a b : K7, (a ≠ 0 ∨ b ≠ 0) →
      4 ≤ (interpolant7 (fun i ↦ a * u0 i + b * u1 i)).natDegree) ∧
    DegreeZeroBadOn S0 ∧ DegreeZeroBadOn S5 ∧
    (∃ R : K7[X], R ≠ 0 ∧ D7 0 P0 = locator7 S0 * R ∧
      R.natDegree ≤ 2) ∧
    (∃ R : K7[X], R ≠ 0 ∧ D7 5 P5 = locator7 S5 * R ∧
      R.natDegree ≤ 2) ∧
    (∀ i : I7,
      E7.eval (node7 i) * (0 * u0 i - 1 * u1 i) = (1 : K7)) ∧
    E7 * P0 = C 0 * C (-1) + B0 ∧
    E7 * P5 = C 5 * C (-1) + B5 ∧
    B0.coeff 2 ≠ B5.coeff 2 := by
  exact ⟨scaled_canonical_projectiveHigh, second_row_bad_on_S0,
    second_row_bad_on_S5, residual_factor_zero, residual_factor_five,
    literal_cross_and_four_sources.1, residual_at_zero, residual_at_five,
    top_coefficients_differ⟩

#print axioms interpolant7_direction_eq_explicit
#print axioms scaled_canonical_projectiveHigh
#print axioms second_row_bad_on_S0
#print axioms second_row_bad_on_S5
#print axioms residual_factor_zero
#print axioms residual_factor_five
#print axioms literal_cross_and_four_sources
#print axioms scaled_grade_and_content_bounds
#print axioms downstream_full_payload_still_has_two_top_fibres

end
end ProximityPrize.SubmissionLower.W133225FullHypothesisBoundaryCountercontrol6900
