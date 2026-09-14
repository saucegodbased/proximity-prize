import OriginalPassiveSeedSource6900
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Polynomial row shears do not preserve the literal m69 source interface

The passive source is built for the affine received-word pencil
`u0 + gamma*u1`.  A node-dependent row operation whose new second row is
`d(X)u0-c(X)u1` is not a relabelling of that pencil by field scalars.  If it
is implemented as a polynomial coordinate change instead, its positive
X-degree consumes the weighted-X budget.  This file records both obstructions
and an exact boundary monomial in the literal source box.
-/

namespace ProximityPrize.SubmissionLower.M69PolynomialRowShearSourceBoxCountergate6900

open Polynomial
open Order2SourceRank

noncomputable section
set_option autoImplicit false
set_option Elab.async false

/-- The simplest X-dependent coordinate scaling: `Y` is replaced by
`X*Y`, while `X,R,S` are fixed. -/
def degreeOneErrorScaling
    (K : Type*) [Field K] : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval fun i =>
    if i = (1 : Fin 4) then contactZ K * errorE K else MvPolynomial.X i

/-- On a source monomial linear in `Y`, the scaling consumes exactly one
unit of X-degree. -/
theorem degreeOneErrorScaling_sourceMonomial
    (K : Type*) [Field K] (a : Nat) :
    degreeOneErrorScaling K (globalSourceMonomial K a 1 0 0) =
      globalSourceMonomial K (a + 1) 1 0 0 := by
  simp [degreeOneErrorScaling, globalSourceMonomial, contactZ, errorE,
    slopeR, curvatureS, pow_succ]
  ring

/-- At two distinct seed values, keeping the same affine graph forces a
replacement direction and intercept to be the original ones.  In particular,
an X-dependent wedge cannot silently replace `u1` while retaining two
selected graphs. -/
theorem two_seed_affine_pencil_rigidity
    {K : Type*} [Field K]
    (u0 u1 v0 v1 gamma delta : K)
    (hgd : gamma ≠ delta)
    (hgamma : u0 + gamma * u1 = v0 + gamma * v1)
    (hdelta : u0 + delta * u1 = v0 + delta * v1) :
    v0 = u0 ∧ v1 = u1 := by
  have hslope : (gamma - delta) * (u1 - v1) = 0 := by
    linear_combination hgamma - hdelta
  have hgd0 : gamma - delta ≠ 0 := sub_ne_zero.mpr hgd
  have hv1 : v1 = u1 := by
    have : u1 - v1 = 0 := (mul_eq_zero.mp hslope).resolve_left hgd0
    exact (sub_eq_zero.mp this).symm
  constructor
  · rw [hv1] at hgamma
    exact (add_right_cancel hgamma).symm
  · exact hv1

/-- Multiplying a degree-`w` candidate by an X-dependent coefficient of
degree `s` has the sharp possible cost `w+s`. -/
theorem polynomial_row_coefficient_cost_is_sharp (s w : Nat) :
    ((Polynomial.X ^ s : ℚ[X]) * Polynomial.X ^ w).natDegree = s + w := by
  rw [← pow_add, natDegree_X_pow]

/-- A polynomial wedge formed from two degree-`w` row representatives has
the honest degree cost `w+s`, where `s` bounds both moving row
coefficients. -/
theorem polynomial_wedge_degree_le
    {K : Type*} [Field K] (c d p0 p1 : K[X]) (s w : Nat)
    (hc : c.natDegree ≤ s) (hd : d.natDegree ≤ s)
    (hp0 : p0.natDegree ≤ w) (hp1 : p1.natDegree ≤ w) :
    (d * p0 - c * p1).natDegree ≤ s + w := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (Nat.add_le_add hd hp0)
  · exact natDegree_mul_le.trans (Nat.add_le_add hc hp1)

/-- Already a degree-one row coefficient takes an extremal degree-131071
candidate outside the degree-131071 list-decoding class. -/
theorem m69_degree_one_row_coefficient_leaves_candidate_cap :
    ((Polynomial.X : ℚ[X]) * Polynomial.X ^ 131071).natDegree = 131072 ∧
      ¬ ((Polynomial.X : ℚ[X]) * Polynomial.X ^ 131071).natDegree ≤ 131071 := by
  have hdegree :
      ((Polynomial.X : ℚ[X]) * Polynomial.X ^ 131071).natDegree = 131072 := by
    simpa using polynomial_row_coefficient_cost_is_sharp 1 131071
  constructor
  · exact hdegree
  · rw [hdegree]
    norm_num

/-- The literal m69 weighted box contains the boundary monomial
`X^(D-w-1)Y`, but the degree-one scaling `Y -> X*Y` sends it to
`X^(D-w)Y`, whose weighted degree is exactly `D` and is excluded by the
strict source cutoff.  Thus an X-dependent row scaling is not an automorphism
of the source box. -/
theorem m69_degree_one_error_scaling_leaves_source_box :
    let D : Nat := 69 * 180413
    let w : Nat := 131071
    let a : Nat := D - w - 1
    globalSourceMonomial ℚ a 1 0 0 ∈
        globalOrder2CoefficientBox ℚ D w 69 69 69 ∧
      globalSourceMonomial ℚ (a + 1) 1 0 0 ∉
        globalOrder2CoefficientBox ℚ D w 69 69 69 := by
  dsimp only
  constructor
  · rw [globalSourceMonomial_eq_monomial]
    apply (MvPolynomial.monomial_mem_restrictSupport (R := ℚ)).mpr
    left
    simp [globalOrder2Exponents]
  · rw [globalSourceMonomial_eq_monomial]
    unfold globalOrder2CoefficientBox
    rw [MvPolynomial.monomial_mem_restrictSupport]
    simp [globalOrder2Exponents]

/-- Exact arithmetic behind the preceding source-box boundary. -/
theorem m69_degree_one_error_scaling_weight_receipt :
    (69 * 180413 - 131071 - 1) + 131071 = 69 * 180413 - 1 ∧
      (69 * 180413 - 131071 - 1 + 1) + 131071 = 69 * 180413 := by
  norm_num

/-- A variable polynomial shear can be unimodular: the matrix
`[[1,0],[X,-1]]` has determinant `-1`.  Unimodularity therefore does not
repair either the affine-pencil or weighted-box obstruction. -/
theorem degree_one_wedge_row_matrix_is_unimodular :
    (1 : ℚ[X]) * (-1) - 0 * Polynomial.X = -1 := by
  ring

/-- Two 180413-node agreement sets are guaranteed only 98682 common nodes;
the literal m69 multiplicity requirement was budgeted for all 180413. -/
theorem two_candidate_intersection_cannot_retain_m69_degree_budget :
    180413 + 180413 - 262144 = 98682 ∧
      69 * 98682 < 69 * 180413 := by
  norm_num

#print axioms two_seed_affine_pencil_rigidity
#print axioms degreeOneErrorScaling_sourceMonomial
#print axioms polynomial_row_coefficient_cost_is_sharp
#print axioms polynomial_wedge_degree_le
#print axioms m69_degree_one_row_coefficient_leaves_candidate_cap
#print axioms m69_degree_one_error_scaling_leaves_source_box
#print axioms m69_degree_one_error_scaling_weight_receipt
#print axioms degree_one_wedge_row_matrix_is_unimodular
#print axioms two_candidate_intersection_cannot_retain_m69_degree_budget

end
end ProximityPrize.SubmissionLower.M69PolynomialRowShearSourceBoxCountergate6900
