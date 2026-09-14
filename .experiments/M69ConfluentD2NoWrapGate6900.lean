import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# A no-wrap confluent-Pascal gate for the first two-row m69 chain

After constant row and column rescaling, the literal chain
`(r,s,q)=(0,0,26)`, `Y={41,42}` is the value/first-Hasse-derivative map

`P ↦ (P(W), P'(W))`.

Consequently its source-facing dual sequence satisfies

`E^2 H_(t+2) - 2*N*E H_(t+1) + N^2 H_t = 0`

whenever the nodal equality is below the cyclic modulus.  Two overlapping
relations force the intervening short polynomial to be divisible by both
coprime factors.  This file isolates that algebraic fact and the exact
numeric no-wrap range for the physical caps.  It deliberately makes no
claim in the remaining wrap band.
-/

namespace ProximityPrize.SubmissionLower.M69ConfluentD2NoWrapGate6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

/-- One polynomial (rather than merely nodal) second-order confluent
relation. -/
def ConfluentRelation {K : Type*} [Field K]
    (E N H0 H1 H2 : K[X]) : Prop :=
  N ^ 2 * H0 - 2 * (N * E) * H1 + E ^ 2 * H2 = 0

/-- The right endpoint of one confluent relation is divisible by `N`. -/
theorem right_dvd_of_confluentRelation
    {K : Type*} [Field K]
    (E N H0 H1 H2 : K[X]) (hcop : IsCoprime E N)
    (hrel : ConfluentRelation E N H0 H1 H2) :
    N ∣ H2 := by
  have hraw : N ∣ E ^ 2 * H2 := by
    refine ⟨2 * E * H1 - N * H0, ?_⟩
    dsimp only [ConfluentRelation] at hrel
    linear_combination hrel
  exact (hcop.symm.pow_right).dvd_of_dvd_mul_left hraw

/-- The left endpoint of one confluent relation is divisible by `E`. -/
theorem left_dvd_of_confluentRelation
    {K : Type*} [Field K]
    (E N H0 H1 H2 : K[X]) (hcop : IsCoprime E N)
    (hrel : ConfluentRelation E N H0 H1 H2) :
    E ∣ H0 := by
  have hraw : E ∣ N ^ 2 * H0 := by
    refine ⟨2 * N * H1 - E * H2, ?_⟩
    dsimp only [ConfluentRelation] at hrel
    linear_combination hrel
  exact hcop.pow_right.dvd_of_dvd_mul_left hraw

/-- Overlapping confluent relations force the common short endpoint to
contain the full coprime product. -/
theorem mul_dvd_middle_of_overlapping_confluentRelations
    {K : Type*} [Field K]
    (E N H0 H1 H2 H3 H4 : K[X]) (hcop : IsCoprime E N)
    (hleft : ConfluentRelation E N H0 H1 H2)
    (hright : ConfluentRelation E N H2 H3 H4) :
    E * N ∣ H2 := by
  exact hcop.mul_dvd
    (left_dvd_of_confluentRelation E N H2 H3 H4 hcop hright)
    (right_dvd_of_confluentRelation E N H0 H1 H2 hcop hleft)

/-- If the common polynomial is shorter than `E*N`, it is zero. -/
theorem middle_eq_zero_of_overlapping_confluentRelations
    {K : Type*} [Field K]
    (E N H0 H1 H2 H3 H4 : K[X])
    (hE : E ≠ 0) (hN : N ≠ 0) (hcop : IsCoprime E N)
    (hleft : ConfluentRelation E N H0 H1 H2)
    (hright : ConfluentRelation E N H2 H3 H4)
    (hshort : H2.natDegree < E.natDegree + N.natDegree) :
    H2 = 0 := by
  by_contra hH
  have hdiv := mul_dvd_middle_of_overlapping_confluentRelations
    E N H0 H1 H2 H3 H4 hcop hleft hright
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv hH
  rw [natDegree_mul hE hN] at hdegree
  omega

/-- Three overlapping relations kill two interior high-prefix duals and the
low-prefix dual between them. -/
theorem three_confluentRelations_kill_middle_triple
    {K : Type*} [Field K]
    (E N H0 H1 H2 H3 H4 H5 H6 : K[X])
    (hE : E ≠ 0) (hN : N ≠ 0) (htwo : (2 : K[X]) ≠ 0)
    (hcop : IsCoprime E N)
    (h012 : ConfluentRelation E N H0 H1 H2)
    (h234 : ConfluentRelation E N H2 H3 H4)
    (h456 : ConfluentRelation E N H4 H5 H6)
    (hH2 : H2.natDegree < E.natDegree + N.natDegree)
    (hH4 : H4.natDegree < E.natDegree + N.natDegree) :
    H2 = 0 ∧ H3 = 0 ∧ H4 = 0 := by
  have hz2 := middle_eq_zero_of_overlapping_confluentRelations
    E N H0 H1 H2 H3 H4 hE hN hcop h012 h234 hH2
  have hz4 := middle_eq_zero_of_overlapping_confluentRelations
    E N H2 H3 H4 H5 H6 hE hN hcop h234 h456 hH4
  refine ⟨hz2, ?_, hz4⟩
  rw [hz2, hz4] at h234
  dsimp only [ConfluentRelation] at h234
  have h234' : (2 : K[X]) * (N * E) * H3 = 0 := by
    simpa only [mul_zero, sub_zero, zero_sub, add_zero, neg_eq_zero, pow_two]
      using h234
  have hprod : (2 : K[X]) * (N * E) ≠ 0 :=
    mul_ne_zero htwo (mul_ne_zero hN hE)
  exact (mul_eq_zero.mp h234').resolve_left hprod

/-- The same kill applied to the step-two/all-high subsequence.  Its
confluent factors are `E^2,N^2`, so the short middle polynomial only has to
lie below degree `2 * (deg E + deg N)`. -/
theorem three_stepTwoRelations_kill_middle_triple
    {K : Type*} [Field K]
    (E N H0 H1 H2 H3 H4 H5 H6 : K[X])
    (hE : E ≠ 0) (hN : N ≠ 0) (htwo : (2 : K[X]) ≠ 0)
    (hcop : IsCoprime E N)
    (h012 : ConfluentRelation (E ^ 2) (N ^ 2) H0 H1 H2)
    (h234 : ConfluentRelation (E ^ 2) (N ^ 2) H2 H3 H4)
    (h456 : ConfluentRelation (E ^ 2) (N ^ 2) H4 H5 H6)
    (hH2 : H2.natDegree < 2 * (E.natDegree + N.natDegree))
    (hH4 : H4.natDegree < 2 * (E.natDegree + N.natDegree)) :
    H2 = 0 ∧ H3 = 0 ∧ H4 = 0 := by
  apply three_confluentRelations_kill_middle_triple
    (E ^ 2) (N ^ 2) H0 H1 H2 H3 H4 H5 H6
    (pow_ne_zero 2 hE) (pow_ne_zero 2 hN) htwo hcop.pow
    h012 h234 h456
  · rw [natDegree_pow, natDegree_pow]
    omega
  · rw [natDegree_pow, natDegree_pow]
    omega

/-- Vanishing of the normalized literal Pascal modes at offsets `4` and `6`
forces both value/derivative dual coefficients to vanish away from `W=0`.
The only characteristic requirement is that `2` is nonzero. -/
theorem two_even_modes_injective
    {K : Type*} [Field K]
    (W lambda0 lambda1 : K) (hW : W ≠ 0) (htwo : (2 : K) ≠ 0)
    (h4 : W ^ 4 * lambda0 + 4 * W ^ 3 * lambda1 = 0)
    (h6 : W ^ 6 * lambda0 + 6 * W ^ 5 * lambda1 = 0) :
    lambda0 = 0 ∧ lambda1 = 0 := by
  have hl1raw : (2 : K) * W ^ 5 * lambda1 = 0 := by
    linear_combination h6 - W ^ 2 * h4
  have hcoef : (2 : K) * W ^ 5 ≠ 0 :=
    mul_ne_zero htwo (pow_ne_zero 5 hW)
  have hl1 : lambda1 = 0 :=
    (mul_eq_zero.mp hl1raw).resolve_left hcoef
  rw [hl1, mul_zero, add_zero] at h4
  have hl0 : lambda0 = 0 :=
    (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 4 hW)
  exact ⟨hl0, hl1⟩

/-- Once two even modes kill the two dual coefficients, the physical terminal
mode at `K-a = 94-41 = 53` is zero.  At `W=0` it is zero directly. -/
theorem terminal53_zero_of_even_modes
    {K : Type*} [Field K]
    (W lambda0 lambda1 : K) (htwo : (2 : K) ≠ 0)
    (h4 : W ^ 4 * lambda0 + 4 * W ^ 3 * lambda1 = 0)
    (h6 : W ^ 6 * lambda0 + 6 * W ^ 5 * lambda1 = 0) :
    W ^ 53 * lambda0 + 53 * W ^ 52 * lambda1 = 0 := by
  by_cases hW : W = 0
  · subst W
    norm_num
  · obtain ⟨rfl, rfl⟩ := two_even_modes_injective W lambda0 lambda1 hW htwo h4 h6
    simp

/-- Exact degree arithmetic for the physical contacts `41,...,47`.

The even contacts have exclusive dual caps `3302,3300,3298,3296`; the odd
contacts have caps `134373,134371,134369`.  If `deg E + deg N <= 127771`,
all three displayed confluent relations are below `X^262144-1`.  If the sum
is at least `3300`, the two middle even contacts are shorter than `E*N`. -/
theorem d2_no_wrap_degree_arithmetic
    (e n : Nat) (he : 2151 ≤ e) (heUpper : e ≤ 18414)
    (hnUpper : n ≤ 149776) (hsumUpper : e + n ≤ 127771)
    (hsumLower : 3300 ≤ e + n) :
    2 * n + 3301 < 262144 ∧
      n + e + 134372 < 262144 ∧
      2 * e + 3299 < 262144 ∧
      2 * n + 3299 < 262144 ∧
      n + e + 134370 < 262144 ∧
      2 * e + 3297 < 262144 ∧
      2 * n + 3297 < 262144 ∧
      n + e + 134368 < 262144 ∧
      2 * e + 3295 < 262144 ∧
      3300 ≤ e + n ∧ 3298 ≤ e + n := by
  omega

/-- Exact all-high/step-two arithmetic for the complementary low-sum band.

The seven even physical contacts are `41,43,...,53`, with exclusive caps
`3302,3300,...,3290`.  All three fourth-order cleared relations are far below
the cyclic modulus, and the two middle contacts are shorter than `E^2*N^2`. -/
theorem d2_low_sum_stepTwo_degree_arithmetic
    (e n : Nat) (he : 2151 ≤ e) (hsum : e + n < 3300) :
    4 * n + 3301 < 262144 ∧
      2 * n + 2 * e + 3299 < 262144 ∧
      4 * e + 3297 < 262144 ∧
      4 * n + 3297 < 262144 ∧
      2 * n + 2 * e + 3295 < 262144 ∧
      4 * e + 3293 < 262144 ∧
      4 * n + 3293 < 262144 ∧
      2 * n + 2 * e + 3291 < 262144 ∧
      4 * e + 3289 < 262144 ∧
      3297 < 2 * (e + n) ∧ 3293 < 2 * (e + n) := by
  omega

#print axioms right_dvd_of_confluentRelation
#print axioms left_dvd_of_confluentRelation
#print axioms mul_dvd_middle_of_overlapping_confluentRelations
#print axioms middle_eq_zero_of_overlapping_confluentRelations
#print axioms three_confluentRelations_kill_middle_triple
#print axioms three_stepTwoRelations_kill_middle_triple
#print axioms two_even_modes_injective
#print axioms terminal53_zero_of_even_modes
#print axioms d2_no_wrap_degree_arithmetic
#print axioms d2_low_sum_stepTwo_degree_arithmetic

end
end ProximityPrize.SubmissionLower.M69ConfluentD2NoWrapGate6900
