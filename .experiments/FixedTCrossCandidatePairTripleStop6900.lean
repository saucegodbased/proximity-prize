import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fixed-T,C cross-candidate pair/triple STOP at 6900

Suppose a family is presented by

`T * B_i - C = H_i * R_i`,

where `T,C` are fixed, `H_i` is the split agreement locator, and the new
residual bound is `deg R_i <= 51673`.  The first theorem records the cheapest
pair eliminant: subtracting two rows removes `C`, but after removing the fixed
factor `T` the surviving polynomial is exactly `B_i-B_j`, whose degree cap is
still `149485`.

The two construction schemas show this is not an artifact of a loose degree
estimate.  A pair can attain a common locator of degree `149485` with constant
residuals.  A genuinely non-collinear triple can attain a common locator of
degree `149484`, while all three residuals have degree at most `30929`.

The final receipts check that both the pair and optimistic non-collinear
triple incidence moments remain feasible one above the target allowance.
-/

namespace ProximityPrize.SubmissionLower.FixedTCrossCandidatePairTripleStop6900

open Polynomial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

noncomputable section

/-- Subtraction is the minimal fixed-`C` pair eliminant. -/
theorem fixed_coset_pair_eliminant
    {K : Type*} [Field K]
    (T C B0 B1 H0 H1 R0 R1 : K[X])
    (h0 : T * B0 - C = H0 * R0)
    (h1 : T * B1 - C = H1 * R1) :
    H1 * R1 - H0 * R0 = T * (B1 - B0) := by
  rw [← h1, ← h0]
  ring

/-- Exact tight pair schema.  Put `T=S1-S0`, `B0=0`, `B1=G`,
`C=-G*S0`, and `Hi=G*Si`.  Both residuals are the constant one. -/
theorem pair_tight_factorization_schema
    {K : Type*} [Field K] (G S0 S1 : K[X]) :
    let T := S1 - S0
    let C := -(G * S0)
    let B0 : K[X] := 0
    let B1 := G
    let H0 := G * S0
    let H1 := G * S1
    T * B0 - C = H0 * 1 ∧ T * B1 - C = H1 * 1 := by
  dsimp only
  constructor <;> ring

/-- Exact tight non-collinear triple schema.  A CRT construction supplies
`T` with `S0+T=S1*R1` and `S0+X*T=S2*R2`.  The scalar polynomials are
`0,G,GX`; the common locator factor is `G`. -/
theorem triple_tight_factorization_schema
    {K : Type*} [Field K] (G S0 S1 S2 T R1 R2 : K[X])
    (h1 : S0 + T = S1 * R1)
    (h2 : S0 + X * T = S2 * R2) :
    let C := -(G * S0)
    let B0 : K[X] := 0
    let B1 := G
    let B2 := G * X
    let H0 := G * S0
    let H1 := G * S1
    let H2 := G * S2
    T * B0 - C = H0 * 1 ∧
      T * B1 - C = H1 * R1 ∧
      T * B2 - C = H2 * R2 := by
  dsimp only
  constructor
  · ring
  constructor
  · calc
      T * G - -(G * S0) = G * (S0 + T) := by ring
      _ = G * (S1 * R1) := by rw [h1]
      _ = (G * S1) * R1 := by ring
  · calc
      T * (G * X) - -(G * S0) = G * (S0 + X * T) := by ring
      _ = G * (S2 * R2) := by rw [h2]
      _ = (G * S2) * R2 := by ring

/-- The three scalars `0,G,GX` are genuinely non-collinear whenever `G` is
nonzero: `GX` is not a scalar multiple of `G`. -/
theorem zero_G_GX_not_collinear
    {K : Type*} [Field K] (G : K[X]) (hG : G ≠ 0) :
    ¬ ∃ a : K, G * X = C a * G := by
  rintro ⟨a, ha⟩
  have hx : (X : K[X]) = C a := by
    apply (mul_left_cancel₀ hG)
    simpa only [mul_comm] using ha
  have hcoeff := congrArg (fun P : K[X] ↦ P.coeff 1) hx
  simpa using hcoeff

/-- Degree ledger for the tight pair and triple schemas. -/
theorem tight_schema_degree_and_node_ledger :
    180413 - 149485 = 30928 ∧
      149485 + 2 * 30928 = 211341 ∧
      211341 ≤ 261852 ∧
      180413 - 149484 = 30929 ∧
      149484 + 3 * 30929 = 242271 ∧
      242271 ≤ 261852 ∧
      2 * 30929 = 61858 ∧
      61857 < 82601 ∧
      30929 ≤ 51673 ∧
      149484 + 1 = 149485 ∧
      149484 + 30929 = 180413 ∧
      180413 ≤ 231508 := by
  norm_num

/-- The full pair determinant has degree `232086`; cancelling its known
fixed factor merely returns the old degree-`149485` scalar difference. -/
theorem cheapest_pair_degree_ledger :
    82601 + 149485 = 232086 ∧
      180413 + 51673 = 232086 ∧
      232086 - 82601 = 149485 := by
  norm_num

/-- Pair and non-collinear triple leading coefficients both have the wrong
sign.  The displayed positive quantities are the exact deficits. -/
theorem pair_and_triple_leading_moment_deficits :
    180413 ^ 2 + 6594095651 = 261852 * 149485 ∧
      180413 ^ 3 + 4377354409424539 = 261852 ^ 2 * 149484 := by
  norm_num

/-- Exact caps at which the leading pair/triple moment signs finally turn
positive.  Increasing either cap by one reverses the sign. -/
theorem pair_and_triple_required_cap_thresholds :
    261852 * 124302 + 123265 = 180413 ^ 2 ∧
      180413 ^ 2 + 138587 = 261852 * 124303 ∧
      261852 ^ 2 * 85642 + 66162186629 = 180413 ^ 3 ∧
      180413 ^ 3 + 2404283275 = 261852 ^ 2 * 85643 := by
  norm_num

def chooseTwo (n : Nat) : Nat := n * (n - 1) / 2
def chooseThree (n : Nat) : Nat := n * (n - 1) * (n - 2) / 6

/-- Even at one candidate above the required allowance, the exact balanced
pair and triple lower moments fit below the optimistic caps `W` and `W-1`.
For the triple inequality we pretend every triple is non-collinear, which is
strictly stronger than the actual hypotheses. -/
theorem allowance_plus_one_balanced_moments_are_feasible :
    let L : Nat := 875068543039974
    let n : Nat := 261852
    let A : Nat := 180413
    let W : Nat := 149485
    let u : Nat := 602912107050818
    let rem : Nat := 34326
    L * A = n * u + rem ∧ rem < n ∧
      (n - rem) * chooseTwo u + rem * chooseTwo (u + 1) ≤
        W * chooseTwo L ∧
      (n - rem) * chooseThree u + rem * chooseThree (u + 1) ≤
        (W - 1) * chooseThree L := by
  norm_num [chooseTwo, chooseThree]

#print axioms fixed_coset_pair_eliminant
#print axioms pair_tight_factorization_schema
#print axioms triple_tight_factorization_schema
#print axioms zero_G_GX_not_collinear
#print axioms tight_schema_degree_and_node_ledger
#print axioms cheapest_pair_degree_ledger
#print axioms pair_and_triple_leading_moment_deficits
#print axioms pair_and_triple_required_cap_thresholds
#print axioms allowance_plus_one_balanced_moments_are_feasible

end
end ProximityPrize.SubmissionLower.FixedTCrossCandidatePairTripleStop6900
