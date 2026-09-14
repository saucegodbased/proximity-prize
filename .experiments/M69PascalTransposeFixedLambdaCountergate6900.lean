import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The literal m69 Pascal transpose is not a fixed-lambda power sequence

For the exact deficient chain `(r,s,q)=(0,0,26)`, the deficient contact
indices are `Y={41,42}` and the terminal contact is `T=94`.  A dual pair
`(lambda_41,lambda_42)` acts on a source at contact `k` through

`mu_k = choose(k,41) W^(k-41) lambda_41
      + choose(k,42) W^(k-42) lambda_42`.

Thus the transpose has a Pascal sum of independent output covectors.  It is
not the fixed-covector sequence `lambda*W^k` used by the earlier adjacent
power recurrence.  The last theorem gives an exact counterexample in every
field of the benchmark characteristic.  It even annihilates the terminal
`k=94` channel pointwise, so adding the terminal channel alone does not
restore the claimed recurrence.
-/

namespace ProximityPrize.SubmissionLower.M69PascalTransposeFixedLambdaCountergate6900

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- At source contact 41 only the first output covector is active. -/
def mu41 {K : Type*} [CommRing K] (_W lambda41 _lambda42 : K) : K :=
  lambda41

/-- The two relevant Pascal coefficients at source contact 42. -/
def mu42 {K : Type*} [CommRing K] (W lambda41 lambda42 : K) : K :=
  42 * W * lambda41 + lambda42

/-- The two relevant Pascal coefficients at source contact 43. -/
def mu43 {K : Type*} [CommRing K] (W lambda41 lambda42 : K) : K :=
  903 * W ^ 2 * lambda41 + 43 * W * lambda42

/-- The terminal `k=94` transpose row for the chain `Y={41,42}`. -/
def mu94 {K : Type*} [CommRing K] (W lambda41 lambda42 : K) : K :=
  760365888182828026538367852 * W ^ 53 * lambda41 +
  959509335087854414441273718 * W ^ 52 * lambda42

/-- Receipt that the displayed numerals are the literal Pascal coefficients. -/
theorem literal_pascal_coefficient_receipt :
    Nat.choose 41 41 = 1 ∧
    Nat.choose 41 42 = 0 ∧
    Nat.choose 42 41 = 42 ∧
    Nat.choose 42 42 = 1 ∧
    Nat.choose 43 41 = 903 ∧
    Nat.choose 43 42 = 43 ∧
    Nat.choose 94 41 = 760365888182828026538367852 ∧
    Nat.choose 94 42 = 959509335087854414441273718 := by
  norm_num [Nat.choose]

/-- Both first contacts have Hasse depth/order `26`; their only difference is
the alternating high/low coefficient prefix.  Thus the same invertible
normalized Hasse scalar occurs on both channels. -/
theorem literal_chain_width_receipt :
    69 * 180413 - 131071 * 41 = 26 * 262144 + 258842 ∧
    69 * 180413 - 131071 * 42 = 26 * 262144 + 127771 := by
  norm_num

/-- The exact correction term to the falsely expected geometric step. -/
theorem pascal_step_defect
    {K : Type*} [CommRing K] (W lambda41 lambda42 : K) :
    mu43 W lambda41 lambda42 - W * mu42 W lambda41 lambda42 =
      861 * W ^ 2 * lambda41 + 42 * W * lambda42 := by
  simp only [mu42, mu43]
  ring

/-- The nonzero pair `(53,-42W)` kills the entire terminal transpose row. -/
theorem terminal_row_pointwise_cancel
    {K : Type*} [CommRing K] (W : K) :
    mu94 W 53 (-42 * W) = 0 := by
  simp only [mu94]
  ring

/-- Despite terminal cancellation, the adjacent fixed-power relation has the
exact defect `43869*W^2`. -/
theorem terminal_null_pair_step_defect
    {K : Type*} [CommRing K] (W : K) :
    mu43 W 53 (-42 * W) - W * mu42 W 53 (-42 * W) =
      43869 * W ^ 2 := by
  rw [pascal_step_defect]
  ring

/-- The first high/low pair is an even cleaner failure: both source contacts
have the same Hasse depth and order, yet the second effective covector also
contains the independent output covector `lambda_42`. -/
theorem terminal_null_pair_first_step_defect
    {K : Type*} [CommRing K] (W : K) :
    mu42 W 53 (-42 * W) - W * mu41 W 53 (-42 * W) = 2131 * W := by
  simp only [mu41, mu42]
  ring

/-- In benchmark characteristic the defect cannot vanish for nonzero `W`.
This is the promised exact counterexample to recovering the fixed-lambda
recurrence from the terminal constraint. -/
theorem benchmark_terminal_constraint_does_not_restore_fixed_power
    {K : Type*} [Field K] [CharP K 2130706433]
    (W : K) (hW : W ≠ 0) :
    mu94 W 53 (-42 * W) = 0 ∧
    mu42 W 53 (-42 * W) ≠ W * mu41 W 53 (-42 * W) := by
  constructor
  · exact terminal_row_pointwise_cancel W
  · intro heq
    have hzero : (2131 : K) * W = 0 := by
      rw [← terminal_null_pair_first_step_defect W, heq, sub_self]
    have hcast : (2131 : K) ≠ 0 := by
      intro hz
      have hdvd := (CharP.cast_eq_zero_iff K 2130706433 2131).mp hz
      norm_num at hdvd
    exact (mul_ne_zero hcast hW) hzero

#print axioms pascal_step_defect
#print axioms terminal_row_pointwise_cancel
#print axioms terminal_null_pair_step_defect
#print axioms terminal_null_pair_first_step_defect
#print axioms benchmark_terminal_constraint_does_not_restore_fixed_power

end ProximityPrize.SubmissionLower.M69PascalTransposeFixedLambdaCountergate6900
