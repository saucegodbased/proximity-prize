import OriginalPassiveSeedSource6900
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Countergate for the proposed Full187 order-four quadratic covariant

The proposed prolongation starts from

`T2(A) = A*W^2 - A'*V*W + (A''/2)*V^2 - (A/2)*V*P`

and forms `A*D(T2(A)) - 3*A'*T2(A)`.  If one differentiates honestly with
`V'=W`, `W'=P`, then the result contains the term

`-(A^2/2)*V*P'`.

The current order-two source has only `(X,Y,R,S)` (and the passive outer
seed), so the proposed truncated formula drops `P'`.  This file checks on
the literal `localSeedSubstitution` chart that the truncation is only order
three.  It also gives the one-variable rational Taylor witness behind the
same failure.  This is research-only and makes no production edit.
-/

namespace ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900

open Polynomial
open Order2SourceRank Order2PassiveSeedSource

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- The part of `A*D(T2(A))-3*A'*T2(A)` that remains after silently
dropping the required `-(A^2/2)*V*P'` term.  The arguments are the first
three locator jets and the available value/slope/curvature variables. -/
def truncatedC3
    (A A1 A2 A3 V W P : K) : K :=
  -3 * A * A1 * W ^ 2 + 3 * A1 ^ 2 * V * W +
    (3 / 2 : K) * A ^ 2 * W * P +
    ((A * A3 - 3 * A1 * A2) / 2) * V ^ 2

/-- The honest differentiated expression necessarily has one more term,
with `P3=P'` the unavailable third jet. -/
def fullC3
    (A A1 A2 A3 V W P P3 : K) : K :=
  truncatedC3 A A1 A2 A3 V W P - (A ^ 2 / 2) * V * P3

/-- Direct product-rule expansion of `A*D(T2(A))-3*A'*T2(A)` under
`A'=A1`, `A1'=A2`, `A2'=A3`, `V'=W`, `W'=P`, and `P'=P3`.
This theorem prevents the third-jet term from being lost by notation. -/
theorem differentiated_T2_exact
    (A A1 A2 A3 V W P P3 : K) (h2 : (2 : K) ≠ 0) :
    A *
        (A1 * W ^ 2 + 2 * A * W * P -
          (A2 * V * W + A1 * (W ^ 2 + V * P)) +
          (A3 * V ^ 2 / 2 + A2 * V * W) -
          (A1 * V * P / 2 + A * (W * P + V * P3) / 2)) -
        3 * A1 *
          (A * W ^ 2 - A1 * V * W + A2 * V ^ 2 / 2 -
            A * V * P / 2) =
      fullC3 A A1 A2 A3 V W P P3 := by
  unfold fullC3 truncatedC3
  field_simp [h2]
  ring

/-- Seed-independent source representative of the truncated expression in
the simplest locator chart `A=X`, `A'=1`, `A''=A'''=0`, with
`(V,W,P)=(Y,R,S)`. -/
def literalTruncatedC3X (K : Type*) [Field K] : Poly4 K :=
  -3 * contactZ K * slopeR K ^ 2 +
    3 * errorE K * slopeR K +
    (3 : K) • ((2 : K)⁻¹ •
      (contactZ K ^ 2 * slopeR K * curvatureS K))

/-- On the exact local order-two contact chart, all apparent leading terms
cancel and the omitted-third-jet residue is exactly `3*E*R`. -/
theorem localSubstitution_literalTruncatedC3X
    :
    localSubstitution Rat 0 0 (literalTruncatedC3X Rat) =
      3 * errorE Rat * slopeR Rat := by
  simp only [literalTruncatedC3X, map_add, map_mul, map_pow,
    map_neg, map_ofNat, map_smul, localSubstitution_Z,
    localSubstitution_E, localSubstitution_R, localSubstitution_S]
  unfold contactY halfZSquared
  simp only [map_inv₀, map_ofNat, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]
  norm_num
  ring

/-- The same identity through the literal passive-seed map named by the
Full187 caller.  No generic contact intuition is used here. -/
theorem localSeedSubstitution_literalTruncatedC3X
    :
    localSeedSubstitution Rat 0 0 0
        (Polynomial.C (literalTruncatedC3X Rat)) =
      Polynomial.C (3 * errorE Rat * slopeR Rat) := by
  rw [localSeedSubstitution_C]
  simp only [literalTruncatedC3X, map_add, map_mul, map_pow,
    map_neg, map_ofNat, map_smul, localSeedInnerSubstitution_X,
    localSeedInnerSubstitution_Y, localSeedInnerSubstitution_R,
    localSeedInnerSubstitution_S]
  unfold contactY halfZSquared
  simp only [map_inv₀, map_ofNat, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]
  norm_num
  ring

/-- Exponent of the surviving literal `E*R` monomial. -/
def expER : Fin 4 →₀ Nat :=
  Finsupp.single 1 1 + Finsupp.single 2 1

theorem threeER_eq_monomial :
    3 * errorE Rat * slopeR Rat =
      MvPolynomial.monomial expER (3 : Rat) := by
  change MvPolynomial.C (3 : Rat) * MvPolynomial.X 1 *
      MvPolynomial.X 2 = _
  simp only [MvPolynomial.X, MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul]
  simp [expER]

@[simp] theorem shiftedContactWeight_expER :
    shiftedContactWeight expER = 3 := by
  simp [expER, shiftedContactWeight]

/-- Its coefficient survives truncation below order four, so the literal
candidate is not in the order-four contact kernel. -/
theorem contactTruncation_four_threeER_ne_zero :
    contactTruncation Rat 4
        (3 * errorE Rat * slopeR Rat) ≠ 0 := by
  intro h
  have hc : MvPolynomial.coeff expER
      (contactTruncation Rat 4 (3 * errorE Rat * slopeR Rat)) = 0 := by
    rw [h]
    simp
  rw [coeff_contactTruncation, if_pos (by simp)] at hc
  have hc' : (3 : Rat) = 0 := by
    rw [threeER_eq_monomial] at hc
    simpa using hc
  norm_num at hc'

theorem literal_seed_contact_order_four_fails :
    seedContactTruncation Rat 4
        (localSeedSubstitution Rat 0 0 0
          (Polynomial.C (literalTruncatedC3X Rat))) ≠ 0 := by
  rw [localSeedSubstitution_literalTruncatedC3X]
  rw [show Polynomial.C (3 * errorE Rat * slopeR Rat) =
      Polynomial.monomial 0 (3 * errorE Rat * slopeR Rat) by simp]
  rw [seedContactTruncation_monomial]
  intro h
  have hc := congrArg (fun p : SeedPoly Rat ↦ p.coeff 0) h
  simp only [Polynomial.coeff_monomial, if_pos rfl, Polynomial.coeff_zero] at hc
  exact contactTruncation_four_threeER_ne_zero hc

/-! ## Small rational Taylor receipt

Along `A=t`, `V=t+t^3/6`, `W=1+t^2/2`, `P=t`, and `P'=1`, the literal
survivor `3*E*R` has cubic coefficient `3*(1/6)*1=1/2`.  The omitted term
has coefficient `-1/2`, and only their sum has zero cubic coefficient. -/

theorem rational_fixture_cubic_ledger :
    (3 : Rat) * (1 / 6) * 1 = 1 / 2 ∧
      (-(1 / 2 : Rat)) * 1 ^ 2 * 1 * 1 = -1 / 2 ∧
      (3 : Rat) * (1 / 6) * 1 + (-(1 / 2 : Rat)) * 1 ^ 2 * 1 * 1 = 0 := by
  norm_num

/-! ## The four honest order-four generators do not remove the tail gate

For `Q=H^2`, after the scalar error correction has acquired one factor of
`H`, the `YZ`, `SZ`, and `RZ` mixed coefficients of the four valid
quadratic generators have the following factors (irrelevant nonzero scalar
constants suppressed only in the prose, not in the identities):

* `A^2 V^2`: `A^2 H^3`;
* `-A V T1(A)`: `2 A H^2 (A H' - A' H)`;
* `2 A T2(A)`: `A^2 H^3`;
* `T1(A)^2`: `2 A H^2 (A' H - 2 A H')`.

Thus the first and third really inherit the old `H^3` factor.  The second
and fourth do not: they retain a logarithmic-Wronskian quotient.  Their
total degrees are nevertheless only one derivative lower, so each isolated
generator still overruns a literal mixed source strip.  This does not rule
out cancellation among the four-generator span.
-/

section FourGeneratorTails

variable {R : Type*} [CommRing R]

theorem four_generator_mixed_tail_factorizations
    (A A1 H H1 : R) :
    H * (A ^ 2 * H ^ 2) = A ^ 2 * H ^ 3 ∧
      H * (A ^ 2 * (2 * H * H1) - 2 * A * A1 * H ^ 2) =
        2 * A * H ^ 2 * (A * H1 - A1 * H) ∧
      H * (A ^ 2 * H ^ 2) = A ^ 2 * H ^ 3 ∧
      H * (2 * A * (A1 * H ^ 2 - A * (2 * H * H1))) =
        2 * A * H ^ 2 * (A1 * H - 2 * A * H1) := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end FourGeneratorTails

/-- Exact target arithmetic for the isolated mixed tails.  The entries are,
respectively, the `A^2V^2` `YZ` tail, the `-AVT1` `YZ` tail, the `2AT2`
`SZ` tail, and the `T1^2` `RZ` (equivalently its one-lower `YZ`) tail. -/
theorem target_four_generator_mixed_tail_overruns :
    58 * 180413 + 3 * 81731 = 10709147 ∧
      60 * 180413 - 131071 = 10693709 ∧
      10709147 - 10693709 = 15438 ∧
      (58 * 180413 + 3 * 81731 - 1) - 10693709 = 15437 ∧
      60 * 180413 - (131071 - 2) = 10693711 ∧
      10709147 - 10693711 = 15436 ∧
      60 * 180413 - (131071 - 1) = 10693710 ∧
      (58 * 180413 + 3 * 81731 - 1) - 10693710 = 15436 ∧
      (58 * 180413 + 3 * 81731 - 2) - 10693709 = 15436 := by
  norm_num

end

end ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900

#print axioms ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900.differentiated_T2_exact
#print axioms ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900.localSeedSubstitution_literalTruncatedC3X
#print axioms ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900.literal_seed_contact_order_four_fails
#print axioms ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900.rational_fixture_cubic_ledger
#print axioms ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900.four_generator_mixed_tail_factorizations
#print axioms ProximityPrize.SubmissionLower.Full187OrderFourCovariantCountergate6900.target_four_generator_mixed_tail_overruns
