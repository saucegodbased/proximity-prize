import K0SRTinyContactCore6900
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Correct first two locator-traded osculating companions

This file works only with the first three coefficients of the literal
flattened epsilon contact.  It records the sign/scaling needed by the
curvature companion when

`Y -> u0+u1*Z+epsilon*R-epsilon^2*S+epsilon^3*T`.
-/

namespace ProximityPrize.SubmissionLower.K0OsculatingHeadCompanion6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

def firstCompanion (H H1 A RG : K[X]) : K[X] :=
  H * RG - H1 * A

def secondCompanion (H H1 H2 A RG SG : K[X]) : K[X] :=
  H ^ 2 * SG - 2 * H * H1 * RG +
    (2 * H1 ^ 2 - H * H2) * A

/-- The minimal cubic-order covariant carrying a quadratic raw-slope term. -/
def thirdR2Companion (H H1 H2 A RG SG : K[X]) : K[X] :=
  2 * H * RG ^ 2 - 2 * H1 * A * RG - H * A * SG + H2 * A ^ 2

/-- The apparent quartic numerator has a literal locator factor. -/
theorem two_first_sq_sub_value_second_eq_locator_mul_third
    (H H1 H2 A RG SG : K[X]) :
    2 * firstCompanion H H1 A RG ^ 2 -
        A * secondCompanion H H1 H2 A RG SG =
      H * thirdR2Companion H H1 H2 A RG SG := by
  simp only [firstCompanion, secondCompanion, thirdR2Companion]
  ring

/-- Abstract three-coefficient form of a translated agreement locator. -/
def locatorSeries (h1 h2 : K) (tail : K[X]) : K[X] :=
  X * C h1 + X ^ 2 * C h2 + X ^ 3 * tail

def locatorDerivativeSeries (h1 h2 : K) (tail : K[X]) : K[X] :=
  C h1 + 2 * X * C h2 + X ^ 2 * tail

def locatorSecondDerivativeSeries (h2 : K) (tail : K[X]) : K[X] :=
  2 * C h2 + X * tail

/-- The centered value residual at an agreement starts in epsilon order one. -/
def valueResidualSeries (a1 a2 : K) (tail : K[X]) : K[X] :=
  X * C a1 + X ^ 2 * C a2 + X ^ 3 * tail

/-- Its raw graph-centered slope has constant coefficient `a1`. -/
def slopeResidualSeries (a1 r1 : K) (tail : K[X]) : K[X] :=
  C a1 + X * C r1 + X ^ 2 * tail

/-- For the formal `-epsilon^2*S` convention, the curvature residual which
makes the classical second covariant start in order three has constant
coefficient `2*r1-2*a2`.  Substituting the literal Taylor coefficients gives
`2*(S-hasseDeriv 2 P-(Z-gamma)*hasseDeriv 2 Q)`.  Equivalently this is
`2*S-P''-(Z-gamma)Q''`; the accepted raw `S` boundary coordinate is the
second Hasse derivative, not the ordinary second derivative. -/
def curvatureResidualSeries (a2 r1 : K) (tail : K[X]) : K[X] :=
  2 * C r1 - 2 * C a2 + X * tail

def firstLowQuotient (h1 h2 a1 a2 r1 : K) : K[X] :=
  C h1 * C r1 - C h1 * C a2 - C h2 * C a1 +
    X * (C h2 * C r1 - 2 * C h2 * C a2)

/-- Exact computation through epsilon order three.  Terms denoted by the
tails in the series definitions enter only above the certified leading
order; setting them to zero exposes the two forced cancellations. -/
theorem firstCompanion_low_jet_identity
    (h1 h2 a1 a2 r1 : K) :
    firstCompanion
      (locatorSeries h1 h2 0)
      (locatorDerivativeSeries h1 h2 0)
      (valueResidualSeries a1 a2 0)
      (slopeResidualSeries a1 r1 0) =
        X ^ 2 * firstLowQuotient h1 h2 a1 a2 r1 := by
  simp only [firstCompanion, locatorSeries, locatorDerivativeSeries,
    valueResidualSeries, slopeResidualSeries, firstLowQuotient, mul_zero,
    add_zero]
  ring

/-- With curvature constant `2*r1-2*a2`, the classical second covariant has
no epsilon-zero, -one, or -two term.  This is the exact sign/scaling audit
needed for the formal `-epsilon^2*S` convention. -/
theorem secondCompanion_low_jet_identity
    (h1 h2 a1 a2 r1 : K) :
    secondCompanion
      (locatorSeries h1 h2 0)
      (locatorDerivativeSeries h1 h2 0)
      (locatorSecondDerivativeSeries h2 0)
      (valueResidualSeries a1 a2 0)
      (slopeResidualSeries a1 r1 0)
      (curvatureResidualSeries a2 r1 0) =
        -2 * X ^ 3 * C h2 * firstLowQuotient h1 h2 a1 a2 r1 := by
  simp only [secondCompanion, locatorSeries, locatorDerivativeSeries,
    locatorSecondDerivativeSeries, valueResidualSeries,
    slopeResidualSeries, curvatureResidualSeries, firstLowQuotient,
    mul_zero, add_zero]
  ring

theorem firstCompanion_low_jet_order_two
    (h1 h2 a1 a2 r1 : K) :
    X ^ 2 ∣ firstCompanion
      (locatorSeries h1 h2 0)
      (locatorDerivativeSeries h1 h2 0)
      (valueResidualSeries a1 a2 0)
      (slopeResidualSeries a1 r1 0) := by
  rw [firstCompanion_low_jet_identity]
  exact dvd_mul_right _ _

theorem secondCompanion_low_jet_order_three
    (h1 h2 a1 a2 r1 : K) :
    X ^ 3 ∣ secondCompanion
      (locatorSeries h1 h2 0)
      (locatorDerivativeSeries h1 h2 0)
      (locatorSecondDerivativeSeries h2 0)
      (valueResidualSeries a1 a2 0)
      (slopeResidualSeries a1 r1 0)
      (curvatureResidualSeries a2 r1 0) := by
  rw [secondCompanion_low_jet_identity]
  refine ⟨-2 * C h2 * firstLowQuotient h1 h2 a1 a2 r1, ?_⟩
  ring

/-! ## Tail-uniform order and the first `R^2` seam -/

/-- The first covariant starts in order two for arbitrary higher tails.  No
relation among the tail parameters is used. -/
theorem firstCompanion_order_two
    (h1 h2 a1 a2 r1 : K)
    (hTail h1Tail aTail rTail : K[X]) :
    X ^ 2 ∣ firstCompanion
      (locatorSeries h1 h2 hTail)
      (locatorDerivativeSeries h1 h2 h1Tail)
      (valueResidualSeries a1 a2 aTail)
      (slopeResidualSeries a1 r1 rTail) := by
  let hBar : K[X] := C h1 + X * C h2 + X ^ 2 * hTail
  let aBar : K[X] := C a1 + X * C a2 + X ^ 2 * aTail
  let dBar : K[X] := C h2 + X * (h1Tail - hTail)
  let rBar : K[X] := C (r1 - a2) + X * (rTail - aTail)
  refine ⟨hBar * rBar - dBar * aBar, ?_⟩
  dsimp [hBar, aBar, dBar, rBar]
  simp only [firstCompanion, locatorSeries, locatorDerivativeSeries,
    valueResidualSeries, slopeResidualSeries, map_sub]
  ring

/-- The corrected second covariant starts in order three for arbitrary
higher tails.  Only its forced curvature constant `2*r1-2*a2` matters. -/
theorem secondCompanion_order_three
    (h1 h2 a1 a2 r1 : K)
    (hTail h1Tail h2Tail aTail rTail sTail : K[X]) :
    X ^ 3 ∣ secondCompanion
      (locatorSeries h1 h2 hTail)
      (locatorDerivativeSeries h1 h2 h1Tail)
      (locatorSecondDerivativeSeries h2 h2Tail)
      (valueResidualSeries a1 a2 aTail)
      (slopeResidualSeries a1 r1 rTail)
      (curvatureResidualSeries a2 r1 sTail) := by
  let hBar : K[X] := C h1 + X * C h2 + X ^ 2 * hTail
  let aBar : K[X] := C a1 + X * C a2 + X ^ 2 * aTail
  let dBar : K[X] := C h2 + X * (h1Tail - hTail)
  let rBar : K[X] := C (r1 - a2) + X * (rTail - aTail)
  let quotient : K[X] :=
    hBar * (hBar * (sTail - 2 * (rTail - aTail)) +
      (2 * (h1Tail - hTail) - h2Tail) * aBar) -
      2 * hBar * dBar * rBar + 2 * dBar ^ 2 * aBar
  refine ⟨quotient, ?_⟩
  dsimp [quotient, hBar, aBar, dBar, rBar]
  simp only [secondCompanion, locatorSeries, locatorDerivativeSeries,
    locatorSecondDerivativeSeries, valueResidualSeries,
    slopeResidualSeries, curvatureResidualSeries, map_sub]
  ring

/-- The R2 covariant itself starts in order three, uniformly in every higher
tail.  This is stronger and cheaper than carrying `B1^2` and `A*B2`
separately. -/
theorem thirdR2Companion_order_three
    (h1 h2 a1 a2 r1 : K)
    (hTail h1Tail h2Tail aTail rTail sTail : K[X]) :
    X ^ 3 ∣ thirdR2Companion
      (locatorSeries h1 h2 hTail)
      (locatorDerivativeSeries h1 h2 h1Tail)
      (locatorSecondDerivativeSeries h2 h2Tail)
      (valueResidualSeries a1 a2 aTail)
      (slopeResidualSeries a1 r1 rTail)
      (curvatureResidualSeries a2 r1 sTail) := by
  let hBar : K[X] := C h1 + X * C h2 + X ^ 2 * hTail
  let aBar : K[X] := C a1 + X * C a2 + X ^ 2 * aTail
  let dBar : K[X] := C h2 + X * (h1Tail - hTail)
  let rBar : K[X] := C (r1 - a2) + X * (rTail - aTail)
  let quotient : K[X] :=
    2 * hBar * aBar * (rTail - aTail) +
      (h2Tail - 2 * (h1Tail - hTail)) * aBar ^ 2 +
      2 * hBar * rBar ^ 2 - 2 * dBar * aBar * rBar -
      hBar * aBar * sTail
  refine ⟨quotient, ?_⟩
  dsimp [quotient, hBar, aBar, dBar, rBar]
  simp only [thirdR2Companion, locatorSeries,
    locatorDerivativeSeries, locatorSecondDerivativeSeries,
    valueResidualSeries, slopeResidualSeries, curvatureResidualSeries,
    map_sub]
  ring

/-- Explicit remainder after extracting the unique quadratic-slope term
from the square of the first covariant.  It is affine in `R`; hence it uses
only the lower `{raw,R}` derivative shapes. -/
def firstCompanionSquareRemainder
    (H H1 A C0 R : K[X]) : K[X] :=
  (-2 * H ^ 2 * C0 - 2 * H * H1 * A) * R +
    H ^ 2 * C0 ^ 2 + 2 * H * H1 * A * C0 + H1 ^ 2 * A ^ 2

theorem firstCompanion_square_extracts_R2
    (H H1 A C0 R : K[X]) :
    firstCompanion H H1 A (R - C0) ^ 2 =
      H ^ 2 * R ^ 2 + firstCompanionSquareRemainder H H1 A C0 R := by
  simp only [firstCompanion, firstCompanionSquareRemainder]
  ring

/-- Multiplying by an external locator power preserves the exact triangular
shape: the only `R^2` term has coefficient `H^(n+2)`. -/
theorem locator_carrier_square_extracts_R2
    (H H1 A C0 R : K[X]) (n : Nat) :
    H ^ n * firstCompanion H H1 A (R - C0) ^ 2 =
      H ^ (n + 2) * R ^ 2 +
        H ^ n * firstCompanionSquareRemainder H H1 A C0 R := by
  rw [firstCompanion_square_extracts_R2]
  rw [mul_add, ← mul_assoc, ← pow_add]

def thirdR2LowerRemainder
    (H H1 H2 A C0 R SG : K[X]) : K[X] :=
  (-4 * H * C0 - 2 * H1 * A) * R +
    2 * H * C0 ^ 2 + 2 * H1 * A * C0 - H * A * SG + H2 * A ^ 2

/-- The cubic-order companion is triangular at the literal R2 seam: its
only quadratic-slope term is `2*H*R^2`; the remainder is in `{raw,R,S}`. -/
theorem thirdR2Companion_extracts_R2
    (H H1 H2 A C0 R SG : K[X]) :
    thirdR2Companion H H1 H2 A (R - C0) SG =
      2 * H * R ^ 2 + thirdR2LowerRemainder H H1 H2 A C0 R SG := by
  simp only [thirdR2Companion, thirdR2LowerRemainder]
  ring

theorem target_R2_cubic_carrier_leading_margin :
    47 * 180413 - (45 * 180413 + 2 * (131071 - 1)) = 98686 := by
  norm_num

theorem target_R2_cubic_carrier_uniform_shift_count :
    4 * (3757 - 1) = 15024 := by
  norm_num

/-! At target, `n=m-4=43`.  The extremal monomial shapes below cover the
`H^43*B1^2` expansion: quadratic derivative shapes at active degree about
`45g`, linear shapes at `46g`, and the raw/raw product at `47g-4`. -/

theorem target_R2_carrier_extremal_shapes_legal :
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (45 * 180413) 0 0 2 0 ∧
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (45 * 180413 - 1) 0 1 1 0 ∧
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (45 * 180413 - 2) 0 2 0 0 ∧
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (46 * 180413 - 2) 0 0 1 1 ∧
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (46 * 180413 - 3) 0 1 0 1 ∧
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (47 * 180413 - 4) 0 0 0 2 := by
  norm_num [K0SRTinyContactCore6900.rawShapeLegal]

/-- The companion `H^43*A*B2` stays in the lower `{raw,R,S}` prefix.  These
are its two new curvature extrema; all raw/R/Y extrema are bounded by the
preceding ledger. -/
theorem target_lower_R_S_companion_extremal_shapes_legal :
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (45 * 180413) 1 1 0 0 ∧
    K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (46 * 180413 - 1) 1 0 0 1 := by
  norm_num [K0SRTinyContactCore6900.rawShapeLegal]

/-! ## The locally cancelable first T channel -/

def c1T (lambda : K) (n : Nat) : K := lambda ^ (n + 1)

def c2T (lambda delta eta W : K) (n : Nat) : K :=
  2 * lambda ^ n * (delta + eta * W)

def wc1T (lambda W : K) (n : Nat) : K :=
  W * lambda ^ (n + 1)

theorem c2_wc1_T_channel_integral_identity
    (lambda delta eta W : K) (n : Nat) :
    -lambda * c2T lambda delta eta W n +
        2 * eta * wc1T lambda W n =
      -2 * delta * c1T lambda n := by
  simp only [c1T, c2T, wc1T, pow_succ]
  ring

theorem c2_wc1_T_channel_cancel
    (lambda delta eta W : K) (n : Nat)
    (hdelta : delta ≠ 0) (htwo : (2 : K) ≠ 0) :
    (-lambda / (2 * delta)) * c2T lambda delta eta W n +
        (eta / delta) * wc1T lambda W n =
      -c1T lambda n := by
  simp only [c1T, c2T, wc1T, pow_succ]
  field_simp [hdelta, htwo]
  ring

/-! ## Target source ledger / naive-product obstruction -/

theorem target_C2_and_WC1_uniform_column_count :
    2 * (3757 - 1) + (3757 - 1) = 11268 := by norm_num

theorem target_naive_RG_C1_excess :
    46 * 180413 + 131071 + (131071 - 1) =
      47 * 180413 + 81728 := by norm_num

theorem target_naive_SG_C1_excess :
    46 * 180413 + 131071 + (131071 - 2) =
      47 * 180413 + 81727 := by norm_num

theorem target_naive_RG_C1_leading_shape_illegal :
    ¬ K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (46 * 180413) 0 1 1 0 := by
  norm_num [K0SRTinyContactCore6900.rawShapeLegal]

theorem target_naive_SG_C1_leading_shape_illegal :
    ¬ K0SRTinyContactCore6900.rawShapeLegal
      (47 * 180413) 131071 3757 16 8 64
      (46 * 180413) 1 1 0 0 := by
  norm_num [K0SRTinyContactCore6900.rawShapeLegal]

#print axioms firstCompanion_low_jet_identity
#print axioms secondCompanion_low_jet_identity
#print axioms firstCompanion_low_jet_order_two
#print axioms secondCompanion_low_jet_order_three
#print axioms firstCompanion_order_two
#print axioms secondCompanion_order_three
#print axioms two_first_sq_sub_value_second_eq_locator_mul_third
#print axioms thirdR2Companion_order_three
#print axioms firstCompanion_square_extracts_R2
#print axioms locator_carrier_square_extracts_R2
#print axioms thirdR2Companion_extracts_R2
#print axioms target_R2_carrier_extremal_shapes_legal
#print axioms target_lower_R_S_companion_extremal_shapes_legal
#print axioms c2_wc1_T_channel_integral_identity
#print axioms c2_wc1_T_channel_cancel
#print axioms target_naive_RG_C1_leading_shape_illegal
#print axioms target_naive_SG_C1_leading_shape_illegal

end
end ProximityPrize.SubmissionLower.K0OsculatingHeadCompanion6900
