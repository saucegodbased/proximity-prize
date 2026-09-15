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
`2*S-P''-(Z-gamma)Q''`, not `S-P''-(Z-gamma)Q''`. -/
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
#print axioms c2_wc1_T_channel_integral_identity
#print axioms c2_wc1_T_channel_cancel
#print axioms target_naive_RG_C1_leading_shape_illegal
#print axioms target_naive_SG_C1_leading_shape_illegal

end
end ProximityPrize.SubmissionLower.K0OsculatingHeadCompanion6900
