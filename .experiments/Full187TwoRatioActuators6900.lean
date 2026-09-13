import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full187 two-ratio pure-endpoint actuators

This formal receipt isolates the first-jet algebra behind the two source-legal
classes

`q * L^(60-b) * V^b * (J2-B*Z)`, for `b=36,37`.

At the pure endpoint `J2=B*Z`, so either class is zero.  On the normalized
error slice `Z=1`, write `J2-B=d0+dE*E+dP*(T*R)+O(2)`.  The values and first
`E` (respectively first `T*R`) jets of the two classes have determinant
`L^47*d0^2`; the displayed CRT values then match the value and the selected
one of those two first jets of `L^59*V`.

This is not a simultaneous two-jet or complete-contact theorem.
-/

namespace ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- The pure `J2` coefficient after `Q=H^2` is expanded literally. -/
def pureB (L L1 L2 H H1 H2 : K) : K :=
  -2 * L ^ 2 * H1 ^ 2 - 2 * L ^ 2 * H * H2 + 4 * L * L1 * H * H1 -
    2 * L1 ^ 2 * H ^ 2 + L * L2 * H ^ 2

/-- The second normal covariant. -/
def normalJ2 (L L1 L2 V W P : K) : K :=
  L ^ 2 * P - 2 * L * L1 * W + (2 * L1 ^ 2 - L * L2) * V

/-- The endpoint identity used by both actuators. -/
theorem pure_J2_eq_BZ (L L1 L2 H H1 H2 Z : K) :
    normalJ2 L L1 L2 (-H ^ 2 * Z) (-2 * H * H1 * Z)
        (-(2 * H1 ^ 2 + 2 * H * H2) * Z) =
      pureB L L1 L2 H H1 H2 * Z := by
  unfold normalJ2 pureB
  ring

/-- At a simple error the pure-endpoint coefficient is a unit whenever `L`
and `H'` are units and the characteristic is not two. -/
theorem pureB_error_value (L L1 L2 H1 H2 : K) :
    pureB L L1 L2 0 H1 H2 = -2 * L ^ 2 * H1 ^ 2 := by
  unfold pureB
  ring

/-- The two first-`E` columns, with the common multiplier values suppressed.
The determinant is nonzero as soon as `L` and the error value `d0` are units.
-/
theorem two_ratio_E_matrix_det (L d0 dE : K) :
    (L ^ 24 * d0) * (L ^ 23 * (37 * d0 + dE)) -
      (L ^ 23 * d0) * (L ^ 24 * (36 * d0 + dE)) =
        L ^ 47 * d0 ^ 2 := by
  ring

/-- Replacing the `E` coefficient by the `T*R` coefficient leaves the same
minor. -/
theorem two_ratio_TR_matrix_det (L d0 dP : K) :
    (L ^ 24 * d0) * (L ^ 23 * (37 * d0 + dP)) -
      (L ^ 23 * d0) * (L ^ 24 * (36 * d0 + dP)) =
        L ^ 47 * d0 ^ 2 := by
  ring

/-- Explicit local coefficient values that send the `b=36,37` pair to the
value and first `E` jet of `L^59*(1+E)`. -/
theorem explicit_pair_matches_F0_value_E
    (L d0 dE : K) (hL : L ≠ 0) (hd0 : d0 ≠ 0) :
    let q36 := (36 * d0 + dE) * L ^ 35 / d0 ^ 2
    let q37 := -(35 * d0 + dE) * L ^ 36 / d0 ^ 2
    let A36 := q36 * L ^ 24 * d0
    let A37 := q37 * L ^ 23 * d0
    (A36 + A37 = L ^ 59) ∧
      (q36 * L ^ 24 * (36 * d0 + dE) +
        q37 * L ^ 23 * (37 * d0 + dE) =
          L ^ 59) := by
  dsimp
  constructor <;> field_simp [hL, hd0] <;> ring

/-- Scaling the two displayed CRT values by `t/L^59` gives an arbitrary
normalized target value. -/
theorem explicit_pair_matches_normalized_value_E
    (L d0 dE t : K) (hL : L ≠ 0) (hd0 : d0 ≠ 0) :
    let q36 := (36 * d0 + dE) * t / (L ^ 24 * d0 ^ 2)
    let q37 := -(35 * d0 + dE) * t / (L ^ 23 * d0 ^ 2)
    q36 * L ^ 24 * d0 + q37 * L ^ 23 * d0 = t ∧
      q36 * L ^ 24 * (36 * d0 + dE) +
        q37 * L ^ 23 * (37 * d0 + dE) = t := by
  dsimp
  constructor <;> field_simp [hL, hd0] <;> ring

/-- Exact target source margins.  The common minimum is the fully seeded
literal term, and `b=36` is the first legal member of this actuator family
when a degree-`<e` CRT multiplier is charged. -/
theorem actuator_source_margin_ledger :
    2 * (180413 + 81731 - 1) = 524286 ∧
    36 * (180413 - 2 * 81731) - (524286 + (81731 - 1)) = 4220 ∧
    37 * (180413 - 2 * 81731) - (524286 + (81731 - 1)) = 21171 ∧
    35 * (180413 - 2 * 81731) - (524286 + (81731 - 1)) = -12731 := by
  norm_num

/-- The exposed `BZ*V^b` term is already illegal at `b=35`, while it is
strictly legal at `b=36,37`; all other `J2` expansion terms have no smaller
margin (their exact audit is in the companion Python receipt). -/
theorem actuator_exposed_seed_term_strips :
    (81731 - 1) + 24 * 180413 + 524286 + 2 * 81731 * 36 <
      60 * 180413 ∧
    (81731 - 1) + 23 * 180413 + 524286 + 2 * 81731 * 37 <
      60 * 180413 ∧
    ¬ ((81731 - 1) + 25 * 180413 + 524286 + 2 * 81731 * 35 <
      60 * 180413) := by
  norm_num

end

end ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900

#print axioms ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900.pure_J2_eq_BZ
#print axioms ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900.two_ratio_E_matrix_det
#print axioms ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900.two_ratio_TR_matrix_det
#print axioms ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900.explicit_pair_matches_F0_value_E
#print axioms ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900.explicit_pair_matches_normalized_value_E
#print axioms ProximityPrize.SubmissionLower.Full187TwoRatioActuators6900.actuator_source_margin_ledger
