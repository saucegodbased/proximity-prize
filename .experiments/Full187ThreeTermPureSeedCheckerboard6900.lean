import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full187 three-term pure-seed checkerboard

This is a precise correction to a too-coarse endpoint intuition.  The 187
normal shell contains source-legal three-term combinations which cancel the
pure-seed leading coefficient.  Thus a proof which separately charges that
coefficient cannot dismiss all multi-packet combinations.

It is deliberately not advertised as a contact correction.  Its last term
has a unique order-two normal error initial form on the `S` line.  The missing
mixed-H / mixed-normal-stratum calculation is exactly whether other shell
blocks can cancel that exposed class while preserving the strict windows.
-/

namespace ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900

set_option autoImplicit false

noncomputable section

variable {K : Type*} [CommRing K]

/-- Pure-seed values of the three normal coordinates.  In the literal
specialisation `V=Y-H^2 Z`, the sign in `pureV` is important. -/
def pureV (H Z : K) : K := -(H ^ 2 * Z)
def pureJ1 (H U Z : K) : K := H * U * Z
def pureJ2 (B Z : K) : K := B * Z

/-- An explicit three-shell checkerboard.  The three normal shapes are all
in the literal 187 set:
`(52,4,0)`, `(53,2,1)`, and `(54,0,2)`. -/
theorem explicit_three_term_pure_seed_checkerboard (H U B Z : K) :
    B * pureV H Z ^ 52 * pureJ1 H U Z ^ 4 -
        (B - U ^ 2) * pureV H Z ^ 53 * pureJ1 H U Z ^ 2 * pureJ2 B Z -
        U ^ 2 * pureV H Z ^ 54 * pureJ2 B Z ^ 2 = 0 := by
  simp only [pureV, pureJ1, pureJ2]
  ring

/-- A literal three-term checkerboard across distinct normal degrees and
distinct `H` strata.  The `Z` and `H` prefactors align the three pure tails.
The normal shapes are `(60,0,0)`, `(58,1,0)`, `(56,2,0)`, with
`r=c+2d=0,1,2`. -/
theorem explicit_mixed_H_three_term_checkerboard (H U Z : K) :
    U ^ 2 * pureV H Z ^ 60 -
        2 * U * H ^ 3 * Z * pureV H Z ^ 58 * pureJ1 H U Z +
        H ^ 6 * Z ^ 2 * pureV H Z ^ 56 * pureJ1 H U Z ^ 2 = 0 := by
  simp only [pureV, pureJ1]
  ring

/-- The normal-shell bookkeeping for all three displayed terms. -/
theorem displayed_shell_triples_legal :
    52 = 60 - 2 * 4 - 3 * 0 ∧
    53 = 60 - 2 * 2 - 3 * 1 ∧
    54 = 60 - 2 * 0 - 3 * 2 ∧
    4 + 0 ≤ 21 ∧ 2 + 1 ≤ 21 ∧ 0 + 2 ≤ 21 ∧
    0 ≤ 10 ∧ 1 ≤ 10 ∧ 2 ≤ 10 := by
  norm_num

theorem mixed_H_shell_triples_and_seed_shifts_legal :
    60 = 60 - 2 * 0 - 3 * 0 ∧
    58 = 60 - 2 * 1 - 3 * 0 ∧
    56 = 60 - 2 * 2 - 3 * 0 ∧
    60 + 0 ≤ 2703 ∧ 59 + 1 ≤ 2703 ∧ 58 + 2 ≤ 2703 ∧
    0 + 0 ≤ 21 ∧ 1 + 0 ≤ 21 ∧ 2 + 0 ≤ 21 := by
  norm_num

/-- For a shell `r=c+2d`, the pure-seed strict X window is independent of
the particular `d`.  The degree 524286 bound simultaneously covers the
pure `J2` coefficient and the square of the pure `J1` coefficient. -/
theorem pure_seed_window_formula (r : Nat) :
    60 * (180413 - 2 * 81731) -
        (180413 - 2 * 81731 - 1) * r = 1017060 - 16950 * r := by
  omega

theorem pure_seed_degree_bound_fits_through_r29
    (r : Nat) (hr : r ≤ 29) :
    524286 < 1017060 - 16950 * r := by
  omega

theorem displayed_checkerboard_strict_window :
    2 * (180413 + 81731 - 1) = 524286 ∧
    1017060 - 16950 * 4 = 949260 ∧
    524286 < 949260 ∧ 949260 - 524286 = 424974 := by
  norm_num

/-- Exact strict-window ledger after a CRT multiplier of degree `< e` is
attached to the mixed-stratum checkerboard.  The three bounds correspond to
`q*U^2`, `q*U*H^3`, and `q*H^6`. -/
theorem mixed_H_checkerboard_CRT_window_ledger :
    81730 + 2 * (180413 + 81731 - 1) = 606016 ∧
    81730 + (180413 + 81731 - 1) + 3 * 81731 = 589066 ∧
    81730 + 6 * 81731 = 572116 ∧
    606016 < 1017060 ∧ 589066 < 1000110 ∧ 572116 < 983160 := by
  norm_num

/-- Reducing the mixed checkerboard at an error leaves `U^2`.  Thus a CRT
multiplier gives a controllable value, though the identity does not itself
cancel the higher error jets contributed by `V^60`. -/
theorem mixed_H_checkerboard_error_value (U : K) :
    U ^ 2 * (1 : K) ^ 60 -
        2 * U * (0 : K) ^ 3 * (1 : K) * (1 : K) ^ 58 * U +
        (0 : K) ^ 6 * (1 : K) ^ 2 * (1 : K) ^ 56 * U ^ 2 = U ^ 2 := by
  ring

/-- The S-line residual of the displayed checkerboard.  On the first normal
error associated-graded line `E=R=0`, `J1` vanishes but `J2=L^2*S`; hence
the pure-tail cancellation leaves a nonzero quadratic class whenever `U,L`
are units. -/
theorem error_S_line_exposed_quadratic (U L S : K) :
    -(U ^ 2) * (L ^ 2 * S) ^ 2 = -(U ^ 2 * L ^ 4 * S ^ 2) := by
  ring

end

end ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900

#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.explicit_three_term_pure_seed_checkerboard
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.explicit_mixed_H_three_term_checkerboard
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.displayed_shell_triples_legal
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.mixed_H_shell_triples_and_seed_shifts_legal
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.pure_seed_window_formula
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.pure_seed_degree_bound_fits_through_r29
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.displayed_checkerboard_strict_window
#print axioms ProximityPrize.SubmissionLower.Full187ThreeTermPureSeedCheckerboard6900.mixed_H_checkerboard_CRT_window_ledger
