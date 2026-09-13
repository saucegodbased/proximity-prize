import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Full187 normal-monomial family: exact error-filtration frontier

At a retained error of the target control `Q=H^2`, the weight-zero part of
`V` is a unit and its nonconstant contact variable is `E`, of weight three.
Thus the tempting claim that a total-degree-`k` Veronese row needs `H^60`
is false.  After triangular extraction of the coefficient of
`E^b R^c S^d`, only `H^(60-3b)` is forced.

This file records the exact triangular leading matrix, transfers that local
root multiplicity from `p*L^n` to `p`, and proves the sharp target arithmetic
frontier.  Every extracted layer `b <= 13` is source-impossible after its
forced error-locator power; the first legal escape is already
`(b,c,d)=(14,17,4)`.  Hence this is a decisive low-error-degree STOP, but
not a STOP for the entire normal-monomial family.
-/

namespace ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900

open Matrix Polynomial
open scoped Matrix Polynomial BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- Highest `(E,R,S)` coefficients of `(V,J1,J2)` at an error.  Lower
triangular entries contain locator jets, but the diagonal is `1,L,L^2`. -/
def normalTopChange (L L' L'' : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
     -L', L, 0;
     2 * (L') ^ 2 - L * L'', -2 * L * L', L ^ 2]

theorem normalTopChange_det (L L' L'' : K) :
    (normalTopChange L L' L'').det = L ^ 3 := by
  simp [normalTopChange, Matrix.det_fin_three]
  ring

/-- In particular the leading change of variables is nonsingular at every
error, where the agreement locator `L` is a unit. -/
theorem normalTopChange_nonsingular
    (L L' L'' : K) (hL : L ≠ 0) :
    (normalTopChange L L' L'').det ≠ 0 := by
  rw [normalTopChange_det]
  exact pow_ne_zero _ hL

/-- The triangular coefficient of the literal leading shape
`Y^b R^c S^d` in

`p * L^ell * V^b * J1^c * J2^d`

is exactly `p*L^(ell+c+2d)`.  This scalar identity is the algebraic payload
used by the lexicographic top-shape extraction. -/
theorem leading_shape_coefficient
    (p L : K) (ell b c d : Nat) :
    p * L ^ ell * 1 ^ b * L ^ c * (L ^ 2) ^ d =
      p * L ^ (ell + c + 2 * d) := by
  rw [one_pow, ← pow_mul]
  simp [mul_assoc, ← pow_add]

/-- Multiplication by a locator which is nonzero at the error does not hide
any of the forced root multiplicity of the extracted scalar coefficient. -/
theorem unit_locator_transfers_rootMultiplicity
    (p L : K[X]) (x : K) (n contactDepth : Nat)
    (hp : p ≠ 0) (hLpoly : L ≠ 0) (hL : L.eval x ≠ 0)
    (hcontact : contactDepth ≤ (p * L ^ n).rootMultiplicity x) :
    contactDepth ≤ p.rootMultiplicity x := by
  have hLpow : L ^ n ≠ 0 := pow_ne_zero _ hLpoly
  have hprod : p * L ^ n ≠ 0 := mul_ne_zero hp hLpow
  have hunit : (L ^ n).rootMultiplicity x = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    simpa [Polynomial.IsRoot] using pow_ne_zero n hL
  rw [Polynomial.rootMultiplicity_mul hprod, hunit, add_zero] at hcontact
  exact hcontact

/-- Fixed finite-node version of the preceding interface.  It does not
replace the contact extraction: its hypothesis is precisely what the
lexicographic `E^b R^c S^d` induction must supply at each actual error. -/
theorem all_errors_force_multiplier_power
    {I : Type*} [Fintype I] [DecidableEq I]
    (node : I ↪ K) (p L : K[X]) (n contactDepth : Nat)
    (hp : p ≠ 0) (hLpoly : L ≠ 0)
    (hL : ∀ i, L.eval (node i) ≠ 0)
    (hcontact : ∀ i,
      contactDepth ≤ (p * L ^ n).rootMultiplicity (node i)) :
    (∏ i, (Polynomial.X - Polynomial.C (node i)) ^ contactDepth) ∣ p := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact (Polynomial.pairwise_coprime_X_sub_C node.injective hij).pow
  · intro i hi
    apply (Polynomial.le_rootMultiplicity_iff hp).mp
    exact unit_locator_transfers_rootMultiplicity p L (node i) n contactDepth
      hp hLpoly (hL i) (hcontact i)

/-- Exact source impossibility for every low `E`-degree layer.  Here
`ell=60-(b+2c+3d)` is the literal nonnegative locator exponent.  The right
side is the coefficient degree forced by `H^(60-3b)` plus the source shift.
Even the best low layer exceeds its strict cutoff by at least 38,697. -/
theorem target_low_error_degree_forced_power_overrun
    (b c d : Nat)
    (hb : b ≤ 13) (hdegreeLow : 2 ≤ b + c + d)
    (hdegreeHigh : b + c + d ≤ 82)
    (hslope : c + d ≤ 21) (hcurv : d ≤ 10) :
    60 * 180413 + 38697 ≤
      (60 - 3 * b) * 81731 +
        (60 - (b + 2 * c + 3 * d) + c + 2 * d) * 180413 +
        131071 * b + (131071 - 1) * c + (131071 - 2) * d := by
  omega

/-- Specializing the filtration to the 21 degree-five Veronese rows closes
the original quintic candidate outright.  The best possible extracted layer
is the pure `V^5` layer; its forced `H^45` coefficient is still 3,431,185
degrees beyond the corresponding strict source cutoff.  Lexicographic
descent then repeats the same argument on every remaining layer. -/
theorem target_all_twenty_one_quintics_forced_power_overrun
    (b c d : Nat) (hdegree : b + c + d = 5) :
    60 * 180413 + 3431185 ≤
      (60 - 3 * b) * 81731 +
        (60 - (b + 2 * c + 3 * d) + c + 2 * d) * 180413 +
        131071 * b + (131071 - 1) * c + (131071 - 2) * d := by
  omega

theorem target_quintic_overrun_sharp_at_V5 :
    (60 - 3 * 5) * 81731 + (60 - 5) * 180413 -
      (60 * 180413 - 131071 * 5) = 3431185 := by
  norm_num

/-- The lower bound is sharp at the terminal red low-`E` shape
`(b,c,d)=(13,16,5)`. -/
theorem target_low_error_degree_overrun_sharp :
    (60 - 3 * 13) * 81731 +
        (60 - (13 + 2 * 16 + 3 * 5) + 16 + 2 * 5) * 180413 -
      (60 * 180413 - 131071 * 13 - (131071 - 1) * 16 -
        (131071 - 2) * 5) = 38697 := by
  norm_num

/-- The first next layer genuinely escapes the degree STOP.  Its forced
`H^18` leading coefficient is 255,837 degrees inside the source strip. -/
theorem target_error_degree_fourteen_first_green :
    (60 - 3 * 14) * 81731 +
        (60 - (14 + 2 * 17 + 3 * 4) + 17 + 2 * 4) * 180413 = 5981483 ∧
      60 * 180413 - 131071 * 14 - (131071 - 1) * 17 -
          (131071 - 2) * 4 = 6237320 ∧
      6237320 - 5981483 = 255837 ∧
      5981483 < 6237320 := by
  norm_num

/-- The original all-`H^60` estimate remains arithmetically valid when its
premise really is available.  Its best possible row is `V^60`, and it is
still 1,943,340 degrees over cutoff.  This theorem is deliberately labelled
conditional; the error filtration above explains why the premise fails for
general `b>0`. -/
theorem target_conditional_full_H60_overrun
    (b c d : Nat)
    (hdegreeLow : 2 ≤ b + c + d)
    (hdegreeHigh : b + c + d ≤ 82)
    (hslope : c + d ≤ 21) (hcurv : d ≤ 10) :
    60 * 180413 + 1943340 ≤
      60 * 81731 +
        (60 - (b + 2 * c + 3 * d) + c + 2 * d) * 180413 +
        131071 * b + (131071 - 1) * c + (131071 - 2) * d := by
  omega

end

end ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900

#print axioms ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900.normalTopChange_det
#print axioms ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900.leading_shape_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900.all_errors_force_multiplier_power
#print axioms ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900.target_low_error_degree_forced_power_overrun
#print axioms ProximityPrize.SubmissionLower.Full187NormalMonomialErrorFiltration6900.target_all_twenty_one_quintics_forced_power_overrun
