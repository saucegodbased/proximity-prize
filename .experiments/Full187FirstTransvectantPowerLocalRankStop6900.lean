import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Universal local formula obstruction for pure first-transvectant powers

The quintic carrier is a real source-family breakthrough, but the family

`H^a * L^(60-2k) * J_L^k`

cannot furnish a universal symbolic correction formula for all three
standard leading error syndromes.  At an error
node, every `a>0` row vanishes in contact weight zero.  The remaining `a=0`
rows are polynomials without constant term in the single passive linear form

`j=L*w-L'*d`.

The leading terms of `F0,F1,F2` are respectively a nonzero multiple of `d`,
of `j`, and of a form containing the independent curvature variable `s`.
Only `F1` lies in the one-coordinate image.  The two elementary
specializations below give a universal/formula-family obstruction and prove
that a symbolic producer valid for arbitrary residual jets needs mixed
`T2`/curvature carriers.  They do not alone exclude interpolation on the one
fixed finite target error set, where the residual triples are not arbitrary.
-/

namespace ProximityPrize.SubmissionLower.Full187FirstTransvectantPowerLocalRankStop6900

set_option autoImplicit false

variable {K : Type*} [Field K]

def leadingJ (L L' d w : K) : K := L * w - L' * d

def leadingF0 (L d : K) : K := L ^ 59 * d

def leadingF1 (L L' d w : K) : K := L ^ 58 * leadingJ L L' d w

def leadingF2 (L L' L'' d w s : K) : K :=
  L ^ 57 * (L ^ 2 * s - 2 * L * L' * w +
    (2 * (L') ^ 2 - L * L'') * d)

/-- Every positive error-locator power disappears in contact weight zero. -/
theorem positive_error_power_vanishes_at_error
    (a : Nat) (ha : 0 < a) : (0 : K) ^ a = 0 := by
  exact zero_pow (Nat.ne_of_gt ha)

/-- No polynomial in `j` with zero constant term can reproduce the leading
`F0` syndrome.  Set `(d,w)=(L,L')`; then `j=0` but `F0=L^60`. -/
theorem leadingF0_not_in_nonconstant_J_image
    (L L' : K) (hL : L ≠ 0) :
    ¬ ∃ P : K → K, P 0 = 0 ∧
        ∀ d w, P (leadingJ L L' d w) = leadingF0 L d := by
  rintro ⟨P, hP0, hP⟩
  have h := hP L L'
  have hj : leadingJ L L' L L' = 0 := by
    simp [leadingJ]
    ring
  rw [hj, hP0] at h
  have hpow : L ^ 60 ≠ 0 := pow_ne_zero _ hL
  apply hpow
  simpa [leadingF0, pow_succ] using h.symm

/-- The `F1` leading term is exactly in the one-coordinate image. -/
theorem leadingF1_in_J_image (L L' : K) :
    ∃ P : K → K, P 0 = 0 ∧
      ∀ d w, P (leadingJ L L' d w) = leadingF1 L L' d w := by
  refine ⟨fun x ↦ L ^ 58 * x, by simp, ?_⟩
  intro d w
  rfl

/-- No polynomial in `j` with zero constant term can reproduce `F2` either.
At `(d,w,s)=(0,0,1)`, `j=0` while `F2=L^59`. -/
theorem leadingF2_not_in_nonconstant_J_image
    (L L' L'' : K) (hL : L ≠ 0) :
    ¬ ∃ P : K → K, P 0 = 0 ∧
        ∀ d w s, P (leadingJ L L' d w) = leadingF2 L L' L'' d w s := by
  rintro ⟨P, hP0, hP⟩
  have h := hP 0 0 1
  have hj : leadingJ L L' 0 0 = 0 := by
    simp [leadingJ]
  rw [hj, hP0] at h
  have hpow : L ^ 59 ≠ 0 := pow_ne_zero _ hL
  apply hpow
  simpa [leadingF2] using h.symm

/-- Exact pure-seed post-error margins for the minimal legal powers. -/
theorem target_error_power_minimal_margins :
    16952 * 5 - 81731 * 1 = 3029 ∧
      16952 * 10 - 81731 * 2 = 6058 ∧
      16952 * 15 - 81731 * 3 = 9087 ∧
      16952 * 20 - 81731 * 4 = 12116 := by
  norm_num

/-- Powers below five cannot carry even one full error-locator factor. -/
theorem target_one_error_factor_requires_power_five
    (k : Nat) (hk : k ≤ 4) : 16952 * k ≤ 81731 := by
  omega

/-- Even the maximum literal slope power `k=21` cannot carry `H^5`. -/
theorem target_five_error_factors_exceed_slope_cap :
    16952 * 21 < 81731 * 5 := by
  norm_num

end ProximityPrize.SubmissionLower.Full187FirstTransvectantPowerLocalRankStop6900

#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantPowerLocalRankStop6900.leadingF0_not_in_nonconstant_J_image
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantPowerLocalRankStop6900.leadingF1_in_J_image
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantPowerLocalRankStop6900.leadingF2_not_in_nonconstant_J_image
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantPowerLocalRankStop6900.target_error_power_minimal_margins
