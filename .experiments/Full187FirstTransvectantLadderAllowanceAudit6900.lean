import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact allowance classification for the Full187 first-transvectant ladder

This file closes the arithmetic side of the pure ladder

`H^a * L^(60-2k) * J_L^k`, `0 <= k <= 21`.

For a shape `Y^y R^r Z^z`, `y+r+z=k`, its strict source margin is

`49343*k - 81731*a - 32391*z`.

The pure seed term `z=k` is always the narrowest, so whole-carrier legality
is equivalent to `81731*a < 16952*k`.  The resulting bands are exact:

* `k=1..4`: `a=0`;
* `k=5..9`: `a<=1`;
* `k=10..14`: `a<=2`;
* `k=15..19`: `a<=3`;
* `k=20..21`: `a<=4`.

Combined with `Full187FirstTransvectantPowerLocalRankStop6900`, this gives a
STOP only for a **universal symbolic formula** in the single coordinate
`J=L*w-L'*d`: positive `a` vanishes in weight zero, while legal `a=0` has
`k>0`, so a universal formula has zero constant term in `J`.  This does not
by itself stop interpolation on the actual finite error jets, where
X-dependent multipliers and translations are available.  Moreover the
correction rows must have zero agreement boundary, which can exclude the
`k=1` row that realizes `F1`.  No finite error-contact STOP is claimed here.
-/

namespace ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900

set_option autoImplicit false

/-- Strict legality of every seed layer of a fixed `(k,a)` ladder member.
The other two exponents `y,r` only improve the margin once
`y+r+z=k`. -/
def AllSeedLayersLegal (k a : Nat) : Prop :=
  ∀ z, z ≤ k → 81731 * a + 32391 * z < 49343 * k

/-- The pure seed layer is the exact worst layer. -/
theorem allSeedLayersLegal_iff_pureSeed (k a : Nat) :
    AllSeedLayersLegal k a ↔ 81731 * a < 16952 * k := by
  constructor
  · intro h
    have hk := h k (by rfl)
    omega
  · intro h z hz
    omega

/-- Direct coefficient/cutoff ledger before specializing `z`. -/
theorem target_shape_margin_identity
    (k a y r z : Nat) (hk : k ≤ 21) (hsum : y + r + z = k)
    (hlegal : 81731 * a + 32391 * z < 49343 * k) :
    81731 * a + (60 - 2 * k) * 180413 +
          y * (180413 - 1) + r * 180413 +
          z * (180413 + 2 * 81731 - 1) +
          (49343 * k - (81731 * a + 32391 * z)) =
      60 * 180413 - 131071 * y - (131071 - 1) * r := by
  have hk2 : 2 * k ≤ 60 := by
    omega
  norm_num at hsum hlegal ⊢
  omega

/-- The constant ladder member `L^60` is never strict-source legal. -/
theorem k_zero_never_legal (a : Nat) :
    ¬ AllSeedLayersLegal 0 a := by
  rw [allSeedLayersLegal_iff_pureSeed]
  omega

/-- Consequently every legal `a=0` member has positive `J` power and hence
zero constant term as a polynomial in `J`. -/
theorem positive_k_of_legal (k a : Nat)
    (h : AllSeedLayersLegal k a) : 0 < k := by
  by_contra hk
  have : k = 0 := by omega
  subst k
  exact k_zero_never_legal a h

theorem allowance_band_1_to_4
    (k a : Nat) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    AllSeedLayersLegal k a ↔ a = 0 := by
  rw [allSeedLayersLegal_iff_pureSeed]
  constructor
  · intro h
    omega
  · rintro rfl
    omega

theorem allowance_band_5_to_9
    (k a : Nat) (hk5 : 5 ≤ k) (hk9 : k ≤ 9) :
    AllSeedLayersLegal k a ↔ a ≤ 1 := by
  rw [allSeedLayersLegal_iff_pureSeed]
  omega

theorem allowance_band_10_to_14
    (k a : Nat) (hk10 : 10 ≤ k) (hk14 : k ≤ 14) :
    AllSeedLayersLegal k a ↔ a ≤ 2 := by
  rw [allSeedLayersLegal_iff_pureSeed]
  omega

theorem allowance_band_15_to_19
    (k a : Nat) (hk15 : 15 ≤ k) (hk19 : k ≤ 19) :
    AllSeedLayersLegal k a ↔ a ≤ 3 := by
  rw [allSeedLayersLegal_iff_pureSeed]
  omega

theorem allowance_band_20_to_21
    (k a : Nat) (hk20 : 20 ≤ k) (hk21 : k ≤ 21) :
    AllSeedLayersLegal k a ↔ a ≤ 4 := by
  rw [allSeedLayersLegal_iff_pureSeed]
  omega

/-- Uniform consequence: the entire legal slope-capped ladder has
`a<=4`. -/
theorem allowed_error_power_le_four
    (k a : Nat) (hk : k ≤ 21) (h : AllSeedLayersLegal k a) :
    a ≤ 4 := by
  rw [allSeedLayersLegal_iff_pureSeed] at h
  omega

/-- Exact positive margins at the first member of each positive-error-power
band.  These agree with the independently checked quintic receipt. -/
theorem first_legal_positive_error_power_margins :
    16952 * 5 - 81731 = 3029 ∧
      16952 * 10 - 2 * 81731 = 6058 ∧
      16952 * 15 - 3 * 81731 = 9087 ∧
      16952 * 20 - 4 * 81731 = 12116 := by
  norm_num

/-! ## Quantitative local error-image bound

The following theorem strengthens the two universal symbolic exclusions. If
a linear combination of `(F0,F1,F2)` agrees for **all** symbolic `(d,w,s)`
with a nonconstant function of the single coordinate `J`, its `F0` and `F2`
coefficients vanish.  Thus this universal-formula intersection is contained
in the one-dimensional `F1` line.  It is deliberately not a theorem about
agreement on only the actual finite error jets. -/

section LocalErrorRank

variable {K : Type*} [Field K]

def localJ (L L1 d w : K) : K := L * w - L1 * d

def localF0 (L d : K) : K := L ^ 59 * d

def localF1 (L L1 d w : K) : K := L ^ 58 * localJ L L1 d w

def localF2 (L L1 L2 d w s : K) : K :=
  L ^ 57 * (L ^ 2 * s - 2 * L * L1 * w +
    (2 * L1 ^ 2 - L * L2) * d)

theorem standard_syndrome_span_inter_singleJ_has_rank_at_most_one
    (L L1 L2 alpha beta gamma : K) (hL : L ≠ 0)
    (P : K → K) (hP0 : P 0 = 0)
    (hP : ∀ d w s,
      P (localJ L L1 d w) =
        alpha * localF0 L d + beta * localF1 L L1 d w +
          gamma * localF2 L L1 L2 d w s) :
    alpha = 0 ∧ gamma = 0 := by
  have hs := hP 0 0 1
  have hgammaMul : gamma * localF2 L L1 L2 0 0 1 = 0 := by
    simpa [localJ, localF0, localF1, hP0] using hs.symm
  have hF2ne : localF2 L L1 L2 0 0 1 ≠ 0 := by
    unfold localF2
    simp only [mul_one, mul_zero, sub_zero, add_zero]
    exact mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hL)
  have hgamma : gamma = 0 := by
    exact (mul_eq_zero.mp hgammaMul).resolve_right hF2ne
  have ha := hP L L1 0
  have hj : localJ L L1 L L1 = 0 := by
    unfold localJ
    ring
  have halphaMul : alpha * localF0 L L = 0 := by
    rw [hj, hP0] at ha
    simpa [localF1, hj, hgamma] using ha.symm
  have hF0ne : localF0 L L ≠ 0 := by
    unfold localF0
    exact mul_ne_zero (pow_ne_zero _ hL) hL
  have halpha : alpha = 0 := by
    exact (mul_eq_zero.mp halphaMul).resolve_right hF0ne
  exact ⟨halpha, hgamma⟩

end LocalErrorRank

end ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900

#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allSeedLayersLegal_iff_pureSeed
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.target_shape_margin_identity
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allowance_band_1_to_4
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allowance_band_5_to_9
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allowance_band_10_to_14
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allowance_band_15_to_19
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allowance_band_20_to_21
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.allowed_error_power_le_four
#print axioms ProximityPrize.SubmissionLower.Full187FirstTransvectantLadderAllowanceAudit6900.standard_syndrome_span_inter_singleJ_has_rank_at_most_one
