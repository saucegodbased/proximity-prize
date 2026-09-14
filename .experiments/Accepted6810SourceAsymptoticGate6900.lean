import Mathlib.Tactic

/-!
Kernel-checked asymptotic RED gate for retargeting the accepted 6810 P4 source
from agreement 181294 to 180413.  There is no finite enumeration here.

For `D=m*A`, `w=131071`, `n=262144`, and `s/m -> beta`, the coefficient
of the large total cap has the leading term

  w*m^3/6 * (alpha^3 - (alpha-beta)^3), alpha=A/w.

The contact-rank leading term changes formula at beta=1/2.  The two theorems
below certify negativity in both chambers at A=180413.
-/

namespace ProximityPrize.Experiments.Accepted6810SourceAsymptoticGate6900

def lowFactor (beta : ℚ) : ℚ :=
  (-393217) * beta ^ 2 + 245193 * beta +
    3 * ((180413 : ℚ) ^ 2 / 131071 - 262144)

/-- For `0 < beta <= 1/2`, the leading nullity slope is the positive factor
`beta/6` times `lowFactor beta`.  In fact the factor is negative on all Q. -/
theorem low_chamber_strictly_negative (beta : ℚ) : lowFactor beta < 0 := by
  have hs : 0 ≤ (beta - (245193 : ℚ) / 786434) ^ 2 := sq_nonneg _
  unfold lowFactor
  nlinarith

def highSlope (beta : ℚ) : ℚ :=
  (131071 / 6 : ℚ) *
      (((180413 / 131071 : ℚ) ^ 3) -
        ((180413 / 131071 : ℚ) - beta) ^ 3) -
    262144 * (beta / 4 + 1 / 24)

/-- In the `1/2 <= beta < 1` chamber the exact leading rank is
`n*m^3*(beta/4+1/24)`.  The leading nullity slope is already negative at
`1/2` and strictly decreases across this whole chamber. -/
theorem high_chamber_strictly_negative
    (beta : ℚ) (hlo : (1 : ℚ) / 2 ≤ beta) (hhi : beta ≤ 1) :
    highSlope beta < 0 := by
  let x : ℚ := beta - 1 / 2
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 1 / 2 := by dsimp [x]; linarith
  have hsq : 0 ≤ x ^ 2 := sq_nonneg _
  have hcubic : x ^ 3 ≤ (1 / 2 : ℚ) * x ^ 2 := by
    have hp := mul_nonneg hsq (sub_nonneg.mpr hx1)
    nlinarith
  unfold highSlope
  dsimp [x] at hx0 hx1 hsq hcubic
  nlinarith

theorem full187_arithmetic_go :
    162963415163901 - 262144 * 621656057 = 9757693 := by
  norm_num

end ProximityPrize.Experiments.Accepted6810SourceAsymptoticGate6900

#print axioms ProximityPrize.Experiments.Accepted6810SourceAsymptoticGate6900.low_chamber_strictly_negative
#print axioms ProximityPrize.Experiments.Accepted6810SourceAsymptoticGate6900.high_chamber_strictly_negative
#print axioms ProximityPrize.Experiments.Accepted6810SourceAsymptoticGate6900.full187_arithmetic_go
