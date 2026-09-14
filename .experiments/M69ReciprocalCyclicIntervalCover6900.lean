import Lean.Elab.Tactic.Omega

/-!
# Arithmetic core of the m69 reciprocal-monomial interval cover

The exact m69 defect census has two alternating kinds of coefficient fringe.
For a reciprocal monomial `X^(-e)` with `2049 <= e <= 18414`, a high even
fringe and its second predecessor cover the whole cyclic coefficient domain.
For a low even fringe, the first and third (high) predecessors do so.

This file certifies only the interval arithmetic.  It does not identify an
arbitrary rational function with a monomial shift, nor prove simultaneous
allocation of predecessor freedoms.
-/

namespace ProximityPrize.SubmissionLower.M69ReciprocalCyclicIntervalCover6900

set_option autoImplicit false

def domainSize : Nat := 262144

/-- In the high-fringe parity, the original interval `[0,f)` overlaps the
suffix interval beginning at `N-2e`, so their union covers `[0,N)`. -/
theorem high_fringe_even_and_second_cover
    (e f k : Nat)
    (heLower : 2049 ≤ e) (heUpper : e ≤ 18414)
    (hfLower : 258802 ≤ f) :
    k < f ∨ domainSize - 2 * e ≤ k := by
  simp only [domainSize]
  omega

/-- In the low-fringe parity, let `g` be the high fringe of the first
predecessor.  The wrapped prefix of that predecessor ends at `g-e`, while the
third predecessor's suffix begins at `N-3e`; these intervals overlap. -/
theorem low_fringe_first_and_third_cover
    (e g k : Nat)
    (heLower : 2049 ≤ e) (heUpper : e ≤ 18414)
    (hgLower : 258802 ≤ g) :
    k < g - e ∨ domainSize - 3 * e ≤ k := by
  simp only [domainSize]
  omega

/-- The overlap inequality used in the high-parity cover. -/
theorem high_fringe_overlap
    (e f : Nat) (heLower : 2049 ≤ e) (heUpper : e ≤ 18414)
    (hfLower : 258802 ≤ f) :
    domainSize - 2 * e ≤ f := by
  simp only [domainSize]
  omega

/-- The overlap inequality used in the low-parity cover. -/
theorem low_fringe_overlap
    (e g : Nat) (heLower : 2049 ≤ e) (heUpper : e ≤ 18414)
    (hgLower : 258802 ≤ g) :
    domainSize - 3 * e ≤ g - e := by
  simp only [domainSize]
  omega

end ProximityPrize.SubmissionLower.M69ReciprocalCyclicIntervalCover6900

#print axioms ProximityPrize.SubmissionLower.M69ReciprocalCyclicIntervalCover6900.high_fringe_even_and_second_cover
#print axioms ProximityPrize.SubmissionLower.M69ReciprocalCyclicIntervalCover6900.low_fringe_first_and_third_cover
