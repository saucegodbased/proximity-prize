import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Full187 width budget for the robust order-four covariant shell

This file contains arithmetic only.  It does not prove that the eight
covariants solve the target contact trellis.

Write `d` for the number of `Lambda`-degree units carried by a weighted
order-four monomial in `Lambda`, `V`, and `J1`; then `0 <= d <= 4` and the
remaining centered factors contribute at most `60-d` copies of `Q`.  Replacing
a centered factor by a raw active variable removes one degree-`2e` factor and
adds source weight at most `w`.  Since `2e>w`, the all-`Z` endpoint is worst.
-/

namespace ProximityPrize.SubmissionLower.Full187OrderFourCovariantWidth6900

set_option autoImplicit false

def w : Nat := 131071
def g : Nat := 180413
def e : Nat := 81731
def D : Nat := 10824780
def qDegree : Nat := 163462
def multiplierMax : Nat := 245192

theorem parameter_receipt :
    qDegree = 2 * e ∧ multiplierMax = 3 * e - 1 ∧
      qDegree - w = 32391 := by
  norm_num [qDegree, e, multiplierMax, w]

/-- Uniform raw-strip bound for every one of the eight source-legal
`Lambda,V,J1` order-four families after multiplication by `V^56`.  The
variable `y` counts centered factors replaced by raw active variables; using
weight `w` is conservative for `R`, whose literal weight is `w-1`. -/
theorem every_covariant_raw_strip_fits
    (h d y : Nat) (hh : h ≤ multiplierMax) (hd : d ≤ 4)
    (hy : y ≤ 60 - d) :
    h + d * g + (60 - d - y) * qDegree + y * w < D := by
  simp only [multiplierMax, g, qDegree, w, D] at hh ⊢
  omega

/-- The worst family is the `Lambda^4 V^56 Z^27` endpoint.  Even with a
full degree-`3e-1` multiplier it has more than seven hundred thousand units
of strict width margin. -/
theorem worst_endpoint_margin :
    multiplierMax + 4 * g + 56 * qDegree = 10120716 ∧
      10120716 < D ∧ D - 10120716 = 704064 := by
  norm_num [multiplierMax, g, qDegree, D]

/-- Degree-`<3e` is exactly enough for three independent Hermite coordinates
at every error location. -/
theorem three_error_jet_room : multiplierMax + 1 = 3 * e := by
  norm_num [multiplierMax, e]

/-- Multiplying a grade-seven order-four cycle by `V^56 Z^20`, then by any
terminal seed shift, respects all component and total-grade caps. -/
theorem robust_shell_shape_caps
    (active seedShift : Nat) (ha : active ≤ 4) (hk : seedShift ≤ 2620) :
    56 + active ≤ 60 ∧ 1 ≤ 21 ∧ 0 ≤ 10 ∧
      (56 + active) + (27 - active) + seedShift ≤ 2703 := by
  omega

#print axioms every_covariant_raw_strip_fits
#print axioms worst_endpoint_margin
#print axioms robust_shell_shape_caps

end ProximityPrize.SubmissionLower.Full187OrderFourCovariantWidth6900
