import Mathlib.Tactic

/-!
# Full187 contact-truncation width refund

This file corrects the old top-`Y` dependency-window warning.  A term in the
order-60 contact quotient survives only below contact weight 60.  Consequently
a surviving same-grade term from `Y^82` cannot be the formerly claimed
`f=81,h=1` edge: it must have `f <= 59` and hence move at least 23 powers into
the passive seed.  The corresponding raw-diagonal source width is then larger
than the complete 262144-node interpolation domain.

This is only the arithmetic gate for the pure/basic raw diagonal.  It does not
prove confluence for `E` or second-jet contact rows and does not prove THREE-RHS.
-/

namespace ProximityPrize.SubmissionLower.Full187ContactTruncationWidthRefund6900

set_option autoImplicit false
set_option Elab.async false

/-- Contact survival below order 60 forces the nonconstant active count to be
at most 59, even before using the nonnegative `E`/second-jet charges. -/
theorem active_count_le_59_of_contact_survival
    (f aE cS : ℕ) (hsurvive : f + 2 * aE + cS < 60) :
    f ≤ 59 := by
  omega

/-- A same-grade decomposition of the top active exponent 82 therefore moves
at least 23 units into the passive seed. -/
theorem top82_same_grade_seed_shift
    (f h aE cS : ℕ)
    (hgrade : f + h = 82)
    (hsurvive : f + 2 * aE + cS < 60) :
    23 ≤ h := by
  omega

/-- The worst surviving raw-diagonal predecessor is `f=59`; its literal
coefficient width is 3,091,591, leaving 2,829,447 degrees beyond the number of
nodes. -/
theorem top82_surviving_raw_diagonal_width
    (f : ℕ) (hf : f ≤ 59) :
    262144 < 60 * 180413 - 131071 * f := by
  omega

theorem top82_worst_width_receipt :
    60 * 180413 - 131071 * 59 = 3091591 ∧
    3091591 - 262144 = 2829447 ∧
    262144 < 3091591 := by
  norm_num

/-- Combined target gate for a surviving same-grade pure/basic term.  The
passive exponent stays well inside the target cap 2703, and the raw-diagonal
multiplier window is large enough for arbitrary data on all target nodes. -/
theorem top82_survival_forces_seed_and_interpolation_room
    (f h aE cS : ℕ)
    (hgrade : f + h = 82)
    (hsurvive : f + 2 * aE + cS < 60) :
    23 ≤ h ∧ h ≤ 2703 ∧
      262144 < 60 * 180413 - 131071 * f := by
  constructor
  · exact top82_same_grade_seed_shift f h aE cS hgrade hsurvive
  constructor
  · omega
  · exact top82_surviving_raw_diagonal_width f
      (active_count_le_59_of_contact_survival f aE cS hsurvive)

/-- The edge used by the old window warning is killed by truncation. -/
theorem old_f81_h1_edge_does_not_survive
    (aE cS : ℕ) : ¬(81 + 2 * aE + cS < 60) := by
  omega

/-! ## All 187 derivative channels

For a terminal active shape, `y+r+s=82` and `r+s<=21`.  Contact truncation
forces `f<=59`, so the active degree of every surviving raw-diagonal
predecessor is at most 80.  Two units of active-degree refund are already
enough to make its coefficient window longer than the full node domain.
-/

theorem terminal_active_predecessor_degree_le_80
    (r s f aE cS : ℕ)
    (hderivative : r + s ≤ 21)
    (hsurvive : f + 2 * aE + cS < 60) :
    f + r + s ≤ 80 := by
  omega

/-- Uniform literal width gate for every surviving raw-diagonal predecessor
of every one of the 187 terminal derivative shapes. -/
theorem terminal_187_raw_diagonal_width
    (r s f aE cS : ℕ)
    (hderivative : r + s ≤ 21)
    (hsurvive : f + 2 * aE + cS < 60) :
    262144 <
      60 * 180413 - 131071 * f - 131070 * r - 131069 * s := by
  omega

/-- Conservative endpoint receipt: replacing all three weights by `w` and
using active predecessor degree 80 still leaves 76,956 degrees of all-node
interpolation room. -/
theorem terminal_187_conservative_width_receipt :
    60 * 180413 - 131071 * 80 = 339100 ∧
    339100 - 262144 = 76956 ∧
    262144 < 339100 := by
  norm_num

/-- For a same-grade term, the source `Y` exponent decomposes as `f+h`.
Across the terminal derivative box this forces at least two passive-seed
steps. -/
theorem terminal_187_same_grade_seed_shift
    (y r s f h aE cS : ℕ)
    (hactive : y + r + s = 82)
    (hderivative : r + s ≤ 21)
    (hgrade : f + h = y)
    (hsurvive : f + 2 * aE + cS < 60) :
    2 ≤ h := by
  omega

/-- The same-grade raw-diagonal replacement preserves the combined active and
passive seed cap exactly. -/
theorem terminal_same_grade_seed_cap_preserved
    (y r s z f h : ℕ)
    (hgrade : f + h = y)
    (hseed : y + r + s + z ≤ 2703) :
    f + r + s + (z + h) ≤ 2703 := by
  omega

/-! A larger raw-diagonal sector also survives the second-jet choice.  When
`aE=0` and `2*cS<=r`, the contact row

`(T,R,S)=(f+cS, f-cS+r, s+cS)`

is the unit diagonal of source shape
`(f+cS, r-2*cS, s+cS)`.  The weighted degree charge is unchanged exactly.
-/

theorem second_jet_raw_diagonal_weight_identity
    (f r s cS : ℕ) (hdiagonal : 2 * cS ≤ r) :
    131071 * (f + cS) + 131070 * (r - 2 * cS) +
        131069 * (s + cS) =
      131071 * f + 131070 * r + 131069 * s := by
  omega

theorem second_jet_raw_diagonal_active_degree
    (f r s cS : ℕ) (hdiagonal : 2 * cS ≤ r) :
    (f + cS) + (r - 2 * cS) + (s + cS) = f + r + s := by
  omega

theorem second_jet_raw_diagonal_derivative_cap
    (r s cS : ℕ)
    (hdiagonal : 2 * cS ≤ r)
    (hderivative : r + s ≤ 21) :
    (r - 2 * cS) + (s + cS) ≤ 21 := by
  omega

/-- Whenever the inverse source also obeys the curvature cap, this entire
second-jet diagonal sector inherits the uniform all-node width gate. -/
theorem second_jet_raw_diagonal_width
    (f r s cS : ℕ)
    (hdiagonal : 2 * cS ≤ r)
    (hderivative : r + s ≤ 21)
    (hsurvive : f + cS < 60) :
    262144 <
      60 * 180413 - 131071 * (f + cS) -
        131070 * (r - 2 * cS) - 131069 * (s + cS) := by
  omega

/-! ## The unique unreduced coefficient-product cliff

To transport a top coefficient of degree `<topWidth` using an arbitrary
all-node interpolant of degree `<262144`, the largest product degree is
`topWidth+262142`.  A passive shift `h` refunds `131071*h` degrees.  Thus
every `h>=3` transport fits, while `h=2` reaches the strict cutoff exactly.
This is only a STOP for retaining the unreduced product.  The `h=2` case has
contact weight 59 and hence Hermite depth one; its node values may instead be
reduced modulo the all-node locator to degree `<262144`, which fits the
predecessor window proved above.
-/

theorem generic_product_fits_of_three_seed_steps
    (topWidth h : ℕ) (htop : 0 < topWidth) (hh : 3 ≤ h) :
    (topWidth - 1) + (262144 - 1) < topWidth + 131071 * h := by
  omega

theorem generic_product_two_seed_exact_cliff
    (topWidth : ℕ) (htop : 0 < topWidth) :
    (topWidth - 1) + (262144 - 1) = topWidth + 2 * 131071 := by
  omega

/-- Combining terminal active degree, derivative cap, same-grade transport,
and contact survival shows that `h=2` is possible only on the eleven-shape
outer derivative boundary.  Survival also forces the pure all-`TR` contact
choice `aE=cS=0`. -/
theorem two_seed_cliff_classification
    (y r s f h aE cS : ℕ)
    (hactive : y + r + s = 82)
    (hderivative : r + s ≤ 21)
    (hgrade : f + h = y)
    (hsurvive : f + 2 * aE + cS < 60)
    (hh : h ≤ 2) :
    h = 2 ∧ y = 61 ∧ f = 59 ∧ r + s = 21 ∧
      aE = 0 ∧ cS = 0 := by
  omega

theorem outer_boundary_shape_parameterization
    (r s : ℕ) (hboundary : r + s = 21) (hs : s ≤ 10) :
    r = 21 - s ∧ s < 11 := by
  omega

/-- The apparent two-seed cliff is an actual linear GREEN after reduction:
its contact row has Hermite depth one and every derivative-boundary
predecessor has more than one full node domain of coefficient width. -/
theorem two_seed_cliff_depth_one_reduction_fits
    (r s : ℕ) (hderivative : r + s ≤ 21) :
    60 - 59 = 1 ∧
      262144 <
        60 * 180413 - 131071 * 59 - 131070 * r - 131069 * s := by
  constructor
  · norm_num
  · exact terminal_187_raw_diagonal_width r s 59 0 0 hderivative (by omega)

#print axioms active_count_le_59_of_contact_survival
#print axioms top82_same_grade_seed_shift
#print axioms top82_surviving_raw_diagonal_width
#print axioms top82_survival_forces_seed_and_interpolation_room
#print axioms old_f81_h1_edge_does_not_survive
#print axioms terminal_active_predecessor_degree_le_80
#print axioms terminal_187_raw_diagonal_width
#print axioms terminal_187_conservative_width_receipt
#print axioms terminal_187_same_grade_seed_shift
#print axioms terminal_same_grade_seed_cap_preserved
#print axioms second_jet_raw_diagonal_weight_identity
#print axioms second_jet_raw_diagonal_active_degree
#print axioms second_jet_raw_diagonal_derivative_cap
#print axioms second_jet_raw_diagonal_width
#print axioms generic_product_fits_of_three_seed_steps
#print axioms generic_product_two_seed_exact_cliff
#print axioms two_seed_cliff_classification
#print axioms outer_boundary_shape_parameterization
#print axioms two_seed_cliff_depth_one_reduction_fits

end ProximityPrize.SubmissionLower.Full187ContactTruncationWidthRefund6900
