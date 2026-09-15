import K0SRTinyContactCore6900
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact cap stop for the affine-mismatch geometric recurrence

Let `H` be the agreement locator and let

`J = Y - U0(X) - U1(X) * W`

be the received-line residual obtained from the full nodal interpolants.
At an agreement both `H` and `J` have contact order one, while at an error
`H` is a unit and `J` has contact order one.  The canonical geometric rung

`H^(44-t) * J^t * B`

therefore has agreement order 44 and error order `t`.

This file checks the first target obstruction to using those rungs as the
four-dimensional low-head annihilator.  In an admissible worst case the
full received interpolant `U0` has degree `n-1=262143`.  Projecting the rung
to its active-zero branch gives the unique term

`(+ or -) H^(44-t) * U0^t * B`.

For the three active boundary seeds this term leaves the literal K0 source
between rungs five and six; for the passive seed it leaves between rungs six
and seven.  Thus this geometric recurrence cannot reach error order 44.
-/

namespace ProximityPrize.SubmissionLower.K0AffineMismatchGeometricRecurrenceStop6900

open K0SRTinyContactCore6900
open Polynomial

set_option autoImplicit false
set_option Elab.async false

/-- Largest X degree in the active-zero branch when `deg H=g` and the full
received interpolant has degree `n-1`. -/
def affineMismatchRungX (t : Nat) : Nat :=
  (44 - t) * 180413 + t * (262144 - 1)

theorem affineMismatchRungX_five :
    affineMismatchRungX 5 = 8346822 := by
  norm_num [affineMismatchRungX]

theorem affineMismatchRungX_six :
    affineMismatchRungX 6 = 8428552 := by
  norm_num [affineMismatchRungX]

theorem affineMismatchRungX_seven :
    affineMismatchRungX 7 = 8510282 := by
  norm_num [affineMismatchRungX]

/-- The order ledger underlying the geometric recurrence. -/
theorem agreement_order_of_geometric_rung (t : Nat) (ht : t <= 44) :
    (44 - t) + t = 44 := by
  omega

/-- Setting the active residual variable to zero isolates the pure-`U0`
branch.  At rung six its coefficient is nonzero with no combinatorial
factor that could disappear in the target characteristic. -/
theorem activeZero_branch_rung_six
    {S : Type*} [CommRing S] (H U B : S) :
    H ^ 38 * (0 - U) ^ 6 * B = H ^ 38 * U ^ 6 * B := by
  ring

/-- The same branch at rung seven has coefficient `-1`. -/
theorem activeZero_branch_rung_seven
    {S : Type*} [CommRing S] (H U B : S) :
    H ^ 37 * (0 - U) ^ 7 * B = -(H ^ 37 * U ^ 7 * B) := by
  ring

/-- With monic extremal interpolants, the bad branch really has the stated
degree; it is not merely an upper-bound artifact. -/
theorem activeZero_branch_rung_six_natDegree
    {K : Type*} [CommRing K] (H U : K[X])
    (hH : H.Monic) (hU : U.Monic)
    (hHdeg : H.natDegree = 180413)
    (hUdeg : U.natDegree = 262143) :
    (H ^ 38 * U ^ 6).natDegree = affineMismatchRungX 6 := by
  calc
    (H ^ 38 * U ^ 6).natDegree =
        (H ^ 38).natDegree + (U ^ 6).natDegree :=
      (hH.pow 38).natDegree_mul (hU.pow 6)
    _ = affineMismatchRungX 6 := by
      rw [hH.natDegree_pow, hU.natDegree_pow, hHdeg, hUdeg]
      norm_num [affineMismatchRungX]

theorem activeZero_branch_rung_seven_natDegree
    {K : Type*} [CommRing K] (H U : K[X])
    (hH : H.Monic) (hU : U.Monic)
    (hHdeg : H.natDegree = 180413)
    (hUdeg : U.natDegree = 262143) :
    (H ^ 37 * U ^ 7).natDegree = affineMismatchRungX 7 := by
  calc
    (H ^ 37 * U ^ 7).natDegree =
        (H ^ 37).natDegree + (U ^ 7).natDegree :=
      (hH.pow 37).natDegree_mul (hU.pow 7)
    _ = affineMismatchRungX 7 := by
      rw [hH.natDegree_pow, hU.natDegree_pow, hHdeg, hUdeg]
      norm_num [affineMismatchRungX]

/-! ## The exact strict-cutoff cliff

The coordinate order below is `(X,S,Y,R,Z)`.  `rawShapeLegal` includes every
literal K0 cap, not merely the weighted X inequality.
-/

/-- At rung five the projected `Y`, `R`, and `S` branches are still legal,
with respective strict-cutoff slacks 1518, 1519, and 1520. -/
theorem target_active_branches_rung_five_legal :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        (affineMismatchRungX 5) 0 1 0 0 /\
      rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        (affineMismatchRungX 5) 0 0 1 0 /\
      rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        (affineMismatchRungX 5) 1 0 0 0 := by
  norm_num [rawShapeLegal, affineMismatchRungX]

/-- The next recurrence equation is impossible in the same family: at rung
six the unique active-zero branch is over the cutoff by 80,212 (`Y`),
80,211 (`R`), or 80,210 (`S`). -/
theorem target_active_branches_rung_six_illegal :
    Not (rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        (affineMismatchRungX 6) 0 1 0 0) /\
      Not (rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        (affineMismatchRungX 6) 0 0 1 0) /\
      Not (rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        (affineMismatchRungX 6) 1 0 0 0) := by
  norm_num [rawShapeLegal, affineMismatchRungX]

/-- The passive `W` branch survives one rung longer. -/
theorem target_passive_branch_rung_six_legal :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      (affineMismatchRungX 6) 0 0 0 1 := by
  norm_num [rawShapeLegal, affineMismatchRungX]

/-- At rung seven even the weight-zero passive branch is over the strict X
cutoff, by 30,871. -/
theorem target_passive_branch_rung_seven_illegal :
    Not (rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      (affineMismatchRungX 7) 0 0 0 1) := by
  norm_num [rawShapeLegal, affineMismatchRungX]

/-- Exact arithmetic form of all four cliff margins.  Positive numbers on
the right are overages, not heuristic dimension losses. -/
theorem target_affine_mismatch_cliff_margins :
    affineMismatchRungX 6 + 131071 - 47 * 180413 = 80212 /\
      affineMismatchRungX 6 + 131070 - 47 * 180413 = 80211 /\
      affineMismatchRungX 6 + 131069 - 47 * 180413 = 80210 /\
      affineMismatchRungX 7 - 47 * 180413 = 30871 := by
  norm_num [affineMismatchRungX]

#print axioms agreement_order_of_geometric_rung
#print axioms activeZero_branch_rung_six
#print axioms activeZero_branch_rung_seven
#print axioms activeZero_branch_rung_six_natDegree
#print axioms activeZero_branch_rung_seven_natDegree
#print axioms target_active_branches_rung_five_legal
#print axioms target_active_branches_rung_six_illegal
#print axioms target_passive_branch_rung_six_legal
#print axioms target_passive_branch_rung_seven_illegal
#print axioms target_affine_mismatch_cliff_margins

end ProximityPrize.SubmissionLower.K0AffineMismatchGeometricRecurrenceStop6900
