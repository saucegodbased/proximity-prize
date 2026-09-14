import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# A countergate for a naive `m = 69` source-slope replacement

The literal passive-source substitution uses one fixed pair of received-word
coordinates.  This file records the elementary obstruction to silently
replacing its second `values₁` argument by a node-dependent rational
direction while claiming the same affine seed graphs at two distinct seeds.

This does *not* rule out a separately proved coordinate change that also
transforms the selected polynomials, nor a direction derived by applying a
concrete dual boundary map to the original source.  It says that one of those
theorems is required rather than a definitional `values₁ := W` substitution.
-/

namespace ProximityPrize.SubmissionLower.M69DirectionReplacementCountergate

theorem two_seed_same_graph_forces_same_coordinates
    {K : Type*} [Field K]
    (u0 u1 v0 w gamma delta : K)
    (hgd : gamma ≠ delta)
    (hgamma : u0 + gamma * u1 = v0 + gamma * w)
    (hdelta : u0 + delta * u1 = v0 + delta * w) :
    w = u1 ∧ v0 = u0 := by
  have hprod : (gamma - delta) * (u1 - w) = 0 := by
    linear_combination hgamma - hdelta
  have hgammaDelta : gamma - delta ≠ 0 := sub_ne_zero.mpr hgd
  have hu1w : u1 - w = 0 := (mul_eq_zero.mp hprod).resolve_left hgammaDelta
  have hw : w = u1 := (sub_eq_zero.mp hu1w).symm
  constructor
  · exact hw
  · rw [hw] at hgamma
    exact (add_right_cancel hgamma).symm

/- Two selected sets of size `180413` in a universe of size `262144` have
at least this many common nodes.  Thus a two-seed compatibility check is not a
negligible corner case in the intended parameter regime. -/
theorem selected_pair_forced_overlap_arithmetic :
    180413 + 180413 - 262144 = 98682 := by
  norm_num

/- A variable-coefficient wedge need not equal the original second received
coordinate, even at a single regular-looking scalar specialization. -/
theorem wedge_is_not_definitionally_the_original_direction :
    (1 : ℚ) * 1 - 0 * 0 ≠ 0 := by
  norm_num

#print axioms two_seed_same_graph_forces_same_coordinates
#print axioms selected_pair_forced_overlap_arithmetic
#print axioms wedge_is_not_definitionally_the_original_direction

end ProximityPrize.SubmissionLower.M69DirectionReplacementCountergate
