import GlobalO2PartialLocatorFourthNormal6900
import Mathlib.Tactic.NormNum

/-!
# Exact-G direct HRS carrier obstruction for the m=47 profile

The partial-locator fourth normal is the canonical single carrier which has
complete agreement contact and exposes the bad direction quotient.  Its
top source term already has weighted degree `47*g-1`.  Consequently even a
linear nonconstant X multiplier reaches the strict cutoff.  In particular,
neither a boundary-killing `(X-xi)` factor nor an error-complement locator can
be applied to this carrier inside the literal source.

This is a precise obstruction only to the direct single-carrier HRS splice.
It does not rule out a coupled X/seed recurrence using lower-weight source
terms.
-/

namespace ProximityPrize.SubmissionLower.K0ExactGDirectHrsCarrierObstruction6900

open Polynomial
open ProximityPrize.SubmissionLower.GlobalO2PartialLocatorFourthNormal6900

set_option autoImplicit false
set_option Elab.async false

noncomputable section

def targetN : Nat := 262144
def targetW : Nat := 131071
def targetM : Nat := 47
def targetGMin : Nat := 180413
def targetErrors : Nat := targetN - targetGMin

/-- Exact top weighted degree of the m=47 partial-locator fourth normal at
an arbitrary exact agreement cardinality. -/
theorem partial_locator_fourth_normal_top_weight_47
    (g : Nat) (hg : targetW + 1 <= g) :
    (targetM - 1) * (targetW + 1) +
          targetM * (g - (targetW + 1)) + targetW =
      targetM * g - 1 := by
  norm_num [targetM, targetW] at hg ⊢
  omega

/-- No positive-degree free X multiplier fits above that top term in the
strict `D=47*g` source box. -/
theorem no_positive_X_multiplier_above_partial_locator
    (g d : Nat) (hg : 1 <= g) (hd : 1 <= d) :
    ¬ (targetM * g - 1 + d < targetM * g) := by
  norm_num [targetM] at hg hd ⊢
  omega

/-- Already the one linear factor needed to kill the generic boundary value
hits the cutoff exactly. -/
theorem boundary_killing_linear_factor_hits_cutoff
    (g : Nat) (hg : 1 <= g) :
    targetM * g - 1 + 1 = targetM * g := by
  norm_num [targetM] at hg ⊢
  omega

/-- At the lowest exact-G stratum, a complement locator for one selected
error has degree 81730.  Applying it to the agreement-killing carrier
overshoots the source cutoff by 81729, despite the locator itself having
degree below the Reed--Solomon width. -/
theorem minimum_stratum_complement_locator_overshoots :
    targetErrors = 81731 ∧
    targetErrors - 1 = 81730 ∧
    targetErrors - 1 < targetW ∧
    targetM * targetGMin - 1 + (targetErrors - 1) =
      targetM * targetGMin + 81729 := by
  norm_num [targetErrors, targetN, targetGMin, targetW, targetM]

/-- The obstruction is caused by the agreement prefactor, not by the raw
m=47 box: a top active-degree raw strip still has 90867 X coefficients and
can hold an error locator (even with one additional boundary root). -/
theorem minimum_stratum_raw_terminal_window_can_hold_error_locator :
    targetM * targetGMin - targetW * 64 = 90867 ∧
      targetErrors = 81731 ∧
      targetErrors < targetM * targetGMin - targetW * 64 := by
  norm_num [targetM, targetGMin, targetW, targetErrors, targetN]

variable {K : Type*} [Field K]

/-- Every standard partial-locator osculating packet has free X window at
most its contact gain `d <= m=47`.  At the minimum exact-G stratum no such
multiplier can isolate one error from the other 81730 distinct errors. -/
theorem no_m47_partial_packet_multiplier_isolates_one_error
    (otherErrors : Finset K) (hcard : otherErrors.card = 81730)
    (d : Nat) (hd : d <= targetM)
    (p : K[X]) (hpdegree : p.natDegree < d)
    (hzero : forall x, x ∈ otherErrors -> p.eval x = 0)
    (selectedError : K) :
    p.eval selectedError = 0 := by
  have hpdegree' : p.natDegree < otherErrors.card := by
    norm_num [targetM] at hd
    omega
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      p otherErrors hzero hpdegree'
  simp [hpzero]

/-- Retained badness yields one nonzero *polynomial* quotient `T`, with the
full target degree window.  There is no need to replace a general
nonconstant `T` by a scalar first-Newton coefficient when working over
`K(X)`. -/
theorem exists_nonzero_anchor_quotient_with_degree
    {H G : Finset K} {u : K -> K} {w g : Nat} {Q q : K[X]}
    (hHG : H ⊆ G) (hHcard : H.card = w + 1)
    (hwg : w < g)
    (hbad : RetainedBadOn G u w)
    (hq : q.natDegree <= w) (hQdegree : Q.natDegree < g)
    (hQ : forall x, x ∈ G -> Q.eval x = u x)
    (hqH : forall x, x ∈ H -> q.eval x = u x) :
    exists T : K[X], T ≠ 0 ∧ Q - q = locator H * T ∧
      T.natDegree < g - (w + 1) := by
  obtain ⟨T, hT, hfactor⟩ :=
    exists_nonzero_anchor_quotient_of_retainedBad
      hHG hbad hq hQ hqH
  refine ⟨T, hT, hfactor, ?_⟩
  have hqg : q.natDegree < g := lt_of_le_of_lt hq hwg
  have hsubdegree : (Q - q).natDegree < g :=
    (Polynomial.natDegree_sub_le Q q).trans_lt (max_lt hQdegree hqg)
  rw [hfactor, Polynomial.natDegree_mul (locator_monic H).ne_zero hT,
    locator_natDegree, hHcard] at hsubdegree
  omega

#print axioms partial_locator_fourth_normal_top_weight_47
#print axioms no_positive_X_multiplier_above_partial_locator
#print axioms minimum_stratum_complement_locator_overshoots
#print axioms minimum_stratum_raw_terminal_window_can_hold_error_locator
#print axioms no_m47_partial_packet_multiplier_isolates_one_error
#print axioms exists_nonzero_anchor_quotient_with_degree

end

end ProximityPrize.SubmissionLower.K0ExactGDirectHrsCarrierObstruction6900
