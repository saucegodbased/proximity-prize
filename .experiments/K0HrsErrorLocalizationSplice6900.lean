import HrsGlobalDescendingMomentClosure6900

/-!
# Singleton error localization from the global reverse-Hasse closure

This is the exact last step needed after the literal PC elimination has
produced all multiplier equations.  A strict-window polynomial which
vanishes at every other error isolates the chosen error at every reversed
Hasse coordinate; its nonzero value cancels over the field.

For lower 6900 the error set has at most `81731` elements and `w = 131071`,
so the complement locator has degree at most `81730 < w`.  Constructing that
locator is elementary.  Producing `hsource` from the complete m47 contact
system is the substantive open recurrence theorem.
-/

namespace ProximityPrize.SubmissionLower.K0HrsErrorLocalizationSplice6900

open scoped BigOperators
open Polynomial
open HrsU0PoleCancellation6900
open HrsGlobalSelectedErrorTestInterface6900
open HrsGlobalDescendingMomentClosure6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- All legal global multiplier equations localize one chosen error.  This
specializes the selected-set theorem to a singleton and cancels the
nonzero complement-locator value. -/
theorem singleton_reversedHasse_eq_zero_of_all_multiplier_equations
    (nodes : I -> K) (depth w : Nat) (g : I -> K[X])
    (U : K[X]) (selected : I) (i : Nat) (hi : i < depth)
    (hU : U.natDegree < w)
    (hselected : U.eval (nodes selected) ≠ 0)
    (hroot : forall x, x ≠ selected -> U.eval (nodes x) = 0)
    (hsource : forall k, k < depth -> forall V : K[X],
      V.natDegree < w ->
        (∑ x, reversedHasse (nodes x) depth (V * g x) k) = 0) :
    reversedHasse (nodes selected) depth (g selected) i = 0 := by
  have hlocalized := selected_sum_eq_zero_of_all_source_equations
    nodes depth w U g i hi ({selected} : Finset I) hU hsource
      (fun x hx => hroot x (by simpa using hx))
  have hproduct : U.eval (nodes selected) *
      reversedHasse (nodes selected) depth (g selected) i = 0 := by
    simpa using hlocalized
  exact (mul_eq_zero.mp hproduct).resolve_left hselected

#print axioms singleton_reversedHasse_eq_zero_of_all_multiplier_equations

end

end ProximityPrize.SubmissionLower.K0HrsErrorLocalizationSplice6900
