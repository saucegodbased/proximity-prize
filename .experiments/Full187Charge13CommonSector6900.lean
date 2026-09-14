import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
Exact arithmetic scaffold for the Full187 terminal charge-13 sector.

This file deliberately proves only source-window and exponent identities.
It does not identify the benchmark derivative variables `R,S` with the
local conics `C0,C1` appearing in discussion #530.
-/

namespace Full187Charge13CommonSector6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

def w : ℕ := 131071
def g : ℕ := 180413
def multiplicity : ℕ := 60
def D : ℕ := multiplicity * g
def activeCap : ℕ := 82
def slopeCap : ℕ := 21
def curvatureCap : ℕ := 10
def seedCap : ℕ := 2703
def passiveExponent : ℕ := seedCap - activeCap
def commonWidth : ℕ := 76979

def sourceWidth (y r s : ℕ) : ℕ :=
  D - w * y - (w - 1) * r - (w - 2) * s

theorem parameter_receipt :
    D = 10824780 ∧ passiveExponent = 2621 := by
  norm_num [D, multiplicity, g, passiveExponent, seedCap, activeCap]

/-- The eleven physical origins have shapes `(y,r,s,z)=(61,21-s,s,2621)`. -/
theorem charge13_origin_identities (s : ℕ) (hs : s ≤ curvatureCap) :
    activeCap - (slopeCap - s) - s = 61 ∧
    slopeCap - s = 11 + (curvatureCap - s) ∧
    passiveExponent = 2621 := by
  simp only [activeCap, slopeCap, curvatureCap, passiveExponent, seedCap] at *
  have hs21 : s ≤ 21 := by omega
  constructor
  · rw [Nat.sub_sub, Nat.sub_add_cancel hs21]
  · constructor
    · omega
    · norm_num

/-- The strict X-coefficient window of origin `s` is `[0,76979+s)`. -/
theorem charge13_source_width (s : ℕ) (hs : s ≤ curvatureCap) :
    sourceWidth 61 (slopeCap - s) s = commonWidth + s := by
  simp only [sourceWidth, D, multiplicity, g, w, slopeCap, curvatureCap,
    commonWidth] at *
  omega

/-- Each common X layer has every degree-ten binary `R/S` monomial once. -/
theorem common_binary_factorization (s : ℕ) (hs : s ≤ curvatureCap) :
    slopeCap - s = 11 + (curvatureCap - s) ∧
    (curvatureCap - s) + s = curvatureCap := by
  simp only [slopeCap, curvatureCap] at *
  omega

/-- At the fringe coefficient `X^(76979+j)`, origin `s` is present iff `j<s`. -/
theorem fringe_present_iff (j s : ℕ) :
    commonWidth + j < commonWidth + s ↔ j < s := by
  omega

/--
After factoring `S^(j+1)` from fringe layer `j`, the remaining exponents
form a degree-`9-j` binary sector.
-/
theorem fringe_binary_factorization (j s : ℕ) (hj : j < curvatureCap)
    (hjs : j < s) (hs : s ≤ curvatureCap) :
    s = (j + 1) + (s - (j + 1)) ∧
    (curvatureCap - s) + (s - (j + 1)) = curvatureCap - (j + 1) := by
  simp only [curvatureCap] at *
  omega

theorem common_rectangle_dimension :
    (∑ _s ∈ Finset.range 11, commonWidth) = 846769 := by
  norm_num [commonWidth, Finset.sum_range_succ]

theorem fringe_dimension :
    (∑ s ∈ Finset.range 11, s) = 55 := by
  norm_num [Finset.sum_range_succ]

theorem total_charge13_source_dimension :
    (∑ s ∈ Finset.range 11, (commonWidth + s)) = 846824 := by
  norm_num [commonWidth, Finset.sum_range_succ]

theorem dimension_split : 846769 + 55 = 846824 := by norm_num

/-- The three principal contact choices all have extra charge thirteen. -/
theorem principal_choice_charges :
    2 * 6 + 1 = 13 ∧ 2 * 5 + 3 = 13 ∧ 2 * 6 + 1 = 13 := by
  norm_num

/-- Their top target rows retain total grade 2703 for every `s≤10`. -/
theorem principal_target_grades (s : ℕ) (hs : s ≤ curvatureCap) :
    6 + (21 - s) + (s + 1) + 2675 = seedCap ∧
    5 + (21 - s) + (s + 3) + 2674 = seedCap ∧
    6 + (22 - s) + (s + 1) + 2674 = seedCap := by
  simp only [curvatureCap, seedCap] at *
  omega

end Full187Charge13CommonSector6900
