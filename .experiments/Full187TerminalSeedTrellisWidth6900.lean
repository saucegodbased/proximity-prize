import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Literal Full187 widths for the terminal three-carrier seed trellis

This file contains only the exact target arithmetic.  The associated source
identity is

  V^58 Z^23 *
    (c Y^2 + (B0-c Q-2 A Lambda Xi') Y Z
      + A Lambda Xi R Z - B0 Q Z^2),

where `deg Q = 2e = 163462`.  Each theorem below checks one complete raw
`Y` strip, including its own weighted source width.  Thus the calculation
does not treat a centered expression as though its summands shared a box.
-/

namespace ProximityPrize.SubmissionLower.Full187TerminalSeedTrellisWidth6900

set_option autoImplicit false
set_option maxHeartbeats 400000

def N : Nat := 262144
def w : Nat := 131071
def g : Nat := 180413
def e : Nat := 81731
def m : Nat := 60
def D : Nat := 10824780
def activeCap : Nat := 82
def seedCap : Nat := 2703
def qDegree : Nat := 163462

/-- Inclusive degree cap for `A`. -/
def aMax : Nat := 950769

/-- Inclusive degree cap for the cancellation remainder `B0`. -/
def b0Max : Nat := 1180521

/-- Inclusive degree cap for `c`. -/
def cMax : Nat := 1049450

theorem parameter_identities :
    N = g + e ∧ D = m * g ∧ qDegree = 2 * e ∧
      qDegree - w = 32391 := by
  norm_num [N, g, e, D, m, qDegree, w]

/-- The `A Lambda Xi R Z * V^58` family, for every raw `Y` exponent. -/
theorem A_R_strip_legal (y : Nat) (hy : y ≤ 58) :
    aMax + g + e + qDegree * (58 - y) + w * y + (w - 1) < D := by
  simp only [aMax, g, e, qDegree, w, D]
  omega

/-- The `-2 A Lambda Xi' Y Z * V^58` family. -/
theorem A_Y_strip_legal (y : Nat) (hy0 : 1 ≤ y) (hy1 : y ≤ 59) :
    aMax + g + (e - 1) + qDegree * (59 - y) + w * y < D := by
  simp only [aMax, g, e, qDegree, w, D]
  omega

/-- The dangerous pure-seed remainder `-B0 Q Z^2 * V^58`. -/
theorem B0_Z_strip_legal (y : Nat) (hy : y ≤ 58) :
    b0Max + qDegree * (59 - y) + w * y < D := by
  simp only [b0Max, qDegree, w, D]
  omega

/-- The companion `B0 Y Z * V^58` family. -/
theorem B0_Y_strip_legal (y : Nat) (hy0 : 1 ≤ y) (hy1 : y ≤ 59) :
    b0Max + qDegree * (59 - y) + w * y < D := by
  simp only [b0Max, qDegree, w, D]
  omega

/-- The `c Y^2 * V^58` family. -/
theorem c_Y2_strip_legal (y : Nat) (hy0 : 2 ≤ y) (hy1 : y ≤ 60) :
    cMax + qDegree * (60 - y) + w * y < D := by
  simp only [cMax, qDegree, w, D]
  omega

/-- The coupled `-c Q Y Z * V^58` family. -/
theorem c_QY_strip_legal (y : Nat) (hy0 : 1 ≤ y) (hy1 : y ≤ 59) :
    cMax + qDegree * (60 - y) + w * y < D := by
  simp only [cMax, qDegree, w, D]
  omega

/-- Four strips hit the strict boundary exactly at `D-1`; there is no hidden
rounding slack in the chosen caps. -/
theorem critical_endpoints_exact :
    aMax + g + e + qDegree * 58 + (w - 1) = D - 1 ∧
    aMax + g + (e - 1) + qDegree * 58 + w = D - 1 ∧
    b0Max + qDegree * 59 = D - 1 ∧
    cMax + qDegree * 59 + w = D - 1 := by
  norm_num [aMax, b0Max, cMax, g, e, qDegree, w, D]

theorem terminal_shape_caps :
    m ≤ activeCap ∧ 1 ≤ 21 ∧ 0 ≤ 10 ∧
      m + (activeCap + 1 - m) ≤ seedCap := by
  norm_num [m, activeCap, seedCap]

/-- Every passive shift of the first active-terminal shell remains within the
literal total-grade cap. -/
theorem all_terminal_seed_shifts_legal (k : Nat) (hk : k ≤ 2620) :
    83 + k ≤ seedCap := by
  simp only [seedCap]
  omega

theorem terminal_seed_layer_count : 2703 - 83 + 1 = 2621 := by
  norm_num

/-- Parameter count before, and a conservative count after, imposing the
degree-`g` agreement congruence. -/
theorem coefficient_room :
    (aMax + 1) + (b0Max + 1) + (cMax + 1) = 3180743 ∧
    3180743 - g = 3000330 ∧
    (aMax + 1) + (b0Max + 1) + 1 - g = 1950880 ∧
    4 * e < 1950880 := by
  norm_num [aMax, b0Max, cMax, g, e]

/-- After solving the agreement congruence by `B0=Brem+Lambda*H`, the free
quotient still has room for twelve error-node Hermite coefficients. -/
theorem congruence_quotient_twelve_jet_room :
    b0Max + 1 - g = 1000109 ∧ 12 * e < 1000109 := by
  norm_num [b0Max, g, e]

#print axioms A_R_strip_legal
#print axioms A_Y_strip_legal
#print axioms B0_Z_strip_legal
#print axioms B0_Y_strip_legal
#print axioms c_Y2_strip_legal
#print axioms c_QY_strip_legal
#print axioms critical_endpoints_exact
#print axioms all_terminal_seed_shifts_legal
#print axioms coefficient_room
#print axioms congruence_quotient_twelve_jet_room

end ProximityPrize.SubmissionLower.Full187TerminalSeedTrellisWidth6900
