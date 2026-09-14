import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic probe for the k0 top shell

This deliberately mirrors only the `budget`/`yCount` sigma index used by
`SecondJetRelaxedGlobalIndex`.  It can be checked without rebuilding the
large `LowerGeometry` aggregate.  `K0TopShellAdjointSeed6900.lean` states the
same constructor against the actual source type and is the integration gate.
-/

namespace K0TopShellArithmeticProbe6900

set_option autoImplicit false

def cutoff (_h : Nat) : Nat := 47 * 180413
def budget (h r : Nat) : Nat := cutoff h - (131071 - 2) * h - (131071 - 1) * r
def yCount (h r : Nat) : Nat :=
  min ((budget h r - 1) / 131071 + 1) (64 + 1 - h - r)

abbrev MirrorIndex :=
  Σ h : Fin 9, Σ r : Fin (16 - 2 * h.val + 1),
    Σ y : Fin (yCount h.val r.val),
      Fin (budget h.val r.val - 131071 * y.val) ×
        Fin (3757 + 1 - h.val - r.val - y.val)

theorem top_shell_budget_width (h : Fin 9) :
    budget h.val (16 - 2 * h.val) - 131071 * (48 + h.val) = 90883 := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp only [budget, cutoff]
  omega

theorem top_shell_yCount (h : Fin 9) :
    yCount h.val (16 - 2 * h.val) = 49 + h.val := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp only [yCount, budget, cutoff]
  norm_num
  omega

theorem top_shell_z_width (h : Fin 9) :
    3757 + 1 - h.val - (16 - 2 * h.val) - (48 + h.val) = 3694 := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  omega

def topShellIndex (h : Fin 9) (a : Fin 90883) (z : Fin 3694) :
    MirrorIndex := by
  let r : Fin (16 - 2 * h.val + 1) :=
    ⟨16 - 2 * h.val, Nat.lt_succ_self _⟩
  have hyCount : yCount h.val r.val = 49 + h.val := by
    simpa [r] using top_shell_yCount h
  let y : Fin (yCount h.val r.val) := by
    refine ⟨48 + h.val, ?_⟩
    rw [hyCount]
    omega
  have hxWidth : budget h.val r.val - 131071 * y.val = 90883 := by
    simpa [r, y] using top_shell_budget_width h
  let x : Fin (budget h.val r.val - 131071 * y.val) := by
    exact ⟨a.val, by simpa [hxWidth] using a.isLt⟩
  have hzWidth : 3757 + 1 - h.val - r.val - y.val = 3694 := by
    simpa [r, y] using top_shell_z_width h
  let zz : Fin (3757 + 1 - h.val - r.val - y.val) := by
    exact ⟨z.val, by simpa [hzWidth] using z.isLt⟩
  exact ⟨h, r, y, x, zz⟩

theorem topShellIndex_values
    (h : Fin 9) (a : Fin 90883) (z : Fin 3694) :
    (topShellIndex h a z).1.val = h.val ∧
      (topShellIndex h a z).2.1.val = 16 - 2 * h.val ∧
      (topShellIndex h a z).2.2.1.val = 48 + h.val ∧
      (topShellIndex h a z).2.2.2.1.val = a.val ∧
      (topShellIndex h a z).2.2.2.2.val = z.val := by
  simp [topShellIndex]

theorem topShellIndex_faces
    (h : Fin 9) (a : Fin 90883) (z : Fin 3694) :
    (topShellIndex h a z).1.val +
          (topShellIndex h a z).2.2.1.val +
          (topShellIndex h a z).2.1.val = 64 ∧
      2 * (topShellIndex h a z).1.val +
          (topShellIndex h a z).2.1.val = 16 := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp [topShellIndex]
  omega

theorem fortySeven_consecutive_fit (a0 : Nat) (ha0 : a0 + 47 ≤ 90883) :
    ∀ j : Fin 47, a0 + j.val < 90883 := by
  intro j
  have hj := j.isLt
  omega

#print axioms top_shell_budget_width
#print axioms top_shell_yCount
#print axioms topShellIndex_values
#print axioms topShellIndex_faces
#print axioms fortySeven_consecutive_fit

end K0TopShellArithmeticProbe6900
