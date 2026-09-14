import K0RawIndexContactCore6900

/-!
# The literal top shell of the k0 m47 source

The simultaneous active and derivative faces

```
h + y + r = 64,     2*h + r = 16
```

are parametrized by `h=0,...,8`, `r=16-2*h`, `y=48+h`.  At the
target value `g=180413`, every one of these nine shapes has exactly the same
available X width `90883` and Z width `3694`.  This file reifies those
coordinates as members of the *actual* `SecondJetRelaxedGlobalIndex`, rather
than merely recording external arithmetic inequalities.

This is only the source-legality half of the proposed top-shell adjoint seed.
The next gate must expand the literal contact map on these indices and prove
that its 47-coordinate Hasse observation block is unitriangular.
-/

namespace ProximityPrize.SubmissionLower.K0TopShellAdjointSeed6900

open K0RawIndexContactCore6900

set_option autoImplicit false
set_option Elab.async false

def targetG : Nat := 180413
def topXWidth : Nat := 90883
def topZWidth : Nat := 3694

theorem target_cutoff : k0Cutoff targetG 0 = 8479411 := by
  norm_num [k0Cutoff, targetG]

theorem top_shell_budget_width (h : Fin 9) :
    budget (k0Cutoff targetG) 131071 h.val (16 - 2 * h.val) -
        131071 * (48 + h.val) = topXWidth := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp only [budget, k0Cutoff, targetG, topXWidth]
  omega

theorem top_shell_yCount (h : Fin 9) :
    yCount (k0Cutoff targetG) 131071 64 h.val
        (16 - 2 * h.val) = 49 + h.val := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp only [yCount, budget, k0Cutoff, targetG]
  norm_num
  omega

theorem top_shell_z_width (h : Fin 9) :
    3757 + 1 - h.val - (16 - 2 * h.val) - (48 + h.val) =
      topZWidth := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp only [topZWidth]
  omega

/-- A literal coordinate on the simultaneous top active/derivative face of
the exact `(B,s,U,L)=(16,8,64,3757)` raw source. -/
def topShellIndex (h : Fin 9) (a : Fin topXWidth) (z : Fin topZWidth) :
    K0RawIndex targetG := by
  let r : Fin (16 - 2 * h.val + 1) :=
    ⟨16 - 2 * h.val, Nat.lt_succ_self _⟩
  have hyCount :
      yCount (k0Cutoff targetG) 131071 64 h.val r.val = 49 + h.val := by
    simpa [r] using top_shell_yCount h
  let y : Fin
      (yCount (k0Cutoff targetG) 131071 64 h.val r.val) := by
    refine ⟨48 + h.val, ?_⟩
    rw [hyCount]
    omega
  have hxWidth :
      budget (k0Cutoff targetG) 131071 h.val r.val -
        131071 * y.val = topXWidth := by
    simpa [r, y] using top_shell_budget_width h
  let x : Fin
      (budget (k0Cutoff targetG) 131071 h.val r.val -
        131071 * y.val) := by
    exact ⟨a.val, by simpa [hxWidth] using a.isLt⟩
  have hzWidth :
      3757 + 1 - h.val - r.val - y.val = topZWidth := by
    simpa [r, y] using top_shell_z_width h
  let zz : Fin (3757 + 1 - h.val - r.val - y.val) := by
    exact ⟨z.val, by simpa [hzWidth] using z.isLt⟩
  exact ⟨h, r, y, x, zz⟩

theorem topShellIndex_exponent
    (h : Fin 9) (a : Fin topXWidth) (z : Fin topZWidth) :
    exponent (topShellIndex h a z) =
      Finsupp.equivFunOnFinite.symm
        ![a.val, h.val, 48 + h.val, 16 - 2 * h.val, z.val] := by
  simp [topShellIndex, exponent]

theorem topShellIndex_active_face
    (h : Fin 9) (a : Fin topXWidth) (z : Fin topZWidth) :
    exponent (topShellIndex h a z) 1 +
        exponent (topShellIndex h a z) 2 +
        exponent (topShellIndex h a z) 3 = 64 := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp [topShellIndex, exponent]
  omega

theorem topShellIndex_derivative_face
    (h : Fin 9) (a : Fin topXWidth) (z : Fin topZWidth) :
    2 * exponent (topShellIndex h a z) 1 +
        exponent (topShellIndex h a z) 3 = 16 := by
  have hh : h.val ≤ 8 := Nat.le_of_lt_succ h.isLt
  simp [topShellIndex, exponent]
  omega

theorem fortySeven_consecutive_topShell_indices
    (h : Fin 9) (a0 : Nat) (ha0 : a0 + 47 ≤ topXWidth)
    (z : Fin topZWidth) :
    ∀ j : Fin 47, a0 + j.val < topXWidth := by
  intro j
  have hj : j.val < 47 := j.isLt
  omega

#print axioms top_shell_budget_width
#print axioms top_shell_yCount
#print axioms topShellIndex_exponent
#print axioms topShellIndex_active_face
#print axioms topShellIndex_derivative_face
#print axioms fortySeven_consecutive_topShell_indices

end ProximityPrize.SubmissionLower.K0TopShellAdjointSeed6900
