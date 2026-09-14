import Mathlib.Tactic

/-!
Arithmetic core of the all-Hasse audit for the 105 locally free Full187
terminal shapes.  No finite matrix evaluation is embedded in this file.
-/

namespace ProximityPrize.SubmissionLower.Full187TerminalLowTHasse

/-- A positive coefficient-Hasse order cannot create a scalar-capacity
obstruction which was absent at order zero. -/
theorem capacity_bad_at_q_implies_bad_at_zero
    (baseMargin cutoff : ℤ) (g q : ℕ)
    (hbad : baseMargin + (g : ℤ) * q < cutoff) :
    baseMargin < cutoff := by
  have hnonneg : 0 ≤ (g : ℤ) * q :=
    mul_nonneg (Int.natCast_nonneg g) (Int.natCast_nonneg q)
  have hle : baseMargin ≤ baseMargin + (g : ℤ) * q :=
    le_add_of_nonneg_right hnonneg
  exact hle.trans_lt hbad

/-- Raising Hasse order adds `q` to the contact `T` index, so failure of the
sharp local pivot at order `q` implies failure already at order zero. -/
theorem pivot_bad_at_q_implies_bad_at_zero
    (T threshold q : ℕ) (hbad : T + q < threshold) :
    T < threshold := by
  omega

/-- A row surviving contact truncation at order `q` also survives at zero. -/
theorem survives_q_implies_survives_zero
    (baseWeight q m : ℕ) (hsurvives : q + baseWeight < m) :
    baseWeight < m := by
  omega

/-- The combined monotonicity used by the executable audit.  Here
`baseMargin + g*q < 0` is the structured-capacity condition and
`T+q < threshold` is failure of the sharp order-two pivot. -/
theorem obstruction_at_q_implies_obstruction_at_zero
    (baseMargin cutoff : ℤ) (g q T threshold baseWeight m : ℕ)
    (hcapacity : baseMargin + (g : ℤ) * q < cutoff)
    (hpivot : T + q < threshold)
    (hsurvives : q + baseWeight < m) :
    baseMargin < cutoff ∧ T < threshold ∧ baseWeight < m := by
  exact ⟨capacity_bad_at_q_implies_bad_at_zero baseMargin cutoff g q hcapacity,
    pivot_bad_at_q_implies_bad_at_zero T threshold q hpivot,
    survives_q_implies_survives_zero baseWeight q m hsurvives⟩

/-- The stronger arbitrary-error staircase has 103 shapes.  Its exact
boundary is checked independently by the executable audit. -/
theorem compact_affine_shape_count_arithmetic :
    17 + 16 + 15 + 14 + 13 + 12 + 10 + 5 + 1 = 103 := by
  norm_num

#print axioms obstruction_at_q_implies_obstruction_at_zero
#print axioms compact_affine_shape_count_arithmetic

end ProximityPrize.SubmissionLower.Full187TerminalLowTHasse
