import OriginalPassiveSeedSource6900
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Top-passive-grade obstruction to covariant wedge synthesis

Algebraically, all mixed channels of total row degree `h` can be combined to
make `(d*u0-c*u1)^h`.  This file records the exact reason that construction is
*not available* on the top passive diagonal used by the literal DataEleven
`(0,0,26)` chain.

For a source contact `k=y+h`, a channel with `u1`-exponent `g` must start at
passive seed `z` and lands at output seed `z+g`.  At the top output seed
`seedCap-y`, source legality says `z+k <= seedCap`.  Alignment and legality
force `h <= g`; the mixed-channel range gives `g <= h`, hence only `g=h`
survives.  It contributes the pure `u1^h` term, not the full wedge.

For m69, `seedCap=2369`.  Row 41 has top output seed 2328 and row 42 has
top output seed 2327.  The shape parameter `q=26` is an X-Hasse/order
parameter and plays no role in this passive-seed arithmetic.
-/

namespace ProximityPrize.SubmissionLower.M69CovariantWedgeSourceCombination6900

open Polynomial
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

/-- The hypothetical full mixed family does algebraically synthesize the
physical wedge.  The later theorems show that the actual top passive grade
does not supply this family. -/
theorem mixed_channels_synthesize_wedge
    {K : Type*} [CommRing K] (c d u0 u1 : K) (h : Nat) :
    (∑ g ∈ Finset.range (h + 1),
        (-c * u1) ^ g * (d * u0) ^ (h - g) * (h.choose g : K)) =
      (d * u0 - c * u1) ^ h := by
  rw [← add_pow]
  ring

/-- Exact abstract top-grade gate.  A channel aligned to the top output
passive seed and legal in the source box must be the last channel `g=h`. -/
theorem top_passive_grade_forces_last_mixed_channel
    (seedCap y h g z : Nat)
    (hy : y ≤ seedCap) (hg : g ≤ h)
    (halign : z + g = seedCap - y)
    (hlegal : z + (y + h) ≤ seedCap) :
    g = h := by
  omega

/-- At positive row distance, a full mixed family cannot exist on the top
passive grade: already its `g=0` channel violates the source cap. -/
theorem top_passive_grade_has_no_full_mixed_family
    (seedCap y h : Nat) (hy : y ≤ seedCap) (hh : 0 < h) :
    ¬ (∀ g, g ≤ h → ∃ z,
      z + g = seedCap - y ∧ z + (y + h) ≤ seedCap) := by
  intro hall
  obtain ⟨z, halign, hlegal⟩ := hall 0 (Nat.zero_le h)
  have hlast := top_passive_grade_forces_last_mixed_channel
    seedCap y h 0 z hy (Nat.zero_le h) halign hlegal
  omega

/-- More generally, if the output is lowered by passive slack `ell`, then a
channel with exponent `g` needs `h <= g+ell`.  In particular, making the
`g=0` summand available requires at least `h` units of passive slack. -/
theorem mixed_channel_requires_passive_slack
    (seedCap y h g z ell : Nat)
    (halign : z + g + y + ell = seedCap)
    (hlegal : z + (y + h) ≤ seedCap) :
    h ≤ g + ell := by
  omega

theorem first_mixed_channel_requires_full_row_slack
    (seedCap y h z ell : Nat)
    (halign : z + 0 + y + ell = seedCap)
    (hlegal : z + (y + h) ≤ seedCap) :
    h ≤ ell := by
  simpa using mixed_channel_requires_passive_slack seedCap y h 0 z ell
    halign hlegal

/-- Literal row-41 specialization: output seed 2328 is `2369-41`. -/
theorem chain0026_row41_top_grade_only_last_channel
    (h g z : Nat) (hg : g ≤ h)
    (halign : z + g = 2328)
    (hlegal : z + (41 + h) ≤ 2369) :
    g = h := by
  exact top_passive_grade_forces_last_mixed_channel
    2369 41 h g z (by norm_num) hg (by norm_num at halign ⊢; exact halign)
      hlegal

/-- Literal row-42 specialization: output seed 2327 is `2369-42`. -/
theorem chain0026_row42_top_grade_only_last_channel
    (h g z : Nat) (hg : g ≤ h)
    (halign : z + g = 2327)
    (hlegal : z + (42 + h) ≤ 2369) :
    g = h := by
  exact top_passive_grade_forces_last_mixed_channel
    2369 42 h g z (by norm_num) hg (by norm_num at halign ⊢; exact halign)
      hlegal

/-- Consequently no positive-distance row-41 contact has all of the mixed
channels required by the binomial wedge expansion. -/
theorem chain0026_row41_no_full_mixed_family
    (h : Nat) (hh : 0 < h) :
    ¬ (∀ g, g ≤ h → ∃ z,
      z + g = 2328 ∧ z + (41 + h) ≤ 2369) := by
  simpa using top_passive_grade_has_no_full_mixed_family 2369 41 h
    (by norm_num) hh

/-- Same obstruction for the second top output row. -/
theorem chain0026_row42_no_full_mixed_family
    (h : Nat) (hh : 0 < h) :
    ¬ (∀ g, g ≤ h → ∃ z,
      z + g = 2327 ∧ z + (42 + h) ≤ 2369) := by
  simpa using top_passive_grade_has_no_full_mixed_family 2369 42 h
    (by norm_num) hh

/-- The actual top diagonal has input seed `2369-k`.  For row 41 its
surviving exponent is `g=k-41`, and it lands at seed 2328. -/
theorem chain0026_row41_top_diagonal_alignment
    (k : Nat) (hkLower : 41 ≤ k) (hkUpper : k ≤ 2369) :
    (2369 - k) + (k - 41) = 2328 := by
  omega

/-- Analogous arithmetic for row 42 and output seed 2327. -/
theorem chain0026_row42_top_diagonal_alignment
    (k : Nat) (hkLower : 42 ≤ k) (hkUpper : k ≤ 2369) :
    (2369 - k) + (k - 42) = 2327 := by
  omega

/-- The only available binomial summand is the `g=h` summand, which is just
the pure original-second-row power. -/
theorem last_mixed_channel_is_pure_u1
    {K : Type*} [CommRing K] (c d u0 u1 : K) (h : Nat) :
    (-c * u1) ^ h * (d * u0) ^ (h - h) * (h.choose h : K) =
      (-c * u1) ^ h := by
  simp

/-- A one-dimensional concrete falsifier: retaining only the last channel
cannot be confused with the full wedge identity. -/
theorem last_channel_is_not_full_wedge_concrete :
    ((-(1 : ℚ) * 1) ^ 1 * ((1 : ℚ) * 1) ^ (1 - 1) *
      (Nat.choose 1 1 : ℚ)) ≠
      (((1 : ℚ) * 1 - (1 : ℚ) * 1) ^ 1) := by
  norm_num

/-- Conditional coefficient-degree cost of a mixed summand.  This remains
useful below the top passive grade, but it does not repair the missing
channels proved above. -/
theorem mixed_channel_polynomial_degree_le
    {K : Type*} [Field K] (c d : K[X]) (h g s : Nat)
    (hg : g ≤ h) (hc : c.natDegree ≤ s) (hd : d.natDegree ≤ s) :
    (d ^ (h - g) * (-c) ^ g).natDegree ≤ h * s := by
  calc
    (d ^ (h - g) * (-c) ^ g).natDegree
        ≤ (d ^ (h - g)).natDegree + ((-c) ^ g).natDegree :=
          natDegree_mul_le
    _ ≤ (h - g) * d.natDegree + g * (-c).natDegree := by
          exact Nat.add_le_add natDegree_pow_le natDegree_pow_le
    _ = (h - g) * d.natDegree + g * c.natDegree := by
          rw [natDegree_neg]
    _ ≤ (h - g) * s + g * s := by
          exact Nat.add_le_add (Nat.mul_le_mul_left _ hd)
            (Nat.mul_le_mul_left _ hc)
    _ = h * s := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hg]

/-- Numerical scope receipt.  In particular, 26 is absent from the passive
seed calculation; it belongs to the independent X-Hasse/order profile. -/
theorem chain0026_passive_seed_receipt :
    2369 - 41 = 2328 ∧ 2369 - 42 = 2327 ∧
      (2369 - 68) + (68 - 41) = 2328 ∧
      (2369 - 68) + (68 - 42) = 2327 := by
  norm_num

#print axioms mixed_channels_synthesize_wedge
#print axioms top_passive_grade_forces_last_mixed_channel
#print axioms top_passive_grade_has_no_full_mixed_family
#print axioms mixed_channel_requires_passive_slack
#print axioms first_mixed_channel_requires_full_row_slack
#print axioms chain0026_row41_top_grade_only_last_channel
#print axioms chain0026_row42_top_grade_only_last_channel
#print axioms chain0026_row41_no_full_mixed_family
#print axioms chain0026_row42_no_full_mixed_family
#print axioms chain0026_row41_top_diagonal_alignment
#print axioms chain0026_row42_top_diagonal_alignment
#print axioms last_mixed_channel_is_pure_u1
#print axioms last_channel_is_not_full_wedge_concrete
#print axioms mixed_channel_polynomial_degree_le
#print axioms chain0026_passive_seed_receipt

end
end ProximityPrize.SubmissionLower.M69CovariantWedgeSourceCombination6900
