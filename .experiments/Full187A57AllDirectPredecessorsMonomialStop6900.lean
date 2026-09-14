import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# All direct A57 predecessor windows miss a hostile monomial suffix

After normalizing the common twelfth-Hasse diagonal, the complete direct
`u0`-free predecessor census has one truncated polynomial channel for each
`h=0,...,23`.  For the high/root-free direction `u1=X^133120`, channel `h`
is shifted by `h*133120 mod 262144`.  This file proves that even an adversarial
envelope allowing an arbitrary polynomial throughout every physical residual
window has zero coefficient at `X^255163`.

The executable companion proves that the actual Hasse maps attain every
coefficient below 255163, giving exact defect 6981.  This kernel theorem is
the coefficient obstruction needed for RED and deliberately does not depend
on that attainment computation.
-/

namespace ProximityPrize.SubmissionLower.Full187A57AllDirectPredecessorsMonomialStop6900

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

variable {K : Type} [Field K]

/-- Cyclic monomial shift produced by `(X^133120)^h` on the 262144-point
multiplicative domain. -/
def hostileShift (h : Nat) : Nat := (h * 133120) % 262144

/-- Exact residual coefficient-window dimension after preserving the prior
prefix on the unique dual-visible predecessor with frozen-U power `h`. -/
def predecessorFringe (h : Nat) : Nat :=
  if h % 2 = 0 then 208036 + h else 76964 + h

/-- Every one of the 24 shifted residual windows ends before coefficient
255163. -/
theorem hostileShift_add_predecessorFringe_le
    (h : Nat) (hh : h < 24) :
    hostileShift h + predecessorFringe h ≤ 255163 := by
  interval_cases h <;> norm_num [hostileShift, predecessorFringe] at *

/-- One arbitrary residual channel in the enlarged adversarial envelope has
zero coefficient at the first missing monomial. -/
theorem one_direct_predecessor_missing_coefficient
    (h : Nat) (hh : h < 24) (V : K[X])
    (hV : V.natDegree < predecessorFringe h) :
    (X ^ hostileShift h * V).coeff 255163 = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  calc
    (X ^ hostileShift h * V).natDegree
        ≤ (X ^ hostileShift h).natDegree + V.natDegree := natDegree_mul_le
    _ = hostileShift h + V.natDegree := by simp
    _ < hostileShift h + predecessorFringe h := Nat.add_lt_add_left hV _
    _ ≤ 255163 := hostileShift_add_predecessorFringe_le h hh

/-- Even the direct sum of all 24 enlarged predecessor windows misses
`X^255163`.  The physical Hasse image is a subspace of this envelope. -/
theorem all_direct_predecessors_missing_coefficient
    (V : Fin 24 → K[X])
    (hV : ∀ h, (V h).natDegree < predecessorFringe h.val) :
    (∑ h : Fin 24, X ^ hostileShift h.val * V h).coeff 255163 = 0 := by
  classical
  have hcoeff : ∀ s : Finset (Fin 24),
      (∑ h ∈ s, X ^ hostileShift h.val * V h).coeff 255163 =
        ∑ h ∈ s, (X ^ hostileShift h.val * V h).coeff 255163 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert h s hnot ih => simp [Finset.sum_insert, hnot, ih, coeff_add]
  rw [hcoeff Finset.univ]
  apply Finset.sum_eq_zero
  intro h _hh
  exact one_direct_predecessor_missing_coefficient h.val h.isLt (V h) (hV h)

/-- The hostile direction lies in the universal high-degree branch. -/
theorem hostile_direction_degree :
    (X ^ 133120 : K[X]).natDegree = 133120 := by
  simp

/-- It is nonzero at every nonzero evaluation node. -/
theorem hostile_direction_root_free
    (x : K) (hx : x ≠ 0) :
    (X ^ 133120 : K[X]).eval x ≠ 0 := by
  simp [hx]

end ProximityPrize.SubmissionLower.Full187A57AllDirectPredecessorsMonomialStop6900

#print axioms ProximityPrize.SubmissionLower.Full187A57AllDirectPredecessorsMonomialStop6900.all_direct_predecessors_missing_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187A57AllDirectPredecessorsMonomialStop6900.hostile_direction_degree
#print axioms ProximityPrize.SubmissionLower.Full187A57AllDirectPredecessorsMonomialStop6900.hostile_direction_root_free
