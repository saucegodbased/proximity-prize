import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# A57 direct-envelope countergate at the strengthened projective/wrap endpoint

The two numerical consequences currently exported from the surviving
DataEleven leaf do not by themselves make the direct Full187 A57 envelope
onto.  Take the canonical monomial pair

`V0 = X^262143`, `V1 = X^262142`.

Every nonzero constant direction has degree at least `262142`, hence at least
the new scalar cutoff `133222`.  The maximum row degree also satisfies the
nonpolynomial-wrap lower bound `237212 + ell` for every feasible
`ell <= 24931`.

Nevertheless, after allowing every mixed direct predecessor independently
through its complete physical residual window, cyclic coefficient `208036`
is still absent.  This is an API-scope STOP only: the full DataEleven leaf has
additional common-family/rational-cross fields which could still rule out
this pair or constrain the actual A57 right hand side.
-/

namespace ProximityPrize.SubmissionLower.Full187A57WedgeHighEndpointMonomialCountergate6900

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

variable {K : Type} [Field K]

/-- Cyclic shift of `V0^k * V1^(t-k)` for the hostile near-top pair. -/
def highMixedShift (t k : Nat) : Nat :=
  (k * 262143 + (t - k) * 262142) % 262144

/-- The complete residual window granted to total received-row power `t`. -/
def mixedPredecessorFringe (t : Nat) : Nat :=
  if t % 2 = 0 then 208036 + t else 76964 + t

/-- Coefficient `n` after cyclic multiplication by the monomial `X^shift`.
The source polynomial is always restricted to degree below `262144`. -/
def cyclicShiftedCoeff (shift n : Nat) (V : K[X]) : K :=
  V.coeff ((n + 262144 - shift) % 262144)

/-- At output coordinate `208036`, the required preimage coefficient lies
outside every one of the 300 complete direct residual windows. -/
theorem mixedPredecessorFringe_le_missingPreimage
    (t k : Nat) (ht : t < 24) (hk : k <= t) :
    mixedPredecessorFringe t <=
      (208036 + 262144 - highMixedShift t k) % 262144 := by
  interval_cases t <;> interval_cases k <;>
    norm_num [highMixedShift, mixedPredecessorFringe] at *

theorem one_high_mixed_predecessor_missing_coefficient
    (t k : Nat) (ht : t < 24) (hk : k <= t) (V : K[X])
    (hV : V.natDegree < mixedPredecessorFringe t) :
    cyclicShiftedCoeff (highMixedShift t k) 208036 V = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  exact hV.trans_le
    (mixedPredecessorFringe_le_missingPreimage t k ht hk)

/-- Even the enlarged direct sum where all 300 mixed channels vary
independently misses cyclic coefficient `208036`. -/
theorem all_high_mixed_predecessors_missing_coefficient
    (V : (t : Fin 24) -> Fin (t.val + 1) -> K[X])
    (hV : forall (t : Fin 24) (k : Fin (t.val + 1)),
      (V t k).natDegree < mixedPredecessorFringe t.val) :
    (∑ t : Fin 24, ∑ k : Fin (t.val + 1),
      cyclicShiftedCoeff (highMixedShift t.val k.val) 208036 (V t k)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t _ht
  apply Finset.sum_eq_zero
  intro k _hk
  exact one_high_mixed_predecessor_missing_coefficient
    t.val k.val t.isLt (by omega) (V t k) (hV t k)

/-- The pair satisfies the upgraded projective lower bound, with much room
to spare. -/
theorem hostile_pair_every_direction_high_133222
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    133222 <=
      (C a * X ^ 262143 + C b * X ^ 262142 : K[X]).natDegree := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := by simpa using hab
    simp [hb]
  · have htop :
        (C a * X ^ 262143 + C b * X ^ 262142 : K[X]).coeff 262143 = a := by
      simp
    have hcoeffNe :
        (C a * X ^ 262143 + C b * X ^ 262142 : K[X]).coeff 262143 ≠ 0 := by
      rw [htop]
      exact ha
    exact (show 133222 <= 262143 by norm_num).trans
      (le_natDegree_of_ne_zero hcoeffNe)

/-- It also satisfies the degree consequence of the canonical wedge wrap for
every feasible value of the leaf's auxiliary degree `ell`. -/
theorem hostile_pair_satisfies_wedge_degree_consequence
    (ell : Nat) (hell : ell <= 24931) :
    237212 + ell <=
      max (X ^ 262143 : K[X]).natDegree (X ^ 262142 : K[X]).natDegree := by
  simp
  omega

end ProximityPrize.SubmissionLower.Full187A57WedgeHighEndpointMonomialCountergate6900

#print axioms ProximityPrize.SubmissionLower.Full187A57WedgeHighEndpointMonomialCountergate6900.all_high_mixed_predecessors_missing_coefficient
#print axioms ProximityPrize.SubmissionLower.Full187A57WedgeHighEndpointMonomialCountergate6900.hostile_pair_every_direction_high_133222
#print axioms ProximityPrize.SubmissionLower.Full187A57WedgeHighEndpointMonomialCountergate6900.hostile_pair_satisfies_wedge_degree_consequence
