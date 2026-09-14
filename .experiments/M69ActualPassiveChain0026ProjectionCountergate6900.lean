import OriginalPassiveSeedSource6900
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The actual passive m69 top-grade Pascal direction

This file starts at the real `globalPassiveArrayConstraint`, rather than an
abstract rational multiplier.  It pins the robust profile and unfolds one
literal top-passive-grade summand.  The resulting Pascal multiplier is the
constraint's actual second received coordinate `values₁`; it is not an
independently chosen wedge `N0/E0`.

This is therefore both a small positive source projection theorem and a
countergate for the current rational-confluence attachment.  It deliberately
does not assert that a coefficient projection to the `(r,s,q)=(0,0,26)`
associated quotient exists: the current target is only the concrete
`passiveTargetSpan`, and no m69 quotient map selecting that tagged physical
coefficient has been defined.
-/

namespace ProximityPrize.SubmissionLower.M69ActualPassiveChain0026ProjectionCountergate6900

open Polynomial
open Order2SourceRank Order2PassiveSeedSource

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

/-- The exact robust-m69 source index used by the actual passive producer.
Here `69` is contact order and `94` is the global `Y`/terminal bound. -/
abbrev M69SourceIndex :=
  PassiveSourceIndex (69 * 180413) 131071 94 24 10 2369

/-- The real m69 contact map, with its original received pair kept visible. -/
def m69GlobalPassiveArrayConstraint
    (K : Type*) [Field K] (I : Type*) [Fintype I]
    (nodes values0 values1 : I → K) :
    (M69SourceIndex → K) →ₗ[K]
      PassiveGlobalConstraintTarget K I 69 94 24 10 2369 :=
  globalPassiveArrayConstraint K I 69 (69 * 180413) 131071 94 24 10 2369
    (by omega) nodes values0 values1

/-- Immediate caller equation: at each node the pinned global map is exactly
the coefficientwise contact truncation of the original local substitution.
No rational direction or leaf datum occurs in this equality. -/
theorem m69GlobalPassiveArrayConstraint_node_value
    (K : Type*) [Field K] (I : Type*) [Fintype I]
    (nodes values0 values1 : I → K) (theta : M69SourceIndex → K)
    (i : I) :
    (((m69GlobalPassiveArrayConstraint K I nodes values0 values1 theta) i :
        passiveTargetSpan K 69 94 24 10 2369) : SeedPoly K) =
      seedContactTruncation K 69
        (localSeedSubstitution K (nodes i) (values0 i) (values1 i)
          (reconstructPassiveSource K (69 * 180413) 131071 94 24 10 2369
            theta)) := by
  rw [m69GlobalPassiveArrayConstraint, globalPassiveArrayConstraint,
    LinearMap.pi_apply]
  exact localPassiveArrayConstraint_value K 69 (69 * 180413) 131071 94 24
    10 2369 (by omega) (nodes i) (values0 i) (values1 i) theta

/-- Scalar appearing in the implementation's literal passive column. -/
def literalPassiveScalar
    {K : Type*} [Field K] (u0 u1 : K) (k row g : Nat) : K :=
  u0 ^ (k - row - g) * u1 ^ g * (k.choose row : K) *
    ((k - row).choose g : K)

/-- On the top passive diagonal `g=k-row`, the residual `u0` power vanishes
and the actual Pascal multiplier is exactly `u1^(k-row)`. -/
theorem literalPassiveScalar_top_diagonal
    {K : Type*} [Field K] (u0 u1 : K) (k row : Nat)
    (_hrow : row ≤ k) :
    literalPassiveScalar u0 u1 k row (k - row) =
      (k.choose row : K) * u1 ^ (k - row) := by
  simp only [literalPassiveScalar]
  have hzero : k - row - (k - row) = 0 := Nat.sub_self _
  rw [hzero, pow_zero, one_mul, Nat.choose_self, Nat.cast_one, mul_one]
  ac_rfl

/-- Exact top-passive summand in `passiveColumnTerm`.  This is the literal
Pascal column formula inside the true source definition. -/
theorem passiveColumnTerm_top_diagonal
    (K : Type*) [Field K] (x u0 u1 : K)
    (a k row r s z : Nat) (hrow : row ≤ k) :
    passiveColumnTerm K x u0 u1 a k r s z row (k - row) =
      Polynomial.monomial (z + (k - row))
        (embedZPolynomial K
            (Polynomial.C ((k.choose row : K) * u1 ^ (k - row)) *
              translatedXPolynomial x a) *
          contactSubstitution K
            (layerSourceMonomial K (row + r + s) r s)) := by
  unfold passiveColumnTerm passiveColumnInner
  rw [show k - row - (k - row) = 0 by omega]
  simp only [pow_zero, one_mul, Nat.choose_self, Nat.cast_one, mul_one]
  congr 2
  ring_nf

/-- For the fixed total passive grade `2369`, every contact `k` contributes
to row `row` at the same output seed `2369-row`.  The direct chain pieces
`k=41,...,68` are instances of this formula; so is the actual terminal
coefficient `k=94,z=2275`. -/
theorem m69_chain_top_diagonal
    (K : Type*) [Field K] (x u0 u1 : K)
    (a k row : Nat) (hk : k ≤ 94) (hrow : row ≤ k) :
    passiveColumnTerm K x u0 u1 a k 0 0 (2369 - k) row (k - row) =
      Polynomial.monomial (2369 - row)
        (embedZPolynomial K
            (Polynomial.C ((k.choose row : K) * u1 ^ (k - row)) *
              translatedXPolynomial x a) *
          contactSubstitution K (layerSourceMonomial K row 0 0)) := by
  rw [passiveColumnTerm_top_diagonal K x u0 u1 a k row 0 0 (2369 - k) hrow]
  congr 2
  omega

/-- The concrete terminal `Y^94 * seed^2275` summand in deficient row 41.
Its multiplier is `u1^53`, not `u0^53`. -/
theorem m69_terminal94_row41
    (K : Type*) [Field K] (x u0 u1 : K) (a : Nat) :
    passiveColumnTerm K x u0 u1 a 94 0 0 2275 41 53 =
      Polynomial.monomial 2328
        (embedZPolynomial K
            (Polynomial.C ((Nat.choose 94 41 : K) * u1 ^ 53) *
              translatedXPolynomial x a) *
          contactSubstitution K (layerSourceMonomial K 41 0 0)) := by
  simpa using m69_chain_top_diagonal K x u0 u1 a 94 41 (by omega) (by omega)

/-- The same actual terminal coefficient in deficient row 42. -/
theorem m69_terminal94_row42
    (K : Type*) [Field K] (x u0 u1 : K) (a : Nat) :
    passiveColumnTerm K x u0 u1 a 94 0 0 2275 42 52 =
      Polynomial.monomial 2327
        (embedZPolynomial K
            (Polynomial.C ((Nat.choose 94 42 : K) * u1 ^ 52) *
              translatedXPolynomial x a) *
          contactSubstitution K (layerSourceMonomial K 42 0 0)) := by
  simpa using m69_chain_top_diagonal K x u0 u1 a 94 42 (by omega) (by omega)

/-- Already the adjacent direct column `k=42 -> row=41` forces any proposed
replacement multiplier to equal the source's actual `values₁` coordinate. -/
theorem adjacent_top_diagonal_forces_values1
    {K : Type*} [Field K] (u1 W : K) (h42 : (42 : K) ≠ 0)
    (hreplace : (42 : K) * u1 = (42 : K) * W) :
    W = u1 := by
  apply (mul_left_cancel₀ h42 hreplace).symm

/-- Profile arithmetic: the terminal source coordinate exists, and the two
deficient output rows and all direct contacts lie inside the true source
box. -/
theorem m69_chain_profile_arithmetic :
    94 + 2275 = 2369 ∧
      41 ≤ 68 ∧ 68 < 94 ∧
      69 * 180413 - 131071 * 94 = 127823 ∧
      127823 - 26 = 127797 := by
  norm_num

#print axioms m69GlobalPassiveArrayConstraint_node_value
#print axioms literalPassiveScalar_top_diagonal
#print axioms passiveColumnTerm_top_diagonal
#print axioms m69_chain_top_diagonal
#print axioms m69_terminal94_row41
#print axioms m69_terminal94_row42
#print axioms adjacent_top_diagonal_forces_values1
#print axioms m69_chain_profile_arithmetic

end
end ProximityPrize.SubmissionLower.M69ActualPassiveChain0026ProjectionCountergate6900
