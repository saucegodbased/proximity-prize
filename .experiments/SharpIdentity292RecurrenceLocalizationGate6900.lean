import RecurrenceGeneratorSpan
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.NormNum

/-!
# The 292-node hard branch makes original-recurrence localization fit

This file isolates the exact positive fact which was unavailable in the
coarser identity-core branch.  If at most 292 of the 262144 nodes lie outside
the fixed identity locus, then the outside locator and the sharp high-E pole
cost at most

`292 + 18414 = 18706`

degrees.  Therefore every original recurrence in grade 81731 can be
localized in grade 100437, retaining all shifts through 30634.

The theorem deliberately stops at recurrence membership.  Its proof uses no
selected polynomial, scalar polynomial, source row, or identity-row equation.
Consequently it is a provenance gate: a downstream contradiction must still
prove that substituting the identity rows into one of these 30635 recurrence
equations gives a new nonzero constraint rather than the normalized-source
tautology.
-/

namespace ProximityPrize.SubmissionLower.SharpIdentity292RecurrenceLocalizationGate6900

open Polynomial RecurrenceShiftIntersection
open RecurrenceGeneratorSpan

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Exact endpoint ledger.  There are 30635 admissible shifts, indexed
`0,...,30634`, after paying the full worst-case localization cost. -/
theorem hard_branch_localization_arithmetic :
    18414 + 292 = 18706 ∧
      81731 + 18706 = 100437 ∧
      100437 + 30634 = 131071 ∧
      131071 - 100437 + 1 = 30635 ∧
      100437 < 131071 := by
  norm_num

/-- The monic locator of a finite node set.  This local definition keeps the
certificate independent of the much larger benchmark import graph. -/
def nodeLocator {K I : Type*} [Field K]
    (nodes : I → K) (S : Finset I) : K[X] :=
  ∏ i ∈ S, (X - C (nodes i))

theorem nodeLocator_monic {K I : Type*} [Field K]
    (nodes : I → K) (S : Finset I) : (nodeLocator nodes S).Monic := by
  simpa [nodeLocator] using
    (Polynomial.monic_prod_X_sub_C (b := nodes) (s := S))

theorem nodeLocator_natDegree {K I : Type*} [Field K]
    (nodes : I → K) (S : Finset I) :
    (nodeLocator nodes S).natDegree = S.card := by
  have h := Polynomial.natDegree_prod_of_monic S
    (fun i : I ↦ (X - C (nodes i) : K[X]))
    (by intro i hi; simpa using Polynomial.monic_X_sub_C (nodes i))
  simpa [nodeLocator] using h

/-- Small-import version of arbitrary-polynomial recurrence propagation. -/
theorem polynomial_mul_recurrence
    {K J : Type*} [Field K]
    (L : J → (K[X] →ₗ[K] K)) (N a b : Nat)
    (q p : K[X]) (hq : q ∈ recurrenceSpace L N a)
    (hp : p.natDegree ≤ b) :
    p * q ∈ recurrenceSpace L N (a + b) := by
  rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp), Finset.sum_mul]
  apply Submodule.sum_mem
  intro k hk
  have hkb : k ≤ b := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hpow := pow_mul_mem_recurrenceSpace L N a k q hq
  have hmem : X ^ k * q ∈ recurrenceSpace L N (a + b) :=
    recurrenceSpace_mono L N (by omega) hpow
  have hs := (recurrenceSpace L N (a + b)).smul_mem (p.coeff k) hmem
  convert hs using 1 <;> rw [Polynomial.smul_eq_C_mul] <;> ring

/-- Generic algebraic core: multiplication by `E` and the outside locator
preserves the full recurrence property at the declared larger grade. -/
theorem localized_recurrence_mem_grade_100437
    {K J I : Type*} [Field K] [Fintype I]
    (L : J → (K[X] →ₗ[K] K)) (nodes : I → K)
    (outside : Finset I) (E q : K[X])
    (houtside : outside.card ≤ 292)
    (hEdegree : E.natDegree ≤ 18414)
    (hq : q ∈ recurrenceSpace L 131071 81731) :
    let M := E * nodeLocator nodes outside
    M.natDegree ≤ 18706 ∧
      M * q ∈ recurrenceSpace L 131071 100437 ∧
      ∀ r : Nat, r ≤ 30634 →
        ∀ j : J, L j (X ^ r * (M * q)) = 0 := by
  dsimp only
  have hlocator : (nodeLocator nodes outside).natDegree ≤ 292 := by
    rw [nodeLocator_natDegree]
    exact houtside
  have hMdegree :
      (E * nodeLocator nodes outside).natDegree ≤ 18706 := by
    exact (natDegree_mul_le.trans (Nat.add_le_add hEdegree hlocator)).trans
      (by norm_num)
  have hmem :
      (E * nodeLocator nodes outside) * q ∈
        recurrenceSpace L 131071 100437 := by
    have h := polynomial_mul_recurrence L 131071 81731 18706
      q (E * nodeLocator nodes outside) hq hMdegree
    simpa only using h
  refine ⟨hMdegree, hmem, ?_⟩
  intro r hr j
  exact hmem.2 j r (by omega)

/-- The hard node-cardinality branch supplies the advertised 292-node
outside set on the actual 262144-node target domain. -/
theorem hard_identity_locus_outside_card_le
    {I : Type*} [Fintype I] (Z : Finset I)
    (hI : Fintype.card I = 262144) (hZ : 261852 ≤ Z.card) :
    ((Finset.univ : Finset I) \ Z).card ≤ 292 := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hI]
  omega

/-- Nonzeroness is also preserved.  This is useful because the target leaf's
nullity `>=7459` supplies a nonzero `q`, its sharp package supplies `E≠0`,
and a node locator is monic. -/
theorem localized_recurrence_ne_zero
    {K I : Type*} [Field K] (nodes : I → K) (outside : Finset I)
    (E q : K[X]) (hE : E ≠ 0) (hq : q ≠ 0) :
    (E * nodeLocator nodes outside) * q ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hE (nodeLocator_monic nodes outside).ne_zero) hq

#print axioms hard_branch_localization_arithmetic
#print axioms polynomial_mul_recurrence
#print axioms localized_recurrence_mem_grade_100437
#print axioms hard_identity_locus_outside_card_le
#print axioms localized_recurrence_ne_zero

end
end ProximityPrize.SubmissionLower.SharpIdentity292RecurrenceLocalizationGate6900
