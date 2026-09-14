import HrsQuotientTopPairing6900
import Lean.Elab.Tactic.Omega

/-!
# Filtered CRT cokernels for the m47 weighted source

For one fixed contact shape, the strict global `X` taper is a polynomial
window.  After the reversed-Hasse CRT bridge has represented a contact dual
by a quotient numerator, the adjoint of a shape multiplier `U` is exactly

```text
g |-> (g * U) mod A.
```

This file identifies the cokernel of every such isolated tapered strip.  A
positive shape cost `c` leaves precisely the remainders of degree `< c`; the
zero-cost strip has no cokernel at all.  The target arithmetic at
`(m,U)=(47,64)` proves that every legal active shape has `c < 47*g`.

This is deliberately a strip theorem.  It does not assert that the literal
coupled `Y/R/S/Z` source is a module or that its PC filtration is confluent.
-/

namespace ProximityPrize.SubmissionLower.K0FilteredCrtGroebnerDual6900

open Polynomial
open HrsQuotientTopPairing6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- A nonconstant monic modulus makes every reduced numerator lie in the
full degree-`<M` quotient window. -/
theorem natDegree_reduced_mul_lt
    (A g U : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) :
    ((g * U) %ₘ A).natDegree < M := by
  have hAneOne : A ≠ 1 := by
    intro hAone
    rw [hAone, Polynomial.natDegree_one] at hAM
    omega
  rw [← hAM]
  exact Polynomial.natDegree_modByMonic_lt (g * U) hA hAneOne

/-- Exact filtered multiplier cokernel, before substituting `W=M-c`.
Annihilating every source multiplier of degree `<W` is equivalent to the
reduced adjoint numerator lying in the complementary window `<M-W` (or
being zero, because `natDegree 0 = 0`). -/
theorem annihilates_multiplier_window_iff_complementary
    (A g U : K[X]) (M W : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) (hWM : W < M) :
    (∀ p : K[X], p.natDegree < W →
        quotientTopPairing A g (U * p) M = 0) ↔
      (g * U) %ₘ A = 0 ∨ ((g * U) %ₘ A).natDegree < M - W := by
  have hredM : ((g * U) %ₘ A).natDegree < M :=
    natDegree_reduced_mul_lt A g U M hM hA hAM
  have hbase :=
    annihilates_quotientTopPairing_iff_complementary
      A ((g * U) %ₘ A) M W hA hAM hWM hredM
  constructor
  · intro hann
    apply hbase.mp
    intro p hp
    rw [quotientTopPairing_mul_transport A g U p M hA]
    exact hann p hp
  · intro hsmall p hp
    have hzero := hbase.mpr hsmall p hp
    rw [quotientTopPairing_mul_transport A g U p M hA] at hzero
    exact hzero

/-- Cost form of the preceding result.  A strip whose legal source width is
`M-c` has exactly a degree-`<c` reduced-numerator obstruction. -/
theorem annihilates_cost_window_iff_remainder_below_cost
    (A g U : K[X]) (M c : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M)
    (hc0 : 0 < c) (hcM : c < M) :
    (∀ p : K[X], p.natDegree < M - c →
        quotientTopPairing A g (U * p) M = 0) ↔
      (g * U) %ₘ A = 0 ∨ ((g * U) %ₘ A).natDegree < c := by
  have hwindow : M - c < M := by omega
  have hiff := annihilates_multiplier_window_iff_complementary
    A g U M (M - c) hM hA hAM hwindow
  rw [show M - (M - c) = c by omega] at hiff
  exact hiff

/-- Endpoint `c=0`: testing the full quotient window forces the reduced
adjoint numerator to vanish, rather than merely to have degree `<0`.

The proof uses the already formalized perfectness of the quotient-top
pairing, so it does not choose a matrix minor or infer rank from dimensions.
-/
theorem annihilates_full_multiplier_window_iff_remainder_zero
    (A g U : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) :
    (∀ p : K[X], p.natDegree < M →
        quotientTopPairing A g (U * p) M = 0) ↔
      (g * U) %ₘ A = 0 := by
  let r : K[X] := (g * U) %ₘ A
  have hrM : r.natDegree < M := by
    simpa only [r] using natDegree_reduced_mul_lt A g U M hM hA hAM
  constructor
  · intro hann
    let rb : K[X]_M :=
      ⟨r, by
        rw [Polynomial.mem_degreeLT]
        by_cases hr0 : r = 0
        · simp [hr0]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hr0).1 hrM⟩
    have hmapzero : quotientTopDualMap A M rb = 0 := by
      apply LinearMap.ext
      intro p
      change quotientTopPairing A r p.val M = 0
      rw [show r = (g * U) %ₘ A by rfl,
        quotientTopPairing_mul_transport A g U p.val M hA]
      apply hann p.val
      have hpdegree : p.val.degree < (M : WithBot Nat) := by
        exact Polynomial.mem_degreeLT.mp p.property
      by_cases hp0 : p.val = 0
      · simpa [hp0] using hM
      · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdegree
    have heqmap :
        quotientTopDualMap A M rb = quotientTopDualMap A M 0 := by
      simpa using hmapzero
    have hrbzero : rb = 0 :=
      (quotientTopDualMap_injective A M hM hA hAM) heqmap
    have hval := congrArg (fun q : K[X]_M ↦ q.val) hrbzero
    simpa only [rb, r, Submodule.coe_zero] using hval
  · intro hred p hp
    calc
      quotientTopPairing A g (U * p) M =
          quotientTopPairing A ((g * U) %ₘ A) p M :=
        (quotientTopPairing_mul_transport A g U p M hA).symm
      _ = 0 := by simp [hred, quotientTopPairing]

/-! ## Exact m47 taper arithmetic -/

/-- Loss of global `X` width for an active weighted source shape
`Y^y R^r S^s`.  This is the literal global-index weight in
`SecondJetRelaxedGlobalIndex`, after the `X` exponent is separated.  It is
not a coefficient read from `SecondJetWeightedBasis.weightedTerm`: that
family is a local contact-kernel family, not the raw source basis. -/
def m47WeightedCost (y r s : Nat) : Nat :=
  131071 * y + 131070 * r + 131069 * s

theorem m47WeightedCost_eq_active_base (y r s : Nat) :
    m47WeightedCost y r s =
      131069 * (y + r + s) + 2 * y + r := by
  simp only [m47WeightedCost]
  omega

theorem m47WeightedCost_pos_of_active
    (y r s : Nat) (hactive : 0 < y + r + s) :
    0 < m47WeightedCost y r s := by
  rw [m47WeightedCost_eq_active_base]
  omega

/-- Every target-legal active shape is strictly inside the `47*g` pole
degree.  At the worst active degree 64 the gap is already 90,867 when
`g=180413`; larger exact-G strata only improve it. -/
theorem m47WeightedCost_lt_pole
    (g y r s : Nat) (hg : 180413 ≤ g) (hactive : y + r + s ≤ 64) :
    m47WeightedCost y r s < 47 * g := by
  rw [m47WeightedCost_eq_active_base]
  omega

theorem m47_worst_active_gap :
    47 * 180413 - 131071 * 64 = 90867 := by
  norm_num

/-- Target specialization: once a literal PC/contact triangular argument
has isolated one legal active shape, its entire dual obstruction is a
reduced polynomial of degree below the explicit weighted cost. -/
theorem m47_active_shape_cokernel
    (A q U : K[X]) (g y r s : Nat)
    (hg : 180413 ≤ g) (hactive : y + r + s ≤ 64)
    (hactive0 : 0 < y + r + s)
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * g) :
    (∀ p : K[X],
        p.natDegree < 47 * g - m47WeightedCost y r s →
          quotientTopPairing A q (U * p) (47 * g) = 0) ↔
      (q * U) %ₘ A = 0 ∨
        ((q * U) %ₘ A).natDegree < m47WeightedCost y r s := by
  apply annihilates_cost_window_iff_remainder_below_cost
  · omega
  · exact hA
  · exact hAdeg
  · exact m47WeightedCost_pos_of_active y r s hactive0
  · exact m47WeightedCost_lt_pole g y r s hg hactive

/-- The constant active shape has the full polynomial window, so its
reduced numerator vanishes outright. -/
theorem m47_constant_shape_dual_zero
    (A q U : K[X]) (g : Nat) (hg : 180413 ≤ g)
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * g) :
    (∀ p : K[X], p.natDegree < 47 * g →
        quotientTopPairing A q (U * p) (47 * g) = 0) ↔
      (q * U) %ₘ A = 0 := by
  exact annihilates_full_multiplier_window_iff_remainder_zero
    A q U (47 * g) (by omega) hA hAdeg

#print axioms natDegree_reduced_mul_lt
#print axioms annihilates_multiplier_window_iff_complementary
#print axioms annihilates_cost_window_iff_remainder_below_cost
#print axioms annihilates_full_multiplier_window_iff_remainder_zero
#print axioms m47_active_shape_cokernel
#print axioms m47_constant_shape_dual_zero

end

end ProximityPrize.SubmissionLower.K0FilteredCrtGroebnerDual6900
