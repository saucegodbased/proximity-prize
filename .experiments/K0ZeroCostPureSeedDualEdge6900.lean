import K0FilteredCrtGroebnerDual6900

/-!
# The zero-cost pure-seed edge in quotient-dual coordinates

For the raw shapes `X^a Z^z` (`y=r=s=0`), the PC substitution has no
off-diagonal terms: localization changes only `X^a` to `(x+T)^a`, and the
outer passive-seed degree remains exactly `z`.  Every one of the 3758 legal
seed bands therefore has the full `X` window.

At a general boundary seed `gamma`, the first boundary jet in the `Z`
direction has coefficient `z * gamma^(z-1)`.  This file identifies the
consequence without a rank-by-dimension argument.  Perfectness of the
quotient-top pairing says that every pure-seed numerator is the corresponding
scalar multiple of the unique numerator representing evaluation at the
boundary `X` coordinate.  At the centered seed `gamma=0`, only `z=1`
survives.

This is a useful forced one-dimensional jet sequence, but also an exact stop:
that evaluation numerator is nonzero.  Thus the pure-seed family by itself is
compatible with an arbitrary nonzero `Z` boundary dual.  A successful
recurrence must couple this sequence to a different PC shape; adjacent pure
seed bands do not.
-/

namespace ProximityPrize.SubmissionLower.K0ZeroCostPureSeedDualEdge6900

open Polynomial
open HrsQuotientTopPairing6900
open K0FilteredCrtGroebnerDual6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-! ## The literal pure-seed primal column -/

/-- Once the all-node contact coefficient of `X^a` has been formed, a raw
pure seed `X^a Z^z` is literally this monomial in the outer seed variable.
This is the part of the PC identity relevant to the global quotient: no
other outer seed degree occurs. -/
def pureSeedColumn (z : Nat) (P : K[X]) : Polynomial K[X] :=
  Polynomial.monomial z P

theorem pureSeedColumn_coeff (z n : Nat) (P : K[X]) :
    (pureSeedColumn z P).coeff n = if z = n then P else 0 := by
  exact Polynomial.coeff_monomial

/-- In particular, distinct pure-seed bands have disjoint outer-seed
support.  This is why the full X windows do not create a recurrence between
their quotient numerators. -/
theorem pureSeedColumn_coeff_other
    (z n : Nat) (P : K[X]) (hzn : z ≠ n) :
    (pureSeedColumn z P).coeff n = 0 := by
  rw [pureSeedColumn, Polynomial.coeff_monomial, if_neg hzn]

/-! ## The evaluation numerator -/

/-- Evaluation at `xi`, restricted to the full quotient window. -/
def boundedEvalFunctional (M : Nat) (xi : K) :
    Module.Dual K K[X]_M where
  toFun p := p.val.eval xi
  map_add' p q := by simp
  map_smul' c p := by simp

/-- The unique reduced quotient numerator whose top pairing is evaluation at
`xi`.  Existence and uniqueness come from the explicit perfectness proof for
`quotientTopPairing`, not from a matrix dimension assertion. -/
def quotientEvalNumerator
    (A : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) (xi : K) : K[X]_M :=
  Classical.choose
    (exists_unique_quotientTop_numerator A M hM hA hAM
      (boundedEvalFunctional M xi))

theorem quotientEvalNumerator_spec
    (A : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) (xi : K) :
    quotientTopDualMap A M
        (quotientEvalNumerator A M hM hA hAM xi) =
      boundedEvalFunctional M xi := by
  exact (Classical.choose_spec
    (exists_unique_quotientTop_numerator A M hM hA hAM
      (boundedEvalFunctional M xi))).1

theorem quotientTopPairing_evalNumerator
    (A : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) (xi : K)
    (p : K[X]_M) :
    quotientTopPairing A
        (quotientEvalNumerator A M hM hA hAM xi).val p.val M =
      p.val.eval xi := by
  have h := LinearMap.congr_fun
    (quotientEvalNumerator_spec A M hM hA hAM xi) p
  exact h

/-- The evaluation numerator cannot vanish: its pairing with the constant
polynomial is one. -/
theorem quotientEvalNumerator_ne_zero
    (A : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M) (xi : K) :
    quotientEvalNumerator A M hM hA hAM xi ≠ 0 := by
  intro hzero
  let one : K[X]_M :=
    ⟨1, by
      rw [Polynomial.mem_degreeLT]
      simpa using hM⟩
  have hpair := quotientTopPairing_evalNumerator
    A M hM hA hAM xi one
  rw [hzero] at hpair
  simp [quotientTopPairing, one] at hpair

/-! ## What a full zero-cost band forces -/

/-- An inhomogeneous full-window equation with right side
`lambda * p(xi)` determines the reduced numerator exactly. -/
theorem full_window_eval_forces_reduced_numerator
    (A q : K[X]) (M : Nat) (hM : 0 < M)
    (hA : A.Monic) (hAM : A.natDegree = M)
    (xi lambda : K)
    (hpair : ∀ p : K[X], p.natDegree < M →
      quotientTopPairing A q p M = lambda * p.eval xi) :
    q %ₘ A =
      lambda • (quotientEvalNumerator A M hM hA hAM xi).val := by
  have hredNat : (q %ₘ A).natDegree < M := by
    simpa using natDegree_reduced_mul_lt A q 1 M hM hA hAM
  let qred : K[X]_M :=
    ⟨q %ₘ A, by
      rw [Polynomial.mem_degreeLT]
      by_cases hq : q %ₘ A = 0
      · simp [hq]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hq).1 hredNat⟩
  have hdual :
      quotientTopDualMap A M qred =
        lambda • boundedEvalFunctional M xi := by
    apply LinearMap.ext
    intro p
    change quotientTopPairing A (q %ₘ A) p.val M =
      lambda * p.val.eval xi
    have hpNat : p.val.natDegree < M := by
      have hpDegree : p.val.degree < (M : WithBot Nat) :=
        Polynomial.mem_degreeLT.mp p.property
      by_cases hp0 : p.val = 0
      · simpa [hp0] using hM
      · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpDegree
    rw [show quotientTopPairing A (q %ₘ A) p.val M =
        quotientTopPairing A q p.val M by
      have ht := quotientTopPairing_mul_transport A q 1 p.val M hA
      simpa using ht]
    exact hpair p.val hpNat
  have heval :
      quotientTopDualMap A M
          (lambda • quotientEvalNumerator A M hM hA hAM xi) =
        lambda • boundedEvalFunctional M xi := by
    rw [map_smul, quotientEvalNumerator_spec]
  have hsubtype :
      qred = lambda • quotientEvalNumerator A M hM hA hAM xi :=
    quotientTopDualMap_injective A M hM hA hAM (hdual.trans heval.symm)
  exact congrArg Subtype.val hsubtype

/-- Scalar in the `Z` derivative of the raw seed monomial `Z^z`, evaluated
at the boundary seed `gamma`. -/
def pureSeedBoundaryScalar (gamma lambda : K) (z : Nat) : K :=
  (z : K) * gamma ^ (z - 1) * lambda

/-- Literal transpose right side of the pure-seed first-boundary jet. -/
def pureSeedBoundaryRHS
    (xi gamma lambda : K) (z : Nat) (p : K[X]) : K :=
  pureSeedBoundaryScalar gamma lambda z * p.eval xi

/-- All 3758 legal pure-seed bands determine the actual quotient numerators
as a one-dimensional derivative-jet sequence. -/
theorem m47_all_pure_seed_bands_force_exact_numerators
    (A : K[X]) (g : Nat) (hg : 180413 ≤ g)
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * g)
    (xi gamma lambda : K) (q : Fin 3758 → K[X])
    (hpair : ∀ z : Fin 3758, ∀ p : K[X], p.natDegree < 47 * g →
      quotientTopPairing A (q z) p (47 * g) =
        pureSeedBoundaryRHS xi gamma lambda z.val p) :
    ∀ z : Fin 3758,
      q z %ₘ A =
        pureSeedBoundaryScalar gamma lambda z.val •
          (quotientEvalNumerator A (47 * g) (by omega) hA hAdeg xi).val := by
  intro z
  apply full_window_eval_forces_reduced_numerator
    A (q z) (47 * g) (by omega) hA hAdeg xi
      (pureSeedBoundaryScalar gamma lambda z.val)
  intro p hp
  exact hpair z p hp

/-! ## Exact non-closure -/

/-- There is a nonzero `Z`-boundary-compatible quotient packet satisfying
every legal pure-seed equation.  Therefore this zero-cost family cannot by
itself prove that the `Z` component of the boundary dual vanishes. -/
theorem exists_all_pure_seed_packet_with_nonzero_Z_numerator
    (A : K[X]) (g : Nat) (hg : 180413 ≤ g)
    (hA : A.Monic) (hAdeg : A.natDegree = 47 * g)
    (xi gamma : K) :
    ∃ q : Fin 3758 → K[X],
      (∀ z : Fin 3758, ∀ p : K[X], p.natDegree < 47 * g →
        quotientTopPairing A (q z) p (47 * g) =
          pureSeedBoundaryRHS xi gamma 1 z.val p) ∧
      q ⟨1, by norm_num⟩ %ₘ A ≠ 0 := by
  let hM : 0 < 47 * g := by omega
  let e := quotientEvalNumerator A (47 * g) hM hA hAdeg xi
  let q : Fin 3758 → K[X] := fun z ↦
    pureSeedBoundaryScalar gamma 1 z.val • e.val
  refine ⟨q, ?_, ?_⟩
  · intro z p hp
    let pb : K[X]_(47 * g) :=
      ⟨p, by
        rw [Polynomial.mem_degreeLT]
        by_cases hp0 : p = 0
        · rw [hp0, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe _
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).1 hp⟩
    have hmap :
        quotientTopDualMap A (47 * g)
            (pureSeedBoundaryScalar gamma 1 z.val • e) =
          pureSeedBoundaryScalar gamma 1 z.val •
            boundedEvalFunctional (47 * g) xi := by
      rw [map_smul]
      exact congrArg
        (fun ell : Module.Dual K K[X]_(47 * g) ↦
          pureSeedBoundaryScalar gamma 1 z.val • ell)
        (quotientEvalNumerator_spec A (47 * g) hM hA hAdeg xi)
    have hpPair := LinearMap.congr_fun hmap pb
    change quotientTopPairing A
        (pureSeedBoundaryScalar gamma 1 z.val • e.val) p (47 * g) =
      pureSeedBoundaryScalar gamma 1 z.val * p.eval xi at hpPair
    simpa only [q, pureSeedBoundaryRHS] using hpPair
  · have heNat : e.val.natDegree < 47 * g := by
      have heDegree : e.val.degree < ((47 * g : Nat) : WithBot Nat) :=
        Polynomial.mem_degreeLT.mp e.property
      by_cases he0 : e.val = 0
      · simp [he0, hM]
      · exact (Polynomial.natDegree_lt_iff_degree_lt he0).2 heDegree
    have hemod := modByMonic_eq_self_of_natDegree_lt
      A e.val (47 * g) hA hAdeg heNat
    simp [q, pureSeedBoundaryScalar]
    rw [hemod]
    intro heval
    have hene : e ≠ 0 := by
      dsimp [e]
      exact quotientEvalNumerator_ne_zero A (47 * g) hM hA hAdeg xi
    apply hene
    apply Subtype.ext
    exact heval

#print axioms pureSeedColumn_coeff
#print axioms quotientEvalNumerator_spec
#print axioms full_window_eval_forces_reduced_numerator
#print axioms m47_all_pure_seed_bands_force_exact_numerators
#print axioms exists_all_pure_seed_packet_with_nonzero_Z_numerator

end

end ProximityPrize.SubmissionLower.K0ZeroCostPureSeedDualEdge6900
