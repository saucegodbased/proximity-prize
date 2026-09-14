import Mathlib.Algebra.Field.Basic

/-!
# Abstract triangular cover for the k=0 error mismatches

The accepted 6810 proof contains a linear strong-induction principle in
`TriangularKernel.eq_zero_of_triangular`.  Raw bordered minors are not linear
in an error mismatch: the first exact chamber has a positive power of that
mismatch on the diagonal.  This file records the corresponding nonlinear
principle.

It deliberately does not assert that the literal contact matrix has the
required triangular formulas.  That is the remaining source theorem.
-/

namespace ProximityPrize.SubmissionLower.K0MismatchTriangularCover6900

set_option autoImplicit false

variable {K : Type*} [Field K] {n : Nat}

/-- A family of polynomial certificates with a nonzero power on each
successive diagonal detects every mismatch.  The diagonal coefficient may
depend on the full mismatch vector; it only has to be nonzero after all
earlier mismatches have been killed. -/
theorem eq_zero_of_power_triangular
    (certificate coefficient : (Fin n -> K) -> Fin n -> K)
    (power : Fin n -> Nat)
    (mismatch : Fin n -> K)
    (hcoefficient : forall i,
      (forall j, j.val < i.val -> mismatch j = 0) ->
        coefficient mismatch i ≠ 0)
    (hdiagonal : forall i,
      (forall j, j.val < i.val -> mismatch j = 0) ->
        certificate mismatch i =
          coefficient mismatch i * mismatch i ^ power i)
    (hzero : certificate mismatch = 0) :
    mismatch = 0 := by
  have hall : forall k : Nat, forall i : Fin n,
      i.val = k -> mismatch i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      have hearlier : forall j, j.val < i.val -> mismatch j = 0 := by
        intro j hj
        exact ih j.val (by omega) j rfl
      have hcertificate : certificate mismatch i = 0 := congrFun hzero i
      rw [hdiagonal i hearlier] at hcertificate
      by_contra hmismatch
      exact (mul_ne_zero (hcoefficient i hearlier)
        (pow_ne_zero _ hmismatch)) hcertificate
  funext i
  exact hall i.val i rfl

/-- Logical splice used by the desired rank-defect recovery theorem.  Rank
defect kills every mismatch-chart minor.  Power-triangularity therefore puts
the data on the globally matched branch, where one further minor excludes
rank defect unless the low-degree agreement interpolant already exists. -/
theorem rankDefect_implies_lowMatch_of_power_triangular_cover
    (LowMatch RankDefect : Prop)
    (certificate coefficient : (Fin n -> K) -> Fin n -> K)
    (matchedCertificate : (Fin n -> K) -> K)
    (power : Fin n -> Nat)
    (mismatch : Fin n -> K)
    (_hpower : forall i, 0 < power i)
    (hcoefficient : ¬ LowMatch -> forall i,
      (forall j, j.val < i.val -> mismatch j = 0) ->
        coefficient mismatch i ≠ 0)
    (hdiagonal : ¬ LowMatch -> forall i,
      (forall j, j.val < i.val -> mismatch j = 0) ->
        certificate mismatch i =
          coefficient mismatch i * mismatch i ^ power i)
    (hmismatchZero : RankDefect -> certificate mismatch = 0)
    (hmatchedZero : RankDefect -> matchedCertificate mismatch = 0)
    (hmatchedNonzero : ¬ LowMatch -> mismatch = 0 ->
      matchedCertificate mismatch ≠ 0) :
    RankDefect -> LowMatch := by
  intro hdefect
  by_contra hlow
  have hmismatch : mismatch = 0 :=
    eq_zero_of_power_triangular certificate coefficient power mismatch
      (hcoefficient hlow) (hdiagonal hlow)
      (hmismatchZero hdefect)
  exact (hmatchedNonzero hlow hmismatch) (hmatchedZero hdefect)

#print axioms eq_zero_of_power_triangular
#print axioms rankDefect_implies_lowMatch_of_power_triangular_cover

end ProximityPrize.SubmissionLower.K0MismatchTriangularCover6900
