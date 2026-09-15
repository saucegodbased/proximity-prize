import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A cap-legal bivariate approximant window at K0 order seven

The eight weighted-order-seven monomials in `J,C1,C2` are individually
30,871 X degrees outside the target.  This file records a different source
space: give every monomial a coefficient polynomial of X degree at most 9450
and passive-Z degree at most 7, then impose cancellation of the first 40322
reversed X coefficients of its data face.

There are 604864 coefficient unknowns and at most 604830 scalar cancellation
conditions, uniformly for every pair of received interpolants `U0,U1`.
Consequently the approximant kernel has dimension at least 34.  Cancellation
leaves X degree exactly at most the strict target cutoff, while every term
containing Y/R/S has 90751 degrees of spare weighted-X room.

The final section records the weighted Euler identity that makes the
four-gradient symbol faithful on the order-seven covariant space.  This is
an error-order-seven rung: `H^37` supplies total order 44 at agreement roots,
but it is a unit at error roots, where the packet has only order seven.  It
therefore advances a layerwise recurrence and is not itself in the complete
old-low-head kernel.  Further obligations are the error-layer correction,
pointwise boundary rank, and all later rungs; the dimension receipt must not
be reported as any of those theorems.
-/

namespace ProximityPrize.SubmissionLower.K0OrderSevenBivariateApproximantDimension6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

def nodeCount : Nat := 262144
def agreement : Nat := 180413
def targetPole : Nat := 47 * agreement
def coefficientXCap : Nat := 9450
def coefficientZCap : Nat := 7
def cancellationDepth : Nat := coefficientXCap + 30872

def packetDimension : Nat :=
  8 * (coefficientXCap + 1) * (coefficientZCap + 1)

def cancellationDimension : Nat :=
  cancellationDepth * (coefficientZCap + 8)

/-- The uniform dimension surplus is 34; no rank or genericity assumption on
the received interpolants occurs in this count. -/
theorem target_bivariate_approximant_dimension_surplus :
    9450 + 30872 = 40322 /\
      8 * (9450 + 1) * (7 + 1) = 604864 /\
      40322 * (7 + 8) = 604830 /\
      604864 = 604830 + 34 := by
  norm_num

/-- Every linear top-coefficient map out of the packet box has a kernel of
dimension at least 34.  This is the basis-free form used by the construction:
the actual map may have smaller rank, which only enlarges the kernel. -/
theorem finrank_ker_topCancellation_ge_34
    (K : Type*) [Field K]
    (A : (Fin 604864 -> K) →ₗ[K]
      (Fin 604830 -> K)) :
    34 <= Module.finrank K (LinearMap.ker A) := by
  have hsum := LinearMap.finrank_range_add_finrank_ker A
  have hrange := Submodule.finrank_le (LinearMap.range A)
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  rw [Module.finrank_fintype_fun_eq_card] at hrange
  simp only [Fintype.card_fin] at hsum hrange
  omega

/-! ## Exact target cap ledger -/

/-- The coefficient convolution initially reaches degree 1844451.  Removing
40322 consecutive leading coefficients leaves degree at most 1804129, one
below the residual strict cutoff `10*g=1804130`. -/
theorem target_data_face_after_cancellation_green :
    7 * (262144 - 1) = 1835001 /\
      9450 + 7 * (262144 - 1) = 1844451 /\
      9450 + 7 * (262144 - 1) = 40322 + 1804129 /\
      47 * 180413 = 37 * 180413 + 1804130 /\
      37 * 180413 + 1804129 + 1 = 47 * 180413 := by
  norm_num

/-- Any term with at least one genuine active variable Y/R/S is cheaper than
the data face by at least `n-1-w=131072`.  Even before using cancellation,
all such terms remain 90751 below the global strict cutoff after the X
coefficient and `H^37` are charged. -/
theorem target_active_terms_have_90751_slack :
    (262144 - 1) - 131071 = 131072 /\
      37 * 180413 + 9450 +
          7 * (262144 - 1) - 131072 = 8388660 /\
      47 * 180413 - 8388660 = 90751 /\
      8388660 < 47 * 180413 := by
  norm_num

/-- Passive Z degree remains tiny: seven coefficient powers plus at most
seven powers from an order-seven covariant. -/
theorem target_passive_Z_envelope :
    7 + 7 = 14 /\
      14 <= 3757 /\
      7 <= 64 /\
      4 <= 16 /\
      2 <= 8 := by
  norm_num

/-- The top window is shorter than the `n=262144` gap between the two terms
of the actual NTT locator `X^n-1`.  Hence replacing `N` by `X^n` is exact in
this window, not a generic leading-symbol assumption. -/
theorem actual_ntt_locator_top_window_exact_arithmetic :
    9450 + 30872 = 40322 /\
      40322 < 262144 /\
      40322 + 221822 = 262144 := by
  norm_num

/-! ## Honest stage budgets

The 34-dimensional box above certifies a nonzero next-rung carrier.  It is
not large enough to prescribe one scalar independently at all 81731 errors.
Increasing only the X coefficient cap to 11119 leaves 81815 dimensions after
the same top-face cancellation: enough in dimension for one scalar error
layer and four boundary rows, with a margin of 80.  Surjectivity of that
actual joint map is a separate theorem.
-/

theorem target_orderSeven_oneLayer_dimension_budget :
    8 * (11119 + 1) * (7 + 1) = 711680 /\
      (11119 + 30872) * (7 + 7 + 1) = 629865 /\
      711680 - 629865 = 81815 /\
      81731 + 4 = 81735 /\
      81815 - 81735 = 80 := by
  norm_num

/-- The larger stage-seven box remains comfortably source-legal on every
term with at least one Y/R/S factor. -/
theorem target_orderSeven_oneLayer_active_slack :
    37 * 180413 + 11119 + 7 * (262144 - 1) - 131072 = 8390329 /\
      47 * 180413 - 8390329 = 89082 := by
  norm_num

/-- Order eight can also pay for a full scalar-error-layer-sized kernel at
the level of dimensions.  Ten weighted-order-eight covariants, X cap 13712,
and passive-Z coefficient cap 100 leave 81904 dimensions after cancellation,
169 more than `81731+4`.  The first active face still has 4759 degrees of
strict-cutoff slack.  Again, this is a budget, not a surjectivity theorem. -/
theorem target_orderEight_oneLayer_dimension_budget :
    10 * (13712 + 1) * (100 + 1) = 13850130 /\
      (13712 + 112602) * (100 + 8 + 1) = 13768226 /\
      13850130 - 13768226 = 81904 /\
      81904 - (81731 + 4) = 169 /\
      37 * 180413 + 81730 + 13712 +
          7 * (262144 - 1) - 131072 = 8474652 /\
      47 * 180413 - 8474652 = 4759 /\
      100 + 8 = 108 /\
      108 <= 3757 := by
  norm_num

/-- A full local error layer cannot be inferred from the preceding scalar
dimension budget.  The unique `Y^7` (equivalently highest ordinary-active)
channel comes only from `J^7`; at fixed passive-Z coefficient it factors
through at most 11120 X coefficients, far below 81731 error values. -/
theorem target_unique_high_active_channel_dimension_stop :
    11119 + 1 = 11120 /\
      11120 < 81731 /\
      81731 - 11120 = 70611 := by
  norm_num

theorem no_surjective_single_high_active_channel
    (K : Type*) [Field K]
    (f : (Fin 11120 -> K) →ₗ[K] (Fin 81731 -> K)) :
    Not (Function.Surjective f) := by
  intro hsurj
  have hdim := LinearMap.finrank_le_finrank_of_surjective hsurj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  omega

/-! ## Faithfulness of the four-gradient symbol -/

variable {R : Type*} [CommRing R]

abbrev Cov := MvPolynomial (Fin 3) R

def j : Cov (R := R) := MvPolynomial.X 0
def c1 : Cov (R := R) := MvPolynomial.X 1
def c2 : Cov (R := R) := MvPolynomial.X 2

def weightedEuler (P : Cov (R := R)) : Cov (R := R) :=
  j * MvPolynomial.pderiv 0 P +
    2 * c1 * MvPolynomial.pderiv 1 P +
      3 * c2 * MvPolynomial.pderiv 2 P

/-- The eight partitions `a+2b+3c=7`, in a fixed order. -/
def orderSevenCovariant (i : Fin 8) : Cov (R := R) := ![
  j ^ 7,
  j ^ 5 * c1,
  j ^ 3 * c1 ^ 2,
  j * c1 ^ 3,
  j ^ 4 * c2,
  j ^ 2 * c1 * c2,
  c1 ^ 2 * c2,
  j * c2 ^ 2] i

/-- Weighted Euler acts by the nonzero eigenvalue seven on every one of the
eight order-seven covariants. -/
theorem weightedEuler_orderSevenCovariant (i : Fin 8) :
    weightedEuler (orderSevenCovariant (R := R) i) =
      7 * orderSevenCovariant (R := R) i := by
  fin_cases i <;>
    simp [weightedEuler, orderSevenCovariant, j, c1, c2] <;>
    ring

/-- Thus an order-seven vector with zero J/C1/C2 gradient is zero whenever
seven is nonzero.  Coefficients may themselves contain X and passive Z,
because they live in the base ring `R` and are untouched by these three
derivatives. -/
theorem eq_zero_of_weightedOrderSeven_gradient_zero
    [IsDomain R]
    (P : Cov (R := R))
    (hEuler : weightedEuler P = 7 * P)
    (hgrad : forall i, MvPolynomial.pderiv i P = 0)
    (hseven : (7 : R) ≠ 0) :
    P = 0 := by
  have hleft : weightedEuler P = 0 := by
    simp [weightedEuler, hgrad]
  rw [hleft] at hEuler
  have hmul : (7 : Cov (R := R)) * P = 0 := by simpa using hEuler.symm
  have hseven' : (7 : Cov (R := R)) ≠ 0 := by
    simpa only [map_ofNat] using
      (MvPolynomial.C_ne_zero (σ := Fin 3) (a := (7 : R))).mpr hseven
  exact (mul_eq_zero.mp hmul).resolve_left hseven'

#print axioms finrank_ker_topCancellation_ge_34
#print axioms target_data_face_after_cancellation_green
#print axioms target_active_terms_have_90751_slack
#print axioms actual_ntt_locator_top_window_exact_arithmetic
#print axioms target_orderSeven_oneLayer_dimension_budget
#print axioms target_orderEight_oneLayer_dimension_budget
#print axioms no_surjective_single_high_active_channel
#print axioms weightedEuler_orderSevenCovariant
#print axioms eq_zero_of_weightedOrderSeven_gradient_zero

end

end ProximityPrize.SubmissionLower.K0OrderSevenBivariateApproximantDimension6900
