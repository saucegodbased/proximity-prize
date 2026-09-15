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

The final section records both the abstract weighted Euler identity and the
decisive compatible-boundary obstruction.  The actual probe evaluates at
`Y=U0+U1*Z`, hence at `J=0`.  On that locus the entire order-seven packet has
a nonzero annihilating covector and boundary rank at most three.  Thus the
degree-cancellation space is real, but it is RED as the required four-signal
rung.  Also, `H^37` supplies total order 44 only at agreement roots; at error
roots the packet has order seven.  Nothing below is an old-low-head kernel or
an endpoint theorem.
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

The 34-dimensional box above certifies a nonzero coefficient packet in the
top-cancellation kernel.  It is not large enough to prescribe one scalar
independently at all 81731 errors, and it cannot supply four boundary signals.
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

/-! ## Abstract faithfulness versus the actual compatible boundary -/

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

/-! The preceding formal-gradient injectivity is a polynomial identity.  It
does not imply rank four after evaluating at one point.  The literal probe
evaluates at `J=0`, where order seven has a uniform codimension-one
obstruction.  Coordinates below are `(dJ,dC1,dC2,dZ)`; the fourth entry stores
the contribution from differentiating a passive-Z coefficient. -/

abbrev Boundary4 (R : Type*) := Fin 4 -> R

def evalJZero (a b : R) (P : Cov (R := R)) : R :=
  MvPolynomial.eval ![0, a, b] P

def jZeroBasisJet
    (a b scale passiveSlope : R) (P : Cov (R := R)) : Boundary4 R := ![
  scale * evalJZero a b (MvPolynomial.pderiv 0 P),
  scale * evalJZero a b (MvPolynomial.pderiv 1 P),
  scale * evalJZero a b (MvPolynomial.pderiv 2 P),
  passiveSlope * evalJZero a b P]

/-- In covariant coordinates the row `(0,C1,-2*C2,0)` annihilates every
evaluated order-seven basis gradient at `J=0`, including the extra `dZ`
contribution from a passive coefficient. -/
def jZeroObstruction (a b : R) (v : Boundary4 R) : R :=
  a * v 1 - 2 * b * v 2

theorem jZeroObstruction_orderSevenCovariant
    (a b scale passiveSlope : R) (i : Fin 8) :
    jZeroObstruction a b
      (jZeroBasisJet a b scale passiveSlope
        (orderSevenCovariant (R := R) i)) = 0 := by
  fin_cases i <;>
    simp [jZeroObstruction, jZeroBasisJet, evalJZero,
      orderSevenCovariant, j, c1, c2] <;>
    ring

/-- Closed form of the entire evaluated packet.  `valueCoeff` is the value
of each coefficient polynomial at the fresh point and `zSlope` its passive-Z
derivative there.  Only three directions survive: one `dJ` axis, one fixed
`(dC1,dC2)` axis, and `dZ`. -/
def orderSevenJZeroBoundarySymbol
    (a b : R) (valueCoeff zSlope : Fin 8 -> R) : Boundary4 R := ![
  valueCoeff 3 * a ^ 3 + valueCoeff 7 * b ^ 2,
  2 * valueCoeff 6 * a * b,
  valueCoeff 6 * a ^ 2,
  zSlope 6 * a ^ 2 * b]

theorem jZeroObstruction_orderSevenJZeroBoundarySymbol
    (a b : R) (valueCoeff zSlope : Fin 8 -> R) :
    jZeroObstruction a b
      (orderSevenJZeroBoundarySymbol a b valueCoeff zSlope) = 0 := by
  simp [jZeroObstruction, orderSevenJZeroBoundarySymbol]
  ring

def orderSevenJZeroBoundaryMap
    {K : Type*} [Field K] (a b : K) :
    ((Fin 8 -> K) × (Fin 8 -> K)) →ₗ[K] Boundary4 K where
  toFun c := orderSevenJZeroBoundarySymbol a b c.1 c.2
  map_add' c d := by
    funext i
    fin_cases i <;> simp [orderSevenJZeroBoundarySymbol] <;> ring
  map_smul' q c := by
    funext i
    fin_cases i <;> simp [orderSevenJZeroBoundarySymbol] <;> ring

theorem jZeroObstruction_has_nonzero_value
    {K : Type*} [Field K]
    (a b : K) (h2 : (2 : K) ≠ 0) (hab : a ≠ 0 \/ b ≠ 0) :
    exists v : Boundary4 K, jZeroObstruction a b v ≠ 0 := by
  rcases hab with ha | hb
  · refine ⟨![0, 1, 0, 0], ?_⟩
    simpa [jZeroObstruction] using ha
  · refine ⟨![0, 0, 1, 0], ?_⟩
    have hneg2 : (-2 : K) ≠ 0 := neg_ne_zero.mpr h2
    simpa [jZeroObstruction] using mul_ne_zero hneg2 hb

/-- Consequently no linear map whose image obeys the actual order-seven
`J=0` obstruction can be onto the four boundary coordinates.  This STOP is
independent of the top-coefficient cancellation rank. -/
theorem not_surjective_of_orderSeven_JZero_obstruction
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a b : K) (h2 : (2 : K) ≠ 0) (hab : a ≠ 0 \/ b ≠ 0)
    (f : V →ₗ[K] Boundary4 K)
    (himage : ∀ v, jZeroObstruction a b (f v) = 0) :
    Not (Function.Surjective f) := by
  intro hsurj
  obtain ⟨target, htarget⟩ :=
    jZeroObstruction_has_nonzero_value a b h2 hab
  obtain ⟨v, hv⟩ := hsurj target
  apply htarget
  rw [← hv]
  exact himage v

/-- Full-stratum statement for the evaluated order-seven packet.  If at least
one of `C1,C2` is nonzero, the displayed covector obstructs surjectivity; if
both vanish, the entire symbol is zero. -/
theorem orderSevenJZeroBoundaryMap_not_surjective
    {K : Type*} [Field K] (a b : K) (h2 : (2 : K) ≠ 0) :
    Not (Function.Surjective (orderSevenJZeroBoundaryMap a b)) := by
  by_cases hab : a = 0 ∧ b = 0
  · intro hsurj
    obtain ⟨c, hc⟩ := hsurj ![1, 0, 0, 0]
    have hzero : orderSevenJZeroBoundaryMap a b c = 0 := by
      rcases hab with ⟨rfl, rfl⟩
      funext i
      fin_cases i <;> simp [orderSevenJZeroBoundaryMap,
        orderSevenJZeroBoundarySymbol]
    rw [hzero] at hc
    have := congrFun hc 0
    simpa using this
  · apply not_surjective_of_orderSeven_JZero_obstruction
      a b h2 (not_and_or.mp hab) (orderSevenJZeroBoundaryMap a b)
    intro c
    exact jZeroObstruction_orderSevenJZeroBoundarySymbol a b c.1 c.2

#print axioms finrank_ker_topCancellation_ge_34
#print axioms target_data_face_after_cancellation_green
#print axioms target_active_terms_have_90751_slack
#print axioms actual_ntt_locator_top_window_exact_arithmetic
#print axioms target_orderSeven_oneLayer_dimension_budget
#print axioms target_orderEight_oneLayer_dimension_budget
#print axioms no_surjective_single_high_active_channel
#print axioms weightedEuler_orderSevenCovariant
#print axioms eq_zero_of_weightedOrderSeven_gradient_zero
#print axioms jZeroObstruction_orderSevenCovariant
#print axioms jZeroObstruction_orderSevenJZeroBoundarySymbol
#print axioms not_surjective_of_orderSeven_JZero_obstruction
#print axioms orderSevenJZeroBoundaryMap_not_surjective

end

end ProximityPrize.SubmissionLower.K0OrderSevenBivariateApproximantDimension6900
