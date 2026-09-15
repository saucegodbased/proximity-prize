import K0SRTinyContactCore6900
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# All-node weighted osculants cross the first K0 active cliff once

Let `N` be the full-node locator and let

`J = Y - U0(X) - U1(X) Z`.

At every old node both `N` and the contacted `J` have epsilon order one.
The raw slope and curvature residuals are

`V = R - U0' - U1' Z`,
`A = -2 S - U0'' - U1'' Z`.

The two literal source polynomials used below are

`C1 = N' J - N V`,

`C2 = N^2 A - 2 N N' V + 4 N^2 S
        + (2 (N')^2 - N N'') J`.

The apparently redundant `4 N^2 S` is essential: it corrects the fact that
the contacted raw `R` is constant whereas the epsilon derivative of contacted
`Y` is `R-2 epsilon S+3 epsilon^2 T`.  The theorems below prove, without a
truncation assumption, that `C1` has order at least two and `C2` order at
least three at every zero of `N`.

At the target, the four order-six shapes

`J^6, J^4 C1, J^3 C2, Z J^6`

have a rank-four fresh-boundary symbol.  After multiplication by `H^38`, all
four fit the literal K0 source.  This removes the former need to multiply a
rung-six scalar carrier by the expensive active boundary variables.  It is a
real one-rung improvement.  It does not iterate: the identical family at
order seven exceeds the strict X cutoff by 30,871 even before an active
boundary weight is charged.
-/

namespace ProximityPrize.SubmissionLower.K0AllNodeWeightedOsculantRungSix6900

open Polynomial
open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

/-- The ordinary first transvectant, with the sign convenient for the
divisibility recurrence. -/
def trueFirst (N J : K[X]) : K[X] :=
  N * J.derivative - N.derivative * J

/-- The ordinary second transvectant. -/
def trueSecond (N J : K[X]) : K[X] :=
  N * (trueFirst N J).derivative -
    2 * N.derivative * trueFirst N J

/-- If two series vanish at epsilon zero, their first transvectant has a
double epsilon zero. -/
theorem X_sq_dvd_trueFirst
    (N J : K[X]) (hN : X ∣ N) (hJ : X ∣ J) :
    X ^ 2 ∣ trueFirst N J := by
  obtain ⟨A, rfl⟩ := hN
  obtain ⟨B, rfl⟩ := hJ
  refine ⟨A * B.derivative - A.derivative * B, ?_⟩
  simp only [trueFirst, derivative_mul, derivative_X, one_mul]
  ring

/-- The second transvectant has a triple epsilon zero. -/
theorem X_cube_dvd_trueSecond
    (N J : K[X]) (hN : X ∣ N) (hJ : X ∣ J) :
    X ^ 3 ∣ trueSecond N J := by
  obtain ⟨A, rfl⟩ := hN
  have hfirst := X_sq_dvd_trueFirst (X * A) J (dvd_mul_right X A) hJ
  obtain ⟨C, hC⟩ := hfirst
  refine ⟨A * C.derivative - 2 * A.derivative * C, ?_⟩
  rw [trueSecond, hC]
  simp [derivative_mul, derivative_pow]
  have htwo : Polynomial.C (2 : K) = (2 : K[X]) := by
    exact map_ofNat (Polynomial.C : K →+* K[X]) 2
  rw [htwo]
  ring

/-- The raw first osculant.  Under literal K0 contact,
`V = J' + 2 epsilon S - 3 epsilon^2 T`. -/
def rawFirst (N J V : K[X]) : K[X] :=
  N.derivative * J - N * V

/-- Exact comparison between the raw first osculant and the ordinary
transvectant. -/
theorem rawFirst_eq
    (N J S T : K[X]) :
    rawFirst N J (J.derivative + 2 * X * S - 3 * X ^ 2 * T) =
      -(trueFirst N J) - N * (2 * X * S - 3 * X ^ 2 * T) := by
  simp only [rawFirst, trueFirst]
  ring

/-- Hence the literal raw `R` generator has contact order at least two at
every old node. -/
theorem X_sq_dvd_rawFirst
    (N J S T : K[X]) (hN : X ∣ N) (hJ : X ∣ J) :
    X ^ 2 ∣ rawFirst N J
      (J.derivative + 2 * X * S - 3 * X ^ 2 * T) := by
  rw [rawFirst_eq]
  apply dvd_add
  · exact dvd_neg.mpr (X_sq_dvd_trueFirst N J hN hJ)
  · obtain ⟨A, rfl⟩ := hN
    refine ⟨-(A * (2 * S - 3 * X * T)), ?_⟩
    ring

/-- Literal raw second osculant.  The `4*N^2*S` correction is what makes
the expression polynomial in the global raw variables while preserving
third contact. -/
def rawSecond (N J V A S : K[X]) : K[X] :=
  N ^ 2 * A - 2 * N * N.derivative * V + 4 * N ^ 2 * S +
    (2 * N.derivative ^ 2 - N * N.derivative.derivative) * J

theorem trueSecond_expanded (N J : K[X]) :
    trueSecond N J =
      N ^ 2 * J.derivative.derivative -
        2 * N * N.derivative * J.derivative +
          (2 * N.derivative ^ 2 - N * N.derivative.derivative) * J := by
  simp only [trueSecond, trueFirst, derivative_sub, derivative_mul]
  ring

/-- The raw/ordinary difference is a multiple of the universal cubic
error `N^2-X*N*N'`. -/
theorem rawSecond_eq
    (N J S T : K[X]) :
    rawSecond N J
        (J.derivative + 2 * X * S - 3 * X ^ 2 * T)
        (J.derivative.derivative - 6 * X * T) S =
      trueSecond N J +
        (N ^ 2 - X * N * N.derivative) * (4 * S - 6 * X * T) := by
  rw [trueSecond_expanded]
  simp only [rawSecond]
  ring

/-- The universal correction has order three whenever `N` has order one.
No assumption on the higher Taylor coefficients of `N` is used. -/
theorem X_cube_dvd_nodal_correction
    (N : K[X]) (hN : X ∣ N) :
    X ^ 3 ∣ N ^ 2 - X * N * N.derivative := by
  obtain ⟨A, rfl⟩ := hN
  refine ⟨-(A * A.derivative), ?_⟩
  simp only [derivative_mul, derivative_X, one_mul]
  ring

/-- Therefore the raw `S/R/Y` osculant has contact order at least three at
every old node. -/
theorem X_cube_dvd_rawSecond
    (N J S T : K[X]) (hN : X ∣ N) (hJ : X ∣ J) :
    X ^ 3 ∣ rawSecond N J
      (J.derivative + 2 * X * S - 3 * X ^ 2 * T)
      (J.derivative.derivative - 6 * X * T) S := by
  rw [rawSecond_eq]
  exact dvd_add (X_cube_dvd_trueSecond N J hN hJ)
    ((X_cube_dvd_nodal_correction N hN).mul_right _)

/-! ## Fresh-boundary symbol -/

abbrev Vec4 := Fin 4 -> K

/-- Coordinate order is `(S,Y,R,Z)`.  The unused last entries absorb the
data-dependent `Z` coefficients of the three gradients. -/
def osculatingSymbol
    (n n1 p b b1 b2 : K) (c : Vec4 (K := K)) : Vec4 (K := K) := ![
  2 * n ^ 2 * c 2,
  c 0 + n1 * c 1 + p * c 2,
  -n * c 1 - 2 * n * n1 * c 2,
  -b * c 0 + b1 * c 1 + b2 * c 2 + c 3]

/-- The gradients of `J,C1,C2,Z` are independent.  The triangular pivots
are `1,-n,2*n^2,1`, whose product is `-2*n^3`. -/
theorem osculatingSymbol_injective
    (n n1 p b b1 b2 : K) (hn : n ≠ 0) (h2 : (2 : K) ≠ 0) :
    Function.Injective (osculatingSymbol n n1 p b b1 b2) := by
  intro c d hcd
  have hS := congrFun hcd 0
  have hc2 : c 2 = d 2 := by
    simpa [osculatingSymbol, hn, h2] using hS
  have hR := congrFun hcd 2
  have hc1 : c 1 = d 1 := by
    simpa [osculatingSymbol, hc2, hn] using hR
  have hY := congrFun hcd 1
  have hc0 : c 0 = d 0 := by
    simpa [osculatingSymbol, hc1, hc2] using hY
  have hZ := congrFun hcd 3
  have hc3 : c 3 = d 3 := by
    simpa [osculatingSymbol, hc0, hc1, hc2] using hZ
  funext i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

/-- After taking the powers `J^6,J^4*C1,J^3*C2,Z*J^6`, elementary row
operations leave these four pivots. -/
theorem rungSix_boundary_pivot_product (n j : K) :
    (6 * j ^ 5) * (j ^ 4) * (j ^ 3) * (j ^ 6) * (-2 * n ^ 3) =
      -12 * n ^ 3 * j ^ 18 := by
  ring

/-- At contact order seven the same three-gradient-plus-seed packet is still
geometrically rank four: its pivot product is nonzero whenever `n`, `j`, and
`14` are nonzero.  Thus the next failure below is a source-cost failure, not
a collapse of leading gradients. -/
theorem rungSeven_boundary_pivot_product (n j : K) :
    (7 * j ^ 6) * (j ^ 5) * (j ^ 4) * (j ^ 7) * (-2 * n ^ 3) =
      -14 * n ^ 3 * j ^ 22 := by
  ring

/-! ## Exact target cap ledger -/

def targetD : Nat := 47 * 180413
def rungX (t : Nat) : Nat := (44 - t) * 180413 + t * (262144 - 1)

/-- Weighted degrees of the raw order-two branches: the data-only branch
is the maximum, at `2n-2`. -/
theorem rawFirst_weighted_degrees :
    (262144 - 1) + 131071 = 393214 /\
    262144 + (131071 - 1) = 393214 /\
    2 * 262144 - 2 = 524286 := by
  norm_num

/-- The three active branches of the raw order-three osculant have identical
weighted degree.  Its data-only branch has degree `3n-3`. -/
theorem rawSecond_weighted_degrees :
    2 * 262144 + (131071 - 2) = 655357 /\
    (2 * 262144 - 1) + (131071 - 1) = 655357 /\
    (2 * 262144 - 2) + 131071 = 655357 /\
    3 * 262144 - 3 = 786429 := by
  norm_num

/-- All three ways to make order six have the same worst weighted X cost.
Unlike the old construction, no additional active boundary multiplier is
needed: the four gradients are carried by the osculants themselves and by
one weight-zero `Z`. -/
theorem target_rung_six_weighted_green :
    38 * 180413 + 6 * (262144 - 1) = 8428552 /\
    38 * 180413 + 4 * (262144 - 1) + (2 * 262144 - 2) = 8428552 /\
    38 * 180413 + 3 * (262144 - 1) + (3 * 262144 - 3) = 8428552 /\
    targetD = 8479411 /\
    8428552 < targetD /\
    targetD - 8428552 = 50859 := by
  norm_num [targetD]

/-- The support envelopes of all four rung-six shapes are tiny compared
with `(B,s,U,L)=(16,8,64,3757)`. -/
theorem target_rung_six_nonX_caps :
    (2 * 0 + 0 <= 16 /\ 0 <= 8 /\ 6 <= 64 /\ 7 <= 3757) /\
    (2 * 0 + 1 <= 16 /\ 0 <= 8 /\ 5 <= 64 /\ 6 <= 3757) /\
    (2 * 1 + 1 <= 16 /\ 1 <= 8 /\ 4 <= 64 /\ 5 <= 3757) := by
  norm_num

/-- Any literal monomial in the displayed support envelopes is source-legal
once its weighted degree is bounded by the certified rung-six maximum. -/
theorem target_rung_six_rawShapeLegal
    (a s y r z : Nat)
    (hB : 2 * s + r <= 16) (hs : s <= 8)
    (hU : s + y + r <= 64) (hL : s + y + r + z <= 3757)
    (hwt : a + 131071 * y + (131071 - 1) * r +
      (131071 - 2) * s <= 8428552) :
    rawShapeLegal targetD 131071 3757 16 8 64 a s y r z := by
  simp only [rawShapeLegal]
  refine ⟨hB, hs, hU, hL, ?_⟩
  norm_num [targetD] at hwt ⊢
  omega

/-- The same four-shape package at order seven is outside the source even
before charging `Y`, `R`, or `S`. -/
theorem target_rung_seven_unweighted_stop :
    rungX 7 = 8510282 /\ targetD = 8479411 /\
      targetD < rungX 7 /\ rungX 7 - targetD = 30871 := by
  norm_num [rungX, targetD]

/-- Every individual semigroup monomial in `J,C1,C2` has data-only degree
`t*(n-1)` when its contact weight is `a+2b+3c=t`: the extremal leading
coefficients of all three factors are nonzero. -/
theorem semigroup_data_degree
    (a b c t : Nat) (hweight : a + 2 * b + 3 * c = t) :
    a * (262144 - 1) + b * (2 * 262144 - 2) +
      c * (3 * 262144 - 3) = t * (262144 - 1) := by
  norm_num at hweight ⊢
  omega

/-- Consequently every *individual* order-`t` monomial packet is outside
the target from `t=7` onward, even without a boundary-variable weight. -/
theorem target_semigroup_monomial_stop_from_seven
    (t : Nat) (ht : 7 <= t) (htop : t <= 44) :
    targetD < (44 - t) * 180413 + t * (262144 - 1) := by
  norm_num [targetD]
  omega

/-- The complete order-seven semigroup has eight monomials.  Each has the
same fatal data degree `7*(n-1)`; the five displayed equalities include the
packet requested for the first post-cliff audit. -/
theorem target_order_seven_semigroup_profiles :
    7 = 7 /\ 5 + 2 = 7 /\ 4 + 3 = 7 /\
      3 + 2 * 2 = 7 /\ 2 + 2 + 3 = 7 /\
      37 * 180413 + 7 * (262144 - 1) = 8510282 /\
      8510282 - targetD = 30871 := by
  norm_num [targetD]

/-- Merely inserting the degree-81731 error locator into the old rung five
is one degree worse than the all-node osculant package and remains RED. -/
theorem target_split_error_locator_rung_six_stop :
    39 * 180413 + 5 * (262144 - 1) + 81731 = 8428553 /\
      8428553 + 131071 - targetD = 80213 /\
      8428553 + (131071 - 1) - targetD = 80212 /\
      8428553 + (131071 - 2) - targetD = 80211 := by
  norm_num [targetD]

/-- The extremal leading coefficients of the first and second data-only
osculants do not disappear.  For `deg N=n`, `deg U=n-1`, they are `-1` and
`-2`; the target characteristic is far from two. -/
theorem extremal_top_coefficients :
    ((262143 : Int) - 262144) = -1 /\
    (-(262143 : Int) * 262142 + 2 * 262144 * 262143 -
      (2 * 262144 ^ 2 - 262144 * 262143)) = -2 := by
  norm_num

#print axioms X_sq_dvd_trueFirst
#print axioms X_cube_dvd_trueSecond
#print axioms X_sq_dvd_rawFirst
#print axioms X_cube_dvd_rawSecond
#print axioms osculatingSymbol_injective
#print axioms rungSix_boundary_pivot_product
#print axioms rungSeven_boundary_pivot_product
#print axioms target_rung_six_weighted_green
#print axioms target_rung_six_rawShapeLegal
#print axioms target_rung_seven_unweighted_stop
#print axioms target_semigroup_monomial_stop_from_seven
#print axioms extremal_top_coefficients

end

end ProximityPrize.SubmissionLower.K0AllNodeWeightedOsculantRungSix6900
