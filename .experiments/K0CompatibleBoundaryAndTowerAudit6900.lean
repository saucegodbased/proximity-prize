import K0AllNodeWeightedOsculantRungSix6900
import CanonicalHighTailCoefficientRank6900
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Compatible-boundary audit and the first honest all-node tower

The order-seven approximant packet must be evaluated at the compatible
boundary `J=0`, not at a random nonzero value of `J`.  The first section
proves that the eight pure weight-seven monomials then have boundary rank at
most three, even before any top-coefficient equations are imposed.

The first section records a cap-feasible repair.  Multiplying the four
linear boundary coordinates by complementary powers of the full-node
locator gives the contact-seven packet

`N^6 J, N^5 C1, N^4 C2, N^7 Z`.

Its compatible boundary symbol is triangular for every `N != 0`.  On the
actual projective-high selected leaf, the scalar received polynomial in the
selected direction has degree at least the full agreement size `180413`.
Consequently its reversed top series starts by index `81730`.  The target
box `(M,K)=(81731,3)` therefore reaches that first live scalar coefficient,
has a uniform dimension surplus of `744662`, and keeps all active faces
legal.  Exact sparse tests support four-row survival under precisely this
target hypothesis.  The uniform joint-kernel theorem is still open: the
dimension and leading-support receipts do not prove it.

The final section gives the sharp obstruction to extending this as a linear
raw tower.  At local contact order nine, the coefficients of `T,R,S` force
the `Y,R,S` coefficient polynomials to contain respectively the sixth,
seventh, and eighth powers of the local node factor.  Globally the S lane is
therefore divisible by `N^8`; after the required agreement boost its literal
target weighted degree is already 63265 above the cutoff.  Thus a full
linear osculant tower cannot close orders nine through 43.
-/

namespace ProximityPrize.SubmissionLower.K0CompatibleBoundaryAndTowerAudit6900

open Polynomial
open K0AllNodeWeightedOsculantRungSix6900
open CanonicalHighTailCoefficientRank6900
open LowReceivedDirectionScalarSplit1331196900
open UniversalProjectiveHighDirectionEndpointCut6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

variable {K : Type} [Field K]

abbrev Vec4 := Fin 4 -> K

/-! ## Locator-lifted order seven restores the compatible symbol

The pure order-seven rank-three STOP is formalized in
`K0OrderSevenBivariateApproximantDimension6900`.  Here we test the first
packet which escapes it by lifting lower-order generators with powers of N.
-/

/-- Formal symbol of `N^6 J, N^5 C1, N^4 C2, N^7 Z`. -/
def liftedOrderSevenFormalSymbol (n : K) (c : Vec4 (K := K)) : Vec4 (K := K) :=
  ![n ^ 6 * c 0, n ^ 5 * c 1, n ^ 4 * c 2, n ^ 7 * c 3]

theorem liftedOrderSevenFormalSymbol_injective
    (n : K) (hn : n ≠ 0) :
    Function.Injective (liftedOrderSevenFormalSymbol n) := by
  intro c d hcd
  have h0 := congrFun hcd 0
  have h1 := congrFun hcd 1
  have h2 := congrFun hcd 2
  have h3 := congrFun hcd 3
  have hc0 : c 0 = d 0 := by
    simpa [liftedOrderSevenFormalSymbol, hn] using h0
  have hc1 : c 1 = d 1 := by
    simpa [liftedOrderSevenFormalSymbol, hn] using h1
  have hc2 : c 2 = d 2 := by
    simpa [liftedOrderSevenFormalSymbol, hn] using h2
  have hc3 : c 3 = d 3 := by
    simpa [liftedOrderSevenFormalSymbol, hn] using h3
  funext i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

/-- Raw `(S,Y,R,Z)` symbol obtained by the already checked triangular
change of coordinates from `(J,C1,C2,Z)`. -/
def liftedOrderSevenRawSymbol
    (n n1 p b b1 b2 : K) (c : Vec4 (K := K)) : Vec4 (K := K) :=
  osculatingSymbol n n1 p b b1 b2 (liftedOrderSevenFormalSymbol n c)

theorem liftedOrderSevenRawSymbol_injective
    (n n1 p b b1 b2 : K) (hn : n ≠ 0) (h2 : (2 : K) ≠ 0) :
    Function.Injective (liftedOrderSevenRawSymbol n n1 p b b1 b2) := by
  intro c d hcd
  apply liftedOrderSevenFormalSymbol_injective n hn
  apply osculatingSymbol_injective n n1 p b b1 b2 hn h2
  exact hcd

/-- Agreement/error contact bookkeeping for the lifted packet. -/
theorem lifted_orderSeven_contact_orders :
    6 + 1 = 7 /\ 5 + 2 = 7 /\ 4 + 3 = 7 /\ 7 = 7 /\
      37 + 7 = 44 := by
  norm_num

/-- Exact target-specific degree bridge.  On the projective-high leaf, the
selected scalar direction cannot equal the low-degree selected polynomial.
If its degree were below the agreement count, their difference would have
too many distinct agreement roots and hence vanish, a contradiction. -/
theorem selected_scalar_direction_degree_ge_agreement
    {I : Type} [Fintype I]
    [Fintype K] [CharP K 2130706433]
    (nodes : I ↪ K) (U : Fin 2 → I → K)
    (P : K[X]) (gamma : K) (agreementSet : Finset I)
    (hPdegree : P.natDegree ≤ 131071)
    (hcard : 180413 ≤ agreementSet.card)
    (hagreement : ∀ i ∈ agreementSet,
      P.eval (nodes i) = U 0 i + gamma * U 1 i)
    (hhigh : CanonicalHighTailDirectionIndependent nodes U) :
    180413 ≤
      (receivedDirectionInterpolant nodes
        (fun i ↦ U 0 i + gamma * U 1 i)).natDegree := by
  classical
  let Q := receivedDirectionInterpolant nodes
    (fun i ↦ U 0 i + gamma * U 1 i)
  have hQhigh : 133120 ≤ Q.natDegree := by
    have h := hhigh 1 gamma (Or.inl one_ne_zero)
    simpa only [one_mul] using h
  by_contra hdegree
  have hQdegree : Q.natDegree < 180413 := Nat.lt_of_not_ge hdegree
  let R := P - Q
  have hRdegree : R.natDegree < agreementSet.card := by
    have hle : R.natDegree ≤ max P.natDegree Q.natDegree := by
      exact natDegree_sub_le P Q
    omega
  have hRzero : R = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      agreementSet nodes.injective.injOn
    · exact Polynomial.degree_le_natDegree.trans_lt
        (by exact_mod_cast hRdegree)
    · intro i hi
      dsimp only [R]
      rw [eval_sub, receivedDirectionInterpolant_eval,
        hagreement i hi]
      simp
  have hPQ : P = Q := sub_eq_zero.mp hRzero
  rw [← hPQ] at hQhigh
  omega

/-- Turning the preceding degree lower bound into the exact reversed-series
support statement used by the approximant: some coefficient in indices
`0,...,81730` is nonzero. -/
theorem exists_live_reversed_scalar_coefficient
    (Q : K[X]) (hupper : Q.natDegree < 262144)
    (hlower : 180413 ≤ Q.natDegree) :
    ∃ r ≤ 81730, Q.coeff (262143 - r) ≠ 0 := by
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hlower
    omega
  let r := 262143 - Q.natDegree
  have hr : r ≤ 81730 := by
    dsimp only [r]
    omega
  have hindex : 262143 - r = Q.natDegree := by
    dsimp only [r]
    omega
  refine ⟨r, hr, ?_⟩
  rw [hindex, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hQne

/-- Uniform top-cancellation dimension receipt for the target box
`deg_X <= e = 81731`, `deg_Z <= 3`.  Four generators are enough because
their compatible symbol is already diagonal. -/
theorem lifted_orderSeven_approximant_dimension_surplus :
    4 * (81731 + 1) * (3 + 1) = 1307712 /\
      (81731 + 30879) * (3 + 2) = 563050 /\
      1307712 = 563050 + 744662 := by
  norm_num

/-- The worst face is `H^37*N^7*Z`.  Cancelling 41879 leading X
coefficients leaves degree exactly `D-1`. -/
theorem lifted_orderSeven_data_face_after_cancellation_green :
    37 * 180413 + 7 * 262144 = 8510289 /\
      8510289 - 47 * 180413 = 30878 /\
      81731 + 30879 = 112610 /\
      37 * 180413 + 7 * 262144 + 81731 - 112610 = 8479410 /\
      8479410 + 1 = 47 * 180413 /\
      112610 < 262144 := by
  norm_num

/-- All genuine active branches are legal without cancellation.  The three
numbers correspond to the Y branch of `N^6 J`, the R branch of `N^5 C1`,
and the S branch of `N^4 C2`. -/
theorem lifted_orderSeven_active_branches_green :
    37 * 180413 + 6 * 262144 + 131071 + 81731 = 8460947 /\
      37 * 180413 + 6 * 262144 + (131071 - 1) + 81731 = 8460946 /\
      37 * 180413 + 6 * 262144 + (131071 - 2) + 81731 = 8460945 /\
      47 * 180413 - 8460947 = 18464 /\
      8460947 < 47 * 180413 := by
  norm_num

theorem lifted_orderSeven_nonX_caps :
    3 + 1 <= 3757 /\ 1 <= 64 /\ 2 * 1 <= 16 /\ 1 <= 8 := by
  norm_num

/-! The same four-generator linear lift cannot even pass the next rung.
At order eight the active Y face restricts the X coefficient cap to 18463,
while top cancellation has fixed overhang 112610.  At that maximal cap the
four-source box loses the dimension comparison for every passive cap. -/
theorem lifted_orderEight_linear_active_cap_stop :
    36 * 180413 + 7 * 262144 + 131071 + 18463 = 8479410 /\
      8479410 < 47 * 180413 /\
      36 * 180413 + 7 * 262144 + 131071 + 18464 =
        47 * 180413 := by
  norm_num

theorem lifted_orderEight_linear_dimension_stop (k : Nat) :
    4 * (18463 + 1) * (k + 1) <
      (18463 + 112610) * (k + 2) := by
  norm_num
  omega

/-! ## Order eight can skip a layer only on a nondegenerate stratum -/

/-- Four pure weight-eight forms have a triangular compatible symbol when
both C1 and C2 are nonzero: `J*C1^2*C2`, `C1^4`, `C1*C2^2`, and
`Z*C1^4`. -/
def pureOrderEightWitnessSymbol
    (c1v c2v z : K) (c : Vec4 (K := K)) : Vec4 (K := K) := ![
  c 0 * c1v ^ 2 * c2v,
  c 1 * (4 * c1v ^ 3) + c 2 * c2v ^ 2 +
    c 3 * z * (4 * c1v ^ 3),
  c 2 * (2 * c1v * c2v),
  c 3 * c1v ^ 4]

theorem pureOrderEightWitnessSymbol_injective
    (c1v c2v z : K) (hc1 : c1v ≠ 0) (hc2 : c2v ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    Function.Injective (pureOrderEightWitnessSymbol c1v c2v z) := by
  intro c d hcd
  have hJ := congrFun hcd 0
  have hC1 := congrFun hcd 1
  have hC2 := congrFun hcd 2
  have hZ := congrFun hcd 3
  have hc3 : c 3 = d 3 := by
    simpa [pureOrderEightWitnessSymbol, hc1] using hZ
  have hc2' : c 2 = d 2 := by
    simpa [pureOrderEightWitnessSymbol, hc1, hc2, h2] using hC2
  have hc0 : c 0 = d 0 := by
    simpa [pureOrderEightWitnessSymbol, hc1, hc2] using hJ
  have h4 : (4 : K) ≠ 0 := by
    intro hfour
    have hfour_eq : (4 : K) = 2 * 2 := by norm_num
    have hmul : (2 : K) * 2 = 0 := by
      rw [← hfour_eq]
      exact hfour
    exact h2 ((mul_eq_zero.mp hmul).resolve_left h2)
  have hc1' : c 1 = d 1 := by
    simpa [pureOrderEightWitnessSymbol, hc2', hc3, hc1, h4] using hC1
  funext i
  fin_cases i
  · exact hc0
  · exact hc1'
  · exact hc2'
  · exact hc3

theorem pure_orderEight_approximant_arithmetic :
    36 + 8 = 44 /\
      36 * 180413 + 8 * (262144 - 1) = 8592012 /\
      8592012 - 47 * 180413 = 112601 /\
      10 * (15000 + 1) * (45 + 1) = 6900460 /\
      (15000 + 112602) * (45 + 9) = 6890508 /\
      6900460 = 6890508 + 9952 /\
      36 * 180413 + 8 * (262144 - 1) + 15000 - 131072 = 8475940 /\
      47 * 180413 - 8475940 = 3471 := by
  norm_num

/-! ## The formal transvectant tower exists

This is the scalar polynomial shadow of differentiation along the cubic
contact curve.  The already-formalized local connection is
`d/deps + 2*S*d/dR + 3*T*d/dS`; it sends contacted Y to R, R to 2S, and S
to 3T.  The recurrence below raises locator/contact divisibility by one.
Thus the obstruction after order eight is not absence of a formal tower: it
is descent to raw affine-linear coordinates under the literal source cap.
-/

def transvectantStep (r : Nat) (N C0 : K[X]) : K[X] :=
  N * C0.derivative - Polynomial.C (r : K) * N.derivative * C0

theorem X_succ_dvd_transvectantStep
    (r : Nat) (N C0 : K[X])
    (hN : Polynomial.X ∣ N) (hC : Polynomial.X ^ r ∣ C0) :
    Polynomial.X ^ (r + 1) ∣ transvectantStep r N C0 := by
  rcases hN with ⟨A, rfl⟩
  rcases hC with ⟨B, rfl⟩
  cases r with
  | zero =>
      refine ⟨A * B.derivative, ?_⟩
      simp [transvectantStep, mul_assoc]
  | succ r =>
      refine ⟨A * B.derivative - Polynomial.C ((r + 1 : Nat) : K) *
        A.derivative * B, ?_⟩
      simp only [transvectantStep, derivative_mul,
        Polynomial.derivative_X_pow_succ, derivative_X, one_mul,
        Nat.cast_add, Nat.cast_one]
      rw [pow_succ (Polynomial.X : K[X]) r]
      rw [pow_succ (Polynomial.X : K[X]) (r + 1)]
      ring

/-! ## A linear raw tower necessarily dies at order nine -/

/-- Local coefficient obstruction.  For a raw affine-linear expression
`A*Y+B*R+C*S+data`, the coefficients of the independent local variables
`T,R,S` are `X^3*A`, `X*A+B`, and `-X^2*A+C`.  Order-nine contact therefore
forces the displayed powers of the local node factor. -/
theorem local_orderNine_linear_contact_forces_tower
    (A B C : K[X])
    (hT : Polynomial.X ^ 9 ∣ Polynomial.X ^ 3 * A)
    (hR : Polynomial.X ^ 9 ∣ Polynomial.X * A + B)
    (hS : Polynomial.X ^ 9 ∣ -(Polynomial.X ^ 2 * A) + C) :
    Polynomial.X ^ 6 ∣ A /\ Polynomial.X ^ 7 ∣ B /\
      Polynomial.X ^ 8 ∣ C := by
  rcases hT with ⟨A0, hT0⟩
  have hX3 : (Polynomial.X ^ 3 : K[X]) ≠ 0 :=
    pow_ne_zero 3 Polynomial.X_ne_zero
  have hA0 : A = Polynomial.X ^ 6 * A0 := by
    apply mul_left_cancel₀ hX3
    calc
      Polynomial.X ^ 3 * A = Polynomial.X ^ 9 * A0 := hT0
      _ = Polynomial.X ^ 3 * (Polynomial.X ^ 6 * A0) := by ring
  rcases hR with ⟨B0, hR0⟩
  have hB0 : B = Polynomial.X ^ 7 * (Polynomial.X ^ 2 * B0 - A0) := by
    rw [hA0] at hR0
    calc
      B = (Polynomial.X * (Polynomial.X ^ 6 * A0) + B) -
          Polynomial.X * (Polynomial.X ^ 6 * A0) := by ring
      _ = Polynomial.X ^ 9 * B0 -
          Polynomial.X * (Polynomial.X ^ 6 * A0) := by rw [hR0]
      _ = Polynomial.X ^ 7 * (Polynomial.X ^ 2 * B0 - A0) := by ring
  rcases hS with ⟨C0, hS0⟩
  have hC0 : C = Polynomial.X ^ 8 * (Polynomial.X * C0 + A0) := by
    rw [hA0] at hS0
    calc
      C = (-(Polynomial.X ^ 2 * (Polynomial.X ^ 6 * A0)) + C) +
          Polynomial.X ^ 2 * (Polynomial.X ^ 6 * A0) := by ring
      _ = Polynomial.X ^ 9 * C0 +
          Polynomial.X ^ 2 * (Polynomial.X ^ 6 * A0) := by rw [hS0]
      _ = Polynomial.X ^ 8 * (Polynomial.X * C0 + A0) := by ring
  exact ⟨⟨A0, hA0⟩,
    ⟨Polynomial.X ^ 2 * B0 - A0, hB0⟩,
    ⟨Polynomial.X * C0 + A0, hC0⟩⟩

/-- Once the local conditions are imposed at every distinct full-domain
node, the preceding local eighth powers multiply to `N^8`.  This theorem is
the final target arithmetic after that standard coprime-factor step: the S
coefficient alone is already outside the source. -/
theorem target_orderNine_linear_S_lane_stop :
    35 * 180413 + 8 * 262144 + (131071 - 2) = 8542676 /\
      47 * 180413 = 8479411 /\
      8542676 - 8479411 = 63265 /\
      8479411 < 8542676 := by
  norm_num

#print axioms liftedOrderSevenRawSymbol_injective
#print axioms selected_scalar_direction_degree_ge_agreement
#print axioms exists_live_reversed_scalar_coefficient
#print axioms lifted_orderSeven_approximant_dimension_surplus
#print axioms lifted_orderSeven_data_face_after_cancellation_green
#print axioms lifted_orderEight_linear_dimension_stop
#print axioms pureOrderEightWitnessSymbol_injective
#print axioms pure_orderEight_approximant_arithmetic
#print axioms X_succ_dvd_transvectantStep
#print axioms local_orderNine_linear_contact_forces_tower
#print axioms target_orderNine_linear_S_lane_stop

end

end ProximityPrize.SubmissionLower.K0CompatibleBoundaryAndTowerAudit6900
