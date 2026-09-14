import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Partial-locator carriers and the reverse-seed mismatch block

This file records two algebraic identities used by the exact-`G`, `k=0`
lower-6900 investigation.  It does not assert the missing global contact
recurrence.
-/

namespace ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900

open Matrix Polynomial

set_option autoImplicit false
set_option Elab.async false

noncomputable section

/-! ## The exact partial/full carrier binomial transform -/

variable {S : Type*} [CommRing S]

/-- The carrier centered with the degree-`w` anchor interpolant. -/
def partialCarrier (H R A W T : S) (m k : Nat) : S :=
  H ^ (m - k) * R ^ m * (A + W * H * T) ^ k

/-- The carrier centered with the full agreement interpolant. -/
def fullCarrier (H R A : S) (m k : Nat) : S :=
  (H * R) ^ (m - k) * A ^ k

/-- Expanding `A_h = A_G + W H T` expresses every partial-locator carrier
as a binomial combination of full-agreement carriers.  The factors `R^r`
are exactly the source-width obstruction which prevents using the summands
individually at the strict cutoff. -/
theorem partialCarrier_eq_sum_fullCarrier
    (H R A W T : S) (m k : Nat) (hk : k <= m) :
    partialCarrier H R A W T m k =
      ∑ r ∈ Finset.range (k + 1),
        (k.choose r : S) * R ^ r * W ^ (k - r) * T ^ (k - r) *
          fullCarrier H R A m r := by
  rw [partialCarrier, add_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r <= k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hrm : r <= m := hrk.trans hk
  have hexpH : m - k + (k - r) = m - r := by omega
  have hexpR : r + (m - r) = m := Nat.add_sub_of_le hrm
  have hHpow : H ^ (m - k) * H ^ (k - r) = H ^ (m - r) := by
    rw [<- pow_add, hexpH]
  have hRpow : R ^ r * R ^ (m - r) = R ^ m := by
    rw [<- pow_add, hexpR]
  simp only [fullCarrier, mul_pow]
  calc
    H ^ (m - k) * R ^ m *
        (A ^ r * (W ^ (k-r) * H ^ (k-r) * T ^ (k-r)) *
          (k.choose r : S)) =
      (k.choose r : S) * W ^ (k-r) * T ^ (k-r) * A ^ r *
        (H ^ (m-k) * H ^ (k-r)) * R ^ m := by ring
    _ = (k.choose r : S) * W ^ (k-r) * T ^ (k-r) * A ^ r *
        H ^ (m-r) * R ^ m := by rw [hHpow]
    _ = (k.choose r : S) * R ^ r * W ^ (k-r) * T ^ (k-r) *
        (H ^ (m-r) * R ^ (m-r) * A ^ r) := by
      rw [<- hRpow]
      ring

/-! ## The two osculating companion changes -/

/-- First anchor-covariant companion. -/
def slopeCompanion (H H' A R : S) : S := H * R - H' * A

/-- Second anchor-covariant companion. -/
def curvatureCompanion (H H' H'' A R Q : S) : S :=
  H ^ 2 * Q - 2 * H * H' * R + (2 * H' ^ 2 - H * H'') * A

/-- If `Q_G-q_H=H*T`, changing from the full-centered to the anchor-centered
value and slope coordinates leaves only the covariant derivative `H^2*T'`.
-/
theorem slopeCompanion_fullCentering
    (H H' A R W T T' : S) :
    slopeCompanion H H' (A + W * H * T)
        (R + W * (H' * T + H * T')) =
      H * R - H' * A + W * H ^ 2 * T' := by
  simp only [slopeCompanion]
  ring

/-- The same cancellation through the second osculating companion. -/
theorem curvatureCompanion_fullCentering
    (H H' H'' A R Q W T T' T'' : S) :
    curvatureCompanion H H' H'' (A + W * H * T)
        (R + W * (H' * T + H * T'))
        (Q + W * (H'' * T + 2 * H' * T' + H * T'')) =
      H ^ 2 * Q - 2 * H * H' * R + (2 * H' ^ 2 - H * H'') * A +
        W * H ^ 3 * T'' := by
  simp only [curvatureCompanion]
  ring

/-- On the scalar quotient where the full-centered value, slope and
curvature coordinates vanish, the three anchor companions are respectively
`W*H*T`, `W*H^2*T'`, and `W*H^3*T''`. -/
theorem osculatingCompanions_at_fullScalarRoot
    (H H' H'' W T T' T'' : S) :
    slopeCompanion H H' (W * H * T)
        (W * (H' * T + H * T')) = W * H ^ 2 * T' ∧
      curvatureCompanion H H' H'' (W * H * T)
        (W * (H' * T + H * T'))
        (W * (H'' * T + 2 * H' * T' + H * T'')) =
          W * H ^ 3 * T'' := by
  constructor
  · simpa using slopeCompanion_fullCentering H H' 0 0 W T T'
  · simpa using curvatureCompanion_fullCentering H H' H'' 0 0 0 W T T' T''

/-! ## Reverse-seed Toeplitz block -/

variable {K : Type*} [Field K]

/-- Multiplication by `delta + epsilon*W`, projected from coefficients
`1,W,...,W^(n-1)` to the *next* coefficients `W,...,W^n`.  Factoring an
arbitrary common `W^z0` gives the identical matrix on any consecutive seed
interval `W^z0,...,W^(z0+n-1)`.

The `delta` entries are strictly above the diagonal and the mismatch
`epsilon` is the diagonal. -/
def reverseSeedToeplitz (delta epsilon : K) (n : Nat) :
    Matrix (Fin n) (Fin n) K :=
  fun i j =>
    if j < i then 0
    else if i = j then epsilon
    else if i.val + 1 = j.val then delta
    else 0

theorem reverseSeedToeplitz_blockTriangular
    (delta epsilon : K) (n : Nat) :
    (reverseSeedToeplitz delta epsilon n).BlockTriangular id := by
  intro i j hij
  change j < i at hij
  simp [reverseSeedToeplitz, hij]

theorem reverseSeedToeplitz_diagonal
    (delta epsilon : K) (n : Nat) (i : Fin n) :
    reverseSeedToeplitz delta epsilon n i i = epsilon := by
  simp [reverseSeedToeplitz]

/-- The local first-mismatch block contributes exactly a positive power of
the mismatch, independently of the nonzero value residual. -/
theorem reverseSeedToeplitz_det
    (delta epsilon : K) (n : Nat) :
    (reverseSeedToeplitz delta epsilon n).det = epsilon ^ n := by
  rw [Matrix.det_of_upperTriangular
    (reverseSeedToeplitz_blockTriangular delta epsilon n)]
  simp [reverseSeedToeplitz_diagonal]

theorem reverseSeedToeplitz_nonsingular
    (delta epsilon : K) (n : Nat) (hepsilon : epsilon ≠ 0) :
    IsUnit (reverseSeedToeplitz delta epsilon n) := by
  rw [Matrix.isUnit_iff_isUnit_det, reverseSeedToeplitz_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hepsilon)

/-! ## Target packet arithmetic and the exact scope of the count obstruction -/

/-- Number of legal unshifted-seed X coefficients in the full anchor
osculating packet.  Here `i` counts `a0`, `r` counts `a1`, `s` counts `a2`,
and `d=i+2r+3s` is anchor contact order. -/
def targetPacketTraceCoefficients : Nat :=
  ∑ s ∈ Finset.range 9,
    ∑ r ∈ Finset.range (17 - 2 * s),
      ∑ i ∈ Finset.Icc 0 (47 - 2 * r - 3 * s),
        (i + 2 * r + 3 * s)

theorem targetPacketTraceCoefficients_eq :
    targetPacketTraceCoefficients = 75888 := by
  decide

theorem targetPacketTraceCoefficients_lt_errors :
    targetPacketTraceCoefficients < 81731 := by
  rw [targetPacketTraceCoefficients_eq]
  norm_num

/-- Number of the same packet columns after allowing every centered external
seed shift `W^z` with `2 <= z <= 3757-(i+r+s)`.  Such shifts have zero first
boundary jet.  Unlike the unshifted count above, they can enter a translated
reverse-seed Toeplitz block and the finite-root passive quotient. -/
def targetPacketZeroBoundaryHigherSeedCoefficients : Nat :=
  ∑ s ∈ Finset.range 9,
    ∑ r ∈ Finset.range (17 - 2 * s),
      ∑ i ∈ Finset.Icc 0 (47 - 2 * r - 3 * s),
        (i + 2 * r + 3 * s) * (3757 - (i + r + s) - 1)

theorem targetPacketZeroBoundaryHigherSeedCoefficients_eq :
    targetPacketZeroBoundaryHigherSeedCoefficients = 283136910 := by
  decide

theorem target_errors_lt_zeroBoundaryHigherSeedCoefficients :
    81731 < targetPacketZeroBoundaryHigherSeedCoefficients := by
  rw [targetPacketZeroBoundaryHigherSeedCoefficients_eq]
  norm_num

/-- If one additionally omits the top possible seed degree, then every such
column has seed degree `< 3757` after expanding its `i+r+s` active factors.
This is the subpacket which automatically has zero infinity/leading-
coefficient trace at a matched error. -/
def targetPacketMatchedClearingHigherSeedCoefficients : Nat :=
  ∑ s ∈ Finset.range 9,
    ∑ r ∈ Finset.range (17 - 2 * s),
      ∑ i ∈ Finset.Icc 0 (47 - 2 * r - 3 * s),
        (i + 2 * r + 3 * s) * (3757 - (i + r + s) - 2)

theorem targetPacketMatchedClearingHigherSeedCoefficients_eq :
    targetPacketMatchedClearingHigherSeedCoefficients = 283061022 := by
  decide

theorem target_errors_lt_matchedClearingHigherSeedCoefficients :
    81731 < targetPacketMatchedClearingHigherSeedCoefficients := by
  rw [targetPacketMatchedClearingHigherSeedCoefficients_eq]
  norm_num

/-- The analogous *unshifted* packet count in the old exact-`G` `m=60`
profile.  The stronger restriction `r+2s <= 21` is used, so this is already
a literal subpacket of the old `r+s <= 21`, `s <= 10` source. -/
def oldM60PacketTraceCoefficients : Nat :=
  ∑ s ∈ Finset.range 11,
    ∑ r ∈ Finset.range (22 - 2 * s),
      ∑ i ∈ Finset.Icc 0 (60 - 2 * r - 3 * s),
        (i + 2 * r + 3 * s)

theorem oldM60PacketTraceCoefficients_eq :
    oldM60PacketTraceCoefficients = 197824 := by
  decide

theorem target_errors_lt_oldM60PacketTraceCoefficients :
    81731 < oldM60PacketTraceCoefficients := by
  rw [oldM60PacketTraceCoefficients_eq]
  norm_num

/-! A constant finite mismatch ratio makes all external seed shifts of one
base trace column scalar multiples.  Thus the large nominal higher-seed count
does not imply error-evaluation rank uniformly in the received data. -/

theorem constantRatio_seedShift_is_smul
    {E : Type*} (rho : K) (z : Nat) (v : E → K) :
    (fun x ↦ rho ^ z * v x) = rho ^ z • v := by
  rfl

/-- Adjacent anchor charts do not force their finite passive roots to vary.
If `q1-q0 = c*LambdaShared`, choosing `delta=LambdaShared` and
`u1-q0=a*LambdaShared` makes both ratios constant. -/
theorem anchorSwap_allows_two_constant_ratios
    {E : Type*} (lambdaShared : E → K)
    (hlambda : ∀ x, lambdaShared x ≠ 0)
    (a c : K) (ha : a ≠ 0) (hac : a - c ≠ 0) :
    let delta := lambdaShared
    let eta0 := fun x ↦ a * lambdaShared x
    let eta1 := fun x ↦ (a - c) * lambdaShared x
    (∀ x, eta1 x = eta0 x - c * lambdaShared x) ∧
      (∀ x, -(delta x) / eta0 x = -(1 / a)) ∧
      (∀ x, -(delta x) / eta1 x = -(1 / (a - c))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro x
    ring
  · intro x
    field_simp [ha, hlambda x]
  · intro x
    field_simp [hac, hlambda x]

/-! ## Constant-`T`, constant-ratio all-anchor collapse -/

/-- The scalar passive-quotient trace supplied by the preceding osculating
identity, after removing the common nonzero `Lambda_G^m` diagonal. -/
def scalarPacketTrace {E : Type*}
    (lambdaG node rho T T' T'' : E → K)
    (m i r s j z : Nat) : E → K :=
  fun x ↦ lambdaG x ^ m * node x ^ j * rho x ^ (z + i + r + s) *
    T x ^ i * T' x ^ r * T'' x ^ s

/-- The at-most-`m` trace frame left when `rho` and `T` are constant and
`T'=T''=0`. -/
def constantTTraceFrame {E : Type*}
    (lambdaG node : E → K) (m : Nat) (j : Fin m) : E → K :=
  fun x ↦ lambdaG x ^ m * node x ^ j.val

/-- Every legal scalar packet trace in the constant-`T`, constant-ratio
specialization lies in the span of the `m` functions
`Lambda_G^m, Lambda_G^m X, ..., Lambda_G^m X^(m-1)`.  If an `R/S`
companion occurs, its scalar trace is zero.  This is the formal core of the
all-anchor Hermite-surjectivity STOP. -/
theorem scalarPacketTrace_constantT_mem_mFrame
    {E : Type*} (lambdaG node : E → K) (rho c : K)
    (m i r s j z : Nat) (hj : j < m) :
    scalarPacketTrace lambdaG node (fun _ ↦ rho) (fun _ ↦ c)
        (fun _ ↦ 0) (fun _ ↦ 0) m i r s j z ∈
      Submodule.span K (Set.range (constantTTraceFrame lambdaG node m)) := by
  by_cases hrs : r + s = 0
  · have hr : r = 0 := by omega
    have hs : s = 0 := by omega
    subst r
    subst s
    have hframe : constantTTraceFrame lambdaG node m (⟨j, hj⟩ : Fin m) ∈
        Submodule.span K (Set.range (constantTTraceFrame lambdaG node m)) :=
      Submodule.subset_span (Set.mem_range_self (⟨j, hj⟩ : Fin m))
    have hscaled := (Submodule.span K
      (Set.range (constantTTraceFrame lambdaG node m))).smul_mem
        (rho ^ (z + i) * c ^ i) hframe
    have htrace : scalarPacketTrace lambdaG node (fun _ ↦ rho) (fun _ ↦ c)
        (fun _ ↦ 0) (fun _ ↦ 0) m i 0 0 j z =
          (rho ^ (z + i) * c ^ i) •
            constantTTraceFrame lambdaG node m (⟨j, hj⟩ : Fin m) := by
      funext x
      simp [scalarPacketTrace, constantTTraceFrame]
      ring
    rw [htrace]
    exact hscaled
  · have hpos : 0 < r ∨ 0 < s := by omega
    rcases hpos with hr | hs
    · have htrace : scalarPacketTrace lambdaG node (fun _ ↦ rho) (fun _ ↦ c)
          (fun _ ↦ 0) (fun _ ↦ 0) m i r s j z = 0 := by
        funext x
        simp [scalarPacketTrace, zero_pow (Nat.ne_of_gt hr)]
      rw [htrace]
      exact Submodule.zero_mem _
    · have htrace : scalarPacketTrace lambdaG node (fun _ ↦ rho) (fun _ ↦ c)
          (fun _ ↦ 0) (fun _ ↦ 0) m i r s j z = 0 := by
        funext x
        simp [scalarPacketTrace, zero_pow (Nat.ne_of_gt hs)]
      rw [htrace]
      exact Submodule.zero_mem _

theorem target_m47_frame_lt_errors : 47 < 81731 := by norm_num

theorem old_m60_frame_lt_errors : 60 < 81731 := by norm_num

/-! ## Why bounded X shifts cannot be literal single-error isolators -/

/-- A free X multiplier admitted by one fixed-seed packet shape has degree
`< d <= 47`.
If it vanishes at the other 81,730 error nodes, it is therefore the zero
polynomial and cannot remain nonzero at the selected error.  This only rules
out literal isolation by one bounded X multiplier; it does not rule out a
mixed-X/seed construction or a coupled determinant which uses the fixed
locator factors of many shapes. -/
theorem target_no_single_error_multiplier
    (otherErrors : Finset K) (hcard : otherErrors.card = 81730)
    (p : K[X]) (hdegree : p.natDegree < 47)
    (hzero : ∀ x ∈ otherErrors, p.eval x = 0) (selectedError : K) :
    p.eval selectedError = 0 := by
  have hdegree' : p.natDegree < otherErrors.card := by omega
  have hp : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      p otherErrors hzero hdegree'
  simp [hp]

theorem target_single_error_degree_gap : 47 < 81730 := by
  norm_num

end

end ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900

#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.partialCarrier_eq_sum_fullCarrier
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.osculatingCompanions_at_fullScalarRoot
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.reverseSeedToeplitz_det
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.targetPacketTraceCoefficients_lt_errors
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.target_errors_lt_zeroBoundaryHigherSeedCoefficients
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.target_errors_lt_matchedClearingHigherSeedCoefficients
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.target_errors_lt_oldM60PacketTraceCoefficients
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.anchorSwap_allows_two_constant_ratios
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.scalarPacketTrace_constantT_mem_mFrame
#print axioms ProximityPrize.SubmissionLower.K0PartialCarrierToeplitz6900.target_no_single_error_multiplier
