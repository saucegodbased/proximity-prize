import ProximityPrize.SubmissionLower.LowerGeometry
import K0SRTinyContactCore6900
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A literal order-44 weighted local ladder and its global locator cliff

The accepted `U/J/V` normal form contains genuinely shape-changing local
source vectors: after order 23, eight `U` factors replace sixteen outer
epsilon factors.  Their contact is exactly, rather than merely at least, the
requested epsilon order.  The first half of this file checks this at the
literal target caps.

These vectors are node-local normal forms.  They do not by themselves give
one global raw vector realizing independently translated forms at every
error.  The second half checks the standard way to globalize contact order,
namely a full-agreement partial-locator packet times powers of the error
locator.  Even granting the maximum order-44 osculating refund, the strict
target cutoff permits only error orders zero through six; order seven is
impossible.  Thus the local ladder is a genuine mechanism but not yet a
global schedule.
-/

namespace ProximityPrize.SubmissionLower.K0M44WeightedShapeSchedule6900

open Polynomial
open SecondJetBasis SecondJetSupport SecondJetLocal
open SecondJetWeightedBasis SecondJetWeightedContact
open SecondJetWeightedLocal SecondJetRelaxedSpace
open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

def zeroExponent : Fin 3 →₀ Nat := 0

/-- Below the shape change, the raw outer monomial has exactly its displayed
contact order. -/
theorem plain_weightedTerm_contact (r : Nat) :
    contact (K := K) (weightedTerm (K := K) r 0 0 0 zeroExponent) =
      (Polynomial.X : Target (K := K)) ^ r := by
  simp [weightedTerm, zeroExponent, family, U, J, V]

/-- Eight accepted `U` factors contribute exactly sixteen orders.  This is
the concrete high part of the order-44 schedule, not an order lower bound. -/
theorem eightU_weightedTerm_contact (r : Nat) :
    contact (K := K) (weightedTerm (K := K) r 0 8 0 zeroExponent) =
      (Polynomial.X : Target (K := K)) ^ (r + 16) *
        Polynomial.C (MvPolynomial.X (1 : Fin 4) ^ 8) := by
  have hu :
      contact (K := K)
          (Polynomial.C
              (Polynomial.C (MvPolynomial.X 0) -
                Polynomial.C (MvPolynomial.X 1)) +
            Polynomial.X * Polynomial.C Polynomial.X) =
        (Polynomial.X : Target (K := K)) ^ 2 *
          Polynomial.C (MvPolynomial.X (1 : Fin 4)) := by
    simpa only [SecondJetLocal.v, map_sub] using
      (contact_u (K := K))
  simp only [weightedTerm, zeroExponent, family, U, J, V,
    Finsupp.zero_apply, min_zero, Nat.zero_sub, pow_zero, one_mul,
    map_mul, map_pow, contact_X, contact_C_C]
  rw [hu]
  simp only [map_one, mul_one, Nat.sub_zero]
  rw [mul_pow]
  ring

/-- Every low rung `0 <= t < 24` is a literal member of the target local
source.  It uses the plain raw outer shape. -/
theorem plain_schedule_mem_target_source
    (t : Nat) (_ht : t < 24) :
    truncateOuter (K := K) 47
        (weightedTerm (K := K) t 0 0 0 zeroExponent) ∈
      source (K := K) 47 3757 16 8 64 (fun _ ↦ 64) := by
  apply truncated_weightedTerm_mem
  · simp [zeroExponent]
  · norm_num
  · norm_num [zeroExponent]
  · norm_num [zeroExponent]
  · norm_num [zeroExponent]
  · intro j hj hj'
    norm_num [zeroExponent]

/-- Every high rung `24 <= t <= 44` is a literal member of the same target
local source.  Its raw shape changes to `epsilon^(t-16) U^8`; the side
condition `8 <= t-16` is exactly why the switch occurs at 24. -/
theorem eightU_schedule_mem_target_source
    (t : Nat) (htlo : 24 ≤ t) (hthi : t ≤ 44) :
    truncateOuter (K := K) 47
        (weightedTerm (K := K) (t - 16) 0 8 0 zeroExponent) ∈
      source (K := K) 47 3757 16 8 64 (fun _ ↦ 64) := by
  apply truncated_weightedTerm_mem
  · simp [zeroExponent]
    omega
  · norm_num
  · norm_num [zeroExponent]
  · norm_num [zeroExponent]
  · norm_num [zeroExponent]
  · intro j hj hj'
    norm_num [zeroExponent]

/-- The high-rung shape has exactly order `t`; in particular this produces
an explicit local order-44 vector without accumulating 44 coefficient jets. -/
theorem eightU_schedule_contact
    (t : Nat) (htlo : 16 ≤ t) :
    contact (K := K)
        (weightedTerm (K := K) (t - 16) 0 8 0 zeroExponent) =
      (Polynomial.X : Target (K := K)) ^ t *
        Polynomial.C (MvPolynomial.X (1 : Fin 4) ^ 8) := by
  rw [eightU_weightedTerm_contact]
  congr 2
  omega

theorem target_order44_weighted_shape_mem :
    truncateOuter (K := K) 47
        (weightedTerm (K := K) 28 0 8 0 zeroExponent) ∈
      source (K := K) 47 3757 16 8 64 (fun _ ↦ 64) := by
  exact eightU_schedule_mem_target_source (K := K) 44 (by norm_num) (by norm_num)

theorem target_order44_weighted_shape_contact :
    contact (K := K) (weightedTerm (K := K) 28 0 8 0 zeroExponent) =
      (Polynomial.X : Target (K := K)) ^ 44 *
        Polynomial.C (MvPolynomial.X (1 : Fin 4) ^ 8) := by
  simpa using eightU_schedule_contact (K := K) 44 (by norm_num)

/-! ## Full-agreement partial-locator globalization cliff -/

def targetG : Nat := 180413
def targetE : Nat := 81731
def targetD : Nat := 47 * targetG

/-- Top weighted degree of an order-44 agreement packet with osculating
contact weight `d`, after multiplying by the `t`th power of the complete
error locator.  The best possible packet has `d=44`; external X shifts only
increase this number and are therefore omitted. -/
def globalizedPacketWeight (t d : Nat) : Nat :=
  44 * targetG - d + t * targetE

/-- A concrete maximal-refund osculating shape is
`A^41 * B2`: its agreement contact weight is `41 + 3 = 44`, its active
degree is 42, and it stays far inside every non-X target cap. -/
theorem maximal_refund_A41B2_caps :
    41 + 3 = 44 ∧
      41 + 1 ≤ 64 ∧
      2 * 1 + 0 ≤ 16 ∧
      1 ≤ 8 ∧
      41 + 1 ≤ 3757 := by
  norm_num

/-- The genuinely shape-changing prefix through error order six fits even
without taking any osculating refund (`d=0`). -/
theorem globalized_partial_locator_prefix_through_six_fits
    (t d : Nat) (ht : t ≤ 6) (hd : d ≤ 44) :
    globalizedPacketWeight t d < targetD := by
  simp [globalizedPacketWeight, targetD, targetG, targetE]
  omega

/-- Order seven misses the strict cutoff even after granting the largest
possible osculating refund `d=44`.  Hence no standard order-44 partial-
locator packet times an error-locator power reaches the seventh equation. -/
theorem globalized_partial_locator_order_seven_is_illegal
    (d : Nat) (hd : d ≤ 44) :
    targetD ≤ globalizedPacketWeight 7 d := by
  simp [globalizedPacketWeight, targetD, targetG, targetE]
  omega

theorem target_partial_locator_cliff_exact :
    targetD - globalizedPacketWeight 6 0 = 50853 ∧
      globalizedPacketWeight 7 44 - targetD = 30834 := by
  norm_num [globalizedPacketWeight, targetD, targetG, targetE]

/-- The four boosted descendants of the original boundary carriers may be
taken with internal contact weights `(42,43,44,41)`, corresponding to
`H^2*A^42`, `H*A^41*B1`, `A^41*B2`, and `H^3*A^41*W`.  All four reach the
sixth error equation with about fifty thousand coefficients of slack, and
all four fail the seventh by more than thirty thousand. -/
theorem boosted_four_carrier_exact_cliff :
    targetD - globalizedPacketWeight 6 42 = 50895 ∧
      targetD - globalizedPacketWeight 6 43 = 50896 ∧
      targetD - globalizedPacketWeight 6 44 = 50897 ∧
      targetD - globalizedPacketWeight 6 41 = 50894 ∧
      globalizedPacketWeight 7 42 - targetD = 30836 ∧
      globalizedPacketWeight 7 43 - targetD = 30835 ∧
      globalizedPacketWeight 7 44 - targetD = 30834 ∧
      globalizedPacketWeight 7 41 - targetD = 30837 := by
  norm_num [globalizedPacketWeight, targetD, targetG, targetE]

#print axioms plain_weightedTerm_contact
#print axioms eightU_weightedTerm_contact
#print axioms plain_schedule_mem_target_source
#print axioms eightU_schedule_mem_target_source
#print axioms target_order44_weighted_shape_contact
#print axioms globalized_partial_locator_prefix_through_six_fits
#print axioms globalized_partial_locator_order_seven_is_illegal
#print axioms target_partial_locator_cliff_exact
#print axioms boosted_four_carrier_exact_cliff

end

end ProximityPrize.SubmissionLower.K0M44WeightedShapeSchedule6900
