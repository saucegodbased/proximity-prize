import K0CriticalRawSStaircase6900

/-!
# The two-seed critical raw-S staircase

The robust exact-ratio controls need the consecutive critical bands
`Y^m*S` and `Y^m*S*Z`.  The node-local nilpotent identity is stable under
an arbitrary passive-seed shift.  This file records that literal identity
and checks the complete `z = 0,1` packet, including every lower companion,
against the target source inequalities.

This is a local/contact and source-legality theorem.  It does not identify
the node-dependent coefficients with one global tapered source vector.
-/

namespace ProximityPrize.SubmissionLower.K0CriticalRawSTwoSeedStaircase6900

open K0RawRSConnectionTranspose6900
open K0CriticalRawSStaircase6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- The lower critical staircase after a passive `Z^z` shift. -/
def criticalLowerStaircaseSeedShift
    (x u0 u1 : K) (a m z : Nat) : FlatContact K :=
  criticalLowerStaircase x u0 u1 a m * localZ ^ z

/-- Multiplying the critical nilpotent relation by any passive seed power
preserves order-`m` contact. -/
theorem eps_pow_dvd_critical_raw_S_seed_relation
    (x u0 u1 : K) (a m z : Nat) :
    eps (K := K) ^ m ∣
      rawContactColumn x u0 u1 a 1 m 0 z +
        criticalLowerStaircaseSeedShift x u0 u1 a m z := by
  have h := dvd_mul_of_dvd_left
    (eps_pow_dvd_critical_raw_S_relation x u0 u1 a m)
    (localZ (K := K) ^ z)
  simpa only [criticalLowerStaircaseSeedShift, rawContactColumn, pow_zero,
    mul_one, add_mul] using h

/-- In particular both critical bands observed in the robust controls have
literal order-`m` contact companions. -/
theorem eps_pow_dvd_critical_raw_S_two_seed_relations
    (x u0 u1 : K) (a m : Nat) :
    (∀ z : Fin 2,
      eps (K := K) ^ m ∣
        rawContactColumn x u0 u1 a 1 m 0 z.val +
          criticalLowerStaircaseSeedShift x u0 u1 a m z.val) := by
  intro z
  exact eps_pow_dvd_critical_raw_S_seed_relation x u0 u1 a m z.val

/-- The alternative adjacent critical cell observed in the exact controls.
Multiplying the first critical relation by the contacted raw `Y` gives a
relation headed by `Y^(m+1)*S`; its lower companions have Y degree at most
`m`, so the `Y^m*S` predecessor is genuinely part of the staircase. -/
def criticalLowerStaircaseNextY
    (x u0 u1 : K) (a m : Nat) : FlatContact K :=
  criticalLowerStaircase x u0 u1 a m * contactedY u0 u1

theorem eps_pow_dvd_critical_raw_S_next_Y_relation
    (x u0 u1 : K) (a m : Nat) :
    eps (K := K) ^ m ∣
      rawContactColumn x u0 u1 a 1 (m + 1) 0 0 +
        criticalLowerStaircaseNextY x u0 u1 a m := by
  have h := dvd_mul_of_dvd_left
    (eps_pow_dvd_critical_raw_S_relation x u0 u1 a m)
    (contactedY u0 u1)
  convert h using 1 <;>
    simp only [criticalLowerStaircaseNextY, rawContactColumn, pow_zero,
      mul_one, add_mul] <;>
    ring

/-- Every raw monomial in either target critical band and in its expanded
lower staircase is legal.  A lower term has seed exponent `zLower + zCrit`,
where `zLower <= 47-y` comes from expanding the seed part and `zCrit <= 1`
is the critical shift. -/
theorem m47_critical_two_seed_and_lower_staircase_legal
    (sCap L a y zLower zCrit : Nat)
    (hsCap : 1 ≤ sCap) (hL : 49 ≤ L)
    (ha : a < 2188005) (hy : y < 47)
    (hzLower : zLower ≤ 47 - y) (hzCrit : zCrit ≤ 1) :
    rawShapeLegal (47 * 180413) 131071 L 16 sCap 64
        a 1 47 0 zCrit ∧
      rawShapeLegal (47 * 180413) 131071 L 16 sCap 64
        a 1 y 0 (zLower + zCrit) := by
  unfold rawShapeLegal
  norm_num at ha ⊢
  omega

/-- The reduced-curvature target profile admits the whole two-seed packet. -/
theorem m47_reduced_profile_two_seed_packet_legal
    (a y zLower zCrit : Nat)
    (ha : a < 2188005) (hy : y < 47)
    (hzLower : zLower ≤ 47 - y) (hzCrit : zCrit ≤ 1) :
    rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        a 1 47 0 zCrit ∧
      rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        a 1 y 0 (zLower + zCrit) := by
  exact m47_critical_two_seed_and_lower_staircase_legal
    6 5107 a y zLower zCrit (by norm_num) (by norm_num)
      ha hy hzLower hzCrit

/-- The target `Y^48*S` band and every raw-Y multiple of a lower companion
fit the reduced profile at their common strict X width. -/
theorem m47_reduced_profile_next_Y_packet_legal
    (a y z : Nat) (ha : a < 2056934) (hy : y < 47)
    (hz : z ≤ 47 - y) :
    rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        a 1 48 0 0 ∧
      rawShapeLegal (47 * 180413) 131071 5107 16 6 64
        a 1 (y + 1) 0 z := by
  unfold rawShapeLegal
  norm_num at ha ⊢
  omega

theorem m47_next_Y_X_width :
    47 * 180413 - 48 * 131071 - (131071 - 2) = 2056934 := by
  norm_num

#print axioms eps_pow_dvd_critical_raw_S_seed_relation
#print axioms eps_pow_dvd_critical_raw_S_two_seed_relations
#print axioms eps_pow_dvd_critical_raw_S_next_Y_relation
#print axioms m47_critical_two_seed_and_lower_staircase_legal
#print axioms m47_reduced_profile_two_seed_packet_legal
#print axioms m47_reduced_profile_next_Y_packet_legal

end

end ProximityPrize.SubmissionLower.K0CriticalRawSTwoSeedStaircase6900
