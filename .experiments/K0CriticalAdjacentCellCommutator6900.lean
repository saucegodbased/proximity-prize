import K0CriticalTailTaperObstruction6900

/-!
# Exact adjacent-cell commutator for the critical raw-S packet

The node-local critical packet is `X_a * S * (V-W)^m`, where
`V=contactedY` and `W=u0+u1 Z`.  Its adjacent-Y packet is multiplication by
`V`, while its adjacent-Z packet is multiplication by `Z`.  Consequently
the combination

```text
nextY - u0 * base - u1 * nextZ
```

is multiplication by `V-W`, and gains one complete contact order.  This is
the literal PC commutator behind the observed interchangeability of the
second critical cell in the Y and Z directions.
-/

namespace ProximityPrize.SubmissionLower.K0CriticalAdjacentCellCommutator6900

open K0RawRSConnectionTranspose6900
open K0CriticalRawSStaircase6900
open K0CriticalRawSTwoSeedStaircase6900
open K0CriticalTailTaperObstruction6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

def criticalPacket
    (x u0 u1 : K) (a m : Nat) : FlatContact K :=
  rawContactColumn x u0 u1 a 1 m 0 0 +
    criticalLowerStaircase x u0 u1 a m

def criticalSeedPacket
    (x u0 u1 : K) (a m : Nat) : FlatContact K :=
  rawContactColumn x u0 u1 a 1 m 0 1 +
    criticalLowerStaircaseSeedShift x u0 u1 a m 1

def criticalNextYPacket
    (x u0 u1 : K) (a m : Nat) : FlatContact K :=
  rawContactColumn x u0 u1 a 1 (m + 1) 0 0 +
    criticalLowerStaircaseNextY x u0 u1 a m

theorem criticalPacket_eq_nilpotent
    (x u0 u1 : K) (a m : Nat) :
    criticalPacket x u0 u1 a m =
      (MvPolynomial.C x + eps) ^ a * localS *
        (contactedY u0 u1 - seedPart u0 u1) ^ m := by
  exact critical_raw_S_add_lower_eq_nilpotent x u0 u1 a m

theorem criticalSeedPacket_eq_base_mul_Z
    (x u0 u1 : K) (a m : Nat) :
    criticalSeedPacket x u0 u1 a m =
      criticalPacket x u0 u1 a m * localZ := by
  simp only [criticalSeedPacket, criticalPacket,
    criticalLowerStaircaseSeedShift, rawContactColumn, pow_one, add_mul]
  ring

theorem criticalNextYPacket_eq_base_mul_Y
    (x u0 u1 : K) (a m : Nat) :
    criticalNextYPacket x u0 u1 a m =
      criticalPacket x u0 u1 a m * contactedY u0 u1 := by
  simp only [criticalNextYPacket, criticalPacket,
    criticalLowerStaircaseNextY, rawContactColumn, pow_zero, mul_one,
    add_mul]
  ring

/-- Exact adjacent-cell commutator.  No rank, quotient, or selected contact
projection occurs in this identity. -/
theorem critical_adjacent_YZ_commutator
    (x u0 u1 : K) (a m : Nat) :
    criticalNextYPacket x u0 u1 a m -
        MvPolynomial.C u0 * criticalPacket x u0 u1 a m -
        MvPolynomial.C u1 * criticalSeedPacket x u0 u1 a m =
      criticalPacket x u0 u1 a m *
        (contactedY u0 u1 - seedPart u0 u1) := by
  rw [criticalNextYPacket_eq_base_mul_Y,
    criticalSeedPacket_eq_base_mul_Z]
  simp only [seedPart]
  ring

theorem critical_adjacent_YZ_commutator_eq_next_nilpotent
    (x u0 u1 : K) (a m : Nat) :
    criticalNextYPacket x u0 u1 a m -
        MvPolynomial.C u0 * criticalPacket x u0 u1 a m -
        MvPolynomial.C u1 * criticalSeedPacket x u0 u1 a m =
      (MvPolynomial.C x + eps) ^ a * localS *
        (contactedY u0 u1 - seedPart u0 u1) ^ (m + 1) := by
  rw [critical_adjacent_YZ_commutator,
    criticalPacket_eq_nilpotent]
  ring

/-- The adjacent-cell commutator gains one full contact order: it is killed
even modulo `epsilon^(m+1)`, rather than merely modulo `epsilon^m`. -/
theorem eps_pow_succ_dvd_critical_adjacent_YZ_commutator
    (x u0 u1 : K) (a m : Nat) :
    eps (K := K) ^ (m + 1) ∣
      criticalNextYPacket x u0 u1 a m -
        MvPolynomial.C u0 * criticalPacket x u0 u1 a m -
        MvPolynomial.C u1 * criticalSeedPacket x u0 u1 a m := by
  rw [critical_adjacent_YZ_commutator_eq_next_nilpotent,
    contactedY_sub_seedPart]
  refine ⟨(MvPolynomial.C x + eps) ^ a * localS *
      (localR - eps * localS + eps ^ 2 * localT) ^ (m + 1), ?_⟩
  rw [mul_pow]
  ring

/-! ## Exact anchor-quotient window split -/

/-- Strict X width of the one-unit-refunded mixed connector
`S * Y^46 * R`. -/
def criticalSYRConnectorWidth : Nat :=
  poleDegree - 131071 * 46 - 131070 - 131069

/-- The target widths expose exactly the `g-w-1` Newton-quotient tail.

* a degree-`<=w` anchor interpolant transports the whole `Y^48*S` window
  into the `Y^47*S` window;
* a full degree-`g-1` direction loses exactly `g-w-1=49341` multipliers;
* replacing one Y by R refunds the one extra degree in the anchor locator
  `E`, whose degree is `w+1`;
* after that refund the residual loss is `49340`, the largest possible
  degree of the quotient `T` in `Q-q=E*T`.
-/
theorem target_anchor_quotient_window_split :
    rawSYWidth 47 = 2188005 ∧
      rawSYWidth 48 = 2056934 ∧
      criticalSYRConnectorWidth = 2188006 ∧
      rawSYWidth 47 - 131071 = rawSYWidth 48 ∧
      rawSYWidth 48 - (rawSYWidth 47 - 180412) = 49341 ∧
      criticalSYRConnectorWidth - 131072 = rawSYWidth 48 ∧
      rawSYWidth 48 -
          (criticalSYRConnectorWidth - 180412) = 49340 := by
  norm_num [rawSYWidth, criticalSYRConnectorWidth, poleDegree]

/-- The precise mixed connector selected by the anchor split is legal in
the reduced-curvature target profile.  It was absent from the original
critical carrier predicate and is illegal in the m5/B2 controls, so neither
fact may be inferred from those older tests. -/
theorem m47_reduced_profile_critical_SYR_connector_legal
    (a z : Nat) (ha : a < 2188006) (hz : z ≤ 1) :
    rawShapeLegal (47 * 180413) 131071 5107 16 6 64
      a 1 46 1 z := by
  unfold rawShapeLegal
  norm_num at ha ⊢
  omega

#print axioms criticalPacket_eq_nilpotent
#print axioms criticalSeedPacket_eq_base_mul_Z
#print axioms criticalNextYPacket_eq_base_mul_Y
#print axioms critical_adjacent_YZ_commutator
#print axioms critical_adjacent_YZ_commutator_eq_next_nilpotent
#print axioms eps_pow_succ_dvd_critical_adjacent_YZ_commutator
#print axioms target_anchor_quotient_window_split
#print axioms m47_reduced_profile_critical_SYR_connector_legal

end


end ProximityPrize.SubmissionLower.K0CriticalAdjacentCellCommutator6900
