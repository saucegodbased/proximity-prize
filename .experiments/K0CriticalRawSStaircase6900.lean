import K0RawRSConnectionTranspose6900
import Mathlib.Data.Nat.Choose.Sum

/-!
# The critical raw-S staircase at contact order m

For one node, put

```text
W = u0 + u1 Z,
N = epsilon R - epsilon^2 S + epsilon^3 T,
V = W + N.
```

Since `epsilon` divides `N`, `epsilon^m` divides `(V-W)^m`.  Expanding the
last expression gives an exact relation between the first critical raw
column `Y^m S` and the complete causal staircase `Y^y S Z^z`, `y<m` and
`z<=m-y`.  This is the literal algebraic mechanism detected by the m5/m6
rank experiments; it is independent of any matrix-rank inference.
-/

namespace ProximityPrize.SubmissionLower.K0CriticalRawSStaircase6900

open scoped BigOperators
open K0RawRSConnectionTranspose6900

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

def seedPart (u0 u1 : K) : FlatContact K :=
  MvPolynomial.C u0 + MvPolynomial.C u1 * localZ

def nilpotentPart : FlatContact K :=
  eps * localR - eps ^ 2 * localS + eps ^ 3 * localT

theorem contactedY_eq_seedPart_add_nilpotentPart (u0 u1 : K) :
    contactedY (K := K) u0 u1 =
      seedPart u0 u1 + nilpotentPart := by
  simp [contactedY, seedPart, nilpotentPart]
  ring

theorem contactedY_sub_seedPart (u0 u1 : K) :
    contactedY (K := K) u0 u1 - seedPart u0 u1 =
      eps * (localR - eps * localS + eps ^ 2 * localT) := by
  simp [contactedY, seedPart]
  ring

/-- The contact-order reason the first new S relation occurs at Y-degree
exactly `m`. -/
theorem eps_pow_dvd_critical_nilpotent
    (u0 u1 : K) (m : Nat) :
    eps (K := K) ^ m ∣
      (contactedY u0 u1 - seedPart u0 u1) ^ m := by
  rw [contactedY_sub_seedPart]
  refine ⟨(localR - eps * localS + eps ^ 2 * localT) ^ m, ?_⟩
  rw [mul_pow]

def seedPowerExpansion (u0 u1 : K) (d : Nat) : FlatContact K :=
  ∑ z ∈ Finset.range (d + 1),
    (MvPolynomial.C u1 * localZ) ^ z *
      MvPolynomial.C u0 ^ (d - z) * (d.choose z : FlatContact K)

/-- Explicit expansion of `(u0+u1 Z)^d`; its Z degree is at most d. -/
theorem seedPowerExpansion_eq_pow (u0 u1 : K) (d : Nat) :
    seedPowerExpansion u0 u1 d = seedPart u0 u1 ^ d := by
  rw [seedPart, show
    MvPolynomial.C u0 + MvPolynomial.C u1 * localZ =
      MvPolynomial.C u1 * localZ + MvPolynomial.C u0 by ring, add_pow]
  unfold seedPowerExpansion
  rfl

/-- The entire lower-Y raw-S staircase which precedes `Y^m S`. -/
def criticalLowerStaircase
    (x u0 u1 : K) (a m : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * localS *
    ∑ y ∈ Finset.range m,
      (-1 : FlatContact K) ^ (y + m) * contactedY u0 u1 ^ y *
        seedPowerExpansion u0 u1 (m - y) * (m.choose y : FlatContact K)

/-- A compact version of the same lower staircase, before expanding powers
of `W=u0+u1Z`. -/
def criticalLowerTail
    (x u0 u1 : K) (a m : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * localS *
    ∑ y ∈ Finset.range m,
      (-1 : FlatContact K) ^ (y + m) *
        contactedY u0 u1 ^ y * seedPart u0 u1 ^ (m - y) *
        (m.choose y : FlatContact K)

theorem criticalLowerStaircase_eq_tail
    (x u0 u1 : K) (a m : Nat) :
    criticalLowerStaircase x u0 u1 a m =
      criticalLowerTail x u0 u1 a m := by
  unfold criticalLowerStaircase criticalLowerTail
  simp_rw [seedPowerExpansion_eq_pow]

/-- Exact binomial companion identity before using nilpotence. -/
theorem critical_raw_S_add_lower_eq_nilpotent
    (x u0 u1 : K) (a m : Nat) :
    rawContactColumn x u0 u1 a 1 m 0 0 +
        criticalLowerStaircase x u0 u1 a m =
      (MvPolynomial.C x + eps) ^ a * localS *
        (contactedY u0 u1 - seedPart u0 u1) ^ m := by
  rw [criticalLowerStaircase_eq_tail]
  unfold criticalLowerTail rawContactColumn
  rw [sub_pow, Finset.sum_range_succ]
  simp
  ring

/-- The critical raw S column is in the truncated contact span of the full
subcritical S staircase. -/
theorem eps_pow_dvd_critical_raw_S_relation
    (x u0 u1 : K) (a m : Nat) :
    eps (K := K) ^ m ∣
      rawContactColumn x u0 u1 a 1 m 0 0 +
        criticalLowerStaircase x u0 u1 a m := by
  rw [critical_raw_S_add_lower_eq_nilpotent]
  rcases eps_pow_dvd_critical_nilpotent u0 u1 m with ⟨Q, hQ⟩
  refine ⟨(MvPolynomial.C x + eps) ^ a * localS * Q, ?_⟩
  rw [hQ]
  ring

/-! ## Target legality of every causal lower band -/

theorem m47_critical_and_lower_staircase_legal
    (sCap L a y z : Nat) (hsCap : 1 ≤ sCap) (hL : 48 ≤ L)
    (ha : a < 2188005) (hy : y < 47) (hz : z ≤ 47 - y) :
    rawShapeLegal (47 * 180413) 131071 L 16 sCap 64 a 1 47 0 0 ∧
      rawShapeLegal (47 * 180413) 131071 L 16 sCap 64 a 1 y 0 z := by
  unfold rawShapeLegal
  norm_num at ha ⊢
  omega

theorem m47_critical_X_width :
    47 * 180413 - 47 * 131071 - (131071 - 2) = 2188005 := by
  norm_num

#print axioms eps_pow_dvd_critical_nilpotent
#print axioms seedPowerExpansion_eq_pow
#print axioms criticalLowerStaircase_eq_tail
#print axioms critical_raw_S_add_lower_eq_nilpotent
#print axioms eps_pow_dvd_critical_raw_S_relation
#print axioms m47_critical_and_lower_staircase_legal

end

end ProximityPrize.SubmissionLower.K0CriticalRawSStaircase6900
