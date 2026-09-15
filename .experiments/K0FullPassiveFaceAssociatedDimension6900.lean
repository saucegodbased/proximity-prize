import K0RawOneAssociatedFace6900
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Full last-passive-face associated dimension at lower 6900

For a cap-face monomial `X^a S^s Y^y R^r Z^z`, the top passive-degree
piece of its literal contact is

`(x+epsilon)^a S^s
  (u1 Z + epsilon R - epsilon^2 S + epsilon^3 T)^y R^r Z^z`.

The first theorem below records this identity without suppressing any of the
formal `S,T,R,Z` channels.  The numerical section then isolates the exact
dimension statement for the complete `3758 \\ 3757` face.  It deliberately
keeps the two remaining bridges as hypotheses:

* the associated map must have rank at most the published local face cap;
* an associated-kernel vector must still be lifted/corrected through all
  lower passive grades to give a complete contact relation.

Thus the `23,088,879` is a genuine associated-grade dimension surplus once
the filtration-compatible local cap is supplied, but it is not by itself a
complete-contact or boundary-separation theorem.
-/

namespace ProximityPrize.SubmissionLower.K0FullPassiveFaceAssociatedDimension6900

open scoped BigOperators
open ProximityPrize.SubmissionLower.K0SRTinyContactCore6900
open ProximityPrize.SubmissionLower.K0RawOneAssociatedFace6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-! ## Exact associated-face contact identity -/

def fullAssociatedFaceColumn
    (x u1 : K) (a s y r z : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * localS ^ s *
    contactedDirection u1 ^ y * localR ^ r * localZ ^ z

/-- Exact binomial splitting by passive degree.  In the summand indexed by
`j`, exactly `j` copies of the constant `u0` have been selected, so its
passive degree is `s+r+z+(y-j)`.  Hence the unique top-degree summand is
`j=0`, namely `fullAssociatedFaceColumn`. -/
theorem fullRawContactColumn_binomial
    (x u0 u1 : K) (a s y r z : Nat) :
    rawContactColumn x u0 u1 a s y r z =
      (MvPolynomial.C x + eps) ^ a * localS ^ s *
        (∑ j ∈ Finset.range (y + 1),
          (MvPolynomial.C u0) ^ j * contactedDirection u1 ^ (y - j) *
            (y.choose j : FlatContact K)) * localR ^ r * localZ ^ z := by
  simp only [rawContactColumn, contactedY_eq_constant_add_direction]
  have hpow :
      (MvPolynomial.C u0 + contactedDirection u1) ^ y =
        ∑ j ∈ Finset.range (y + 1),
          (MvPolynomial.C u0) ^ j * contactedDirection u1 ^ (y - j) *
            (y.choose j : FlatContact K) :=
    add_pow (MvPolynomial.C u0) (contactedDirection u1) y
  rw [hpow]

theorem fullAssociatedFaceColumn_is_zero_constant_summand
    (x u0 u1 : K) (a s y r z : Nat) :
    (MvPolynomial.C x + eps) ^ a * localS ^ s *
          ((MvPolynomial.C u0) ^ 0 * contactedDirection u1 ^ (y - 0) *
            (y.choose 0 : FlatContact K)) * localR ^ r * localZ ^ z =
      fullAssociatedFaceColumn x u1 a s y r z := by
  simp [fullAssociatedFaceColumn]

/-! ## Literal target face legality and arithmetic -/

/-- A tuple satisfying the active, curvature, and weighted-X conditions
gives a literal monomial on the cap-3758 face. -/
theorem target_fullFace_shape_legal
    (a s y r : Nat)
    (hB : 2 * s + r ≤ 16) (hs : s ≤ 8)
    (hU : s + y + r ≤ 64)
    (ha : a + 131071 * y + (131071 - 1) * r +
        (131071 - 2) * s < 47 * 180413) :
    rawShapeLegal (47 * 180413) 131071 3758 16 8 64
      a s y r (3758 - (s + y + r)) := by
  unfold rawShapeLegal
  omega

/-- The same face count as the difference of the two complete source
ledgers.  The companion exact-integer script independently enumerates this
difference directly over every legal `(S,R,Y)` shape. -/
theorem target_fullFace_source_difference :
    65079223811319 - 65061789117960 = 17434693359 := by
  norm_num

/-- Exact published one-node associated/local-cap increment. -/
theorem target_fullFace_local_cap_difference :
    248257440 - 248191020 = 66420 := by
  norm_num

/-- Across all target nodes, the complete face exceeds that cap by exactly
23,088,879 dimensions. -/
theorem target_fullFace_associated_surplus_receipt :
    262144 * 66420 = 17411604480 ∧
      17434693359 - 17411604480 = 23088879 := by
  norm_num

/-! ## What the dimension surplus actually implies -/

variable {V W : Type*}
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [FiniteDimensional K V]

/-- Once a filtration-compatible proof bounds the rank of the complete
associated-face map by the all-node local cap, rank-nullity forces the stated
kernel.  This theorem does not assert that such a vector kills the lower
passive grades of the *complete* contact map. -/
theorem target_fullFace_associated_kernel_forced
    (associatedFace : V →ₗ[K] W)
    (hDomain : Module.finrank K V = 17434693359)
    (hRank : Module.finrank K associatedFace.range ≤ 17411604480) :
    23088879 ≤ Module.finrank K associatedFace.ker := by
  have hnullity := associatedFace.finrank_range_add_finrank_ker
  omega

#print axioms fullRawContactColumn_binomial
#print axioms fullAssociatedFaceColumn_is_zero_constant_summand
#print axioms target_fullFace_shape_legal
#print axioms target_fullFace_source_difference
#print axioms target_fullFace_local_cap_difference
#print axioms target_fullFace_associated_surplus_receipt
#print axioms target_fullFace_associated_kernel_forced

end

end ProximityPrize.SubmissionLower.K0FullPassiveFaceAssociatedDimension6900
