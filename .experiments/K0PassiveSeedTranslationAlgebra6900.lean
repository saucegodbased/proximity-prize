import K0PassiveSeedProductRule6900
import Mathlib.Tactic.Ring

/-!
# Constant affine normalization of the passive seed

The literal last-passive-face experiment is easiest to read at a nonzero
boundary seed.  This file records why a zero seed is not a separate source
case.  Translate the passive coordinate by a constant

```text
W = Z - c,      u0' = u0 + c*u1.
```

Then `u0' + u1*W = u0 + u1*Z`.  Translation is unitriangular in the seed
degree: `W^z` is a linear combination of `Z^j`, `j <= z`, with leading
coefficient one.  Since the raw source is downward closed in its seed
degree, the translation and its inverse preserve every literal source
window.  Taking `c = gamma+1` sends every boundary seed to `W=-1`, uniformly
and without an X-degree payment.

These are algebra/source-legality facts.  They remove the apparent
`gamma=0` special case, but do not prove that the cap-3757 relative
connecting map is surjective.
-/

namespace ProximityPrize.SubmissionLower.K0PassiveSeedTranslationAlgebra6900

open scoped BigOperators
open K0SRTinyContactCore6900
open K0PassiveSeedProductRule6900

noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K]

/-- The translated passive coordinate `W=Z-c`. -/
def shiftedSeed (c : K) : FlatContact K :=
  localZ - MvPolynomial.C c

/-- Contacted value written in the translated seed coordinate and the
correspondingly sheared constant received row. -/
def shiftedContactedY (u0 u1 c : K) : FlatContact K :=
  MvPolynomial.C (u0 + c * u1) +
      MvPolynomial.C u1 * shiftedSeed c +
    eps * localR - eps ^ 2 * localS + eps ^ 3 * localT

/-- Constant passive translation leaves the contacted affine received line
literally unchanged. -/
theorem shiftedContactedY_eq (u0 u1 c : K) :
    shiftedContactedY u0 u1 c = contactedY u0 u1 := by
  simp only [shiftedContactedY, shiftedSeed, contactedY, map_add, map_mul]
  ring

/-- A raw monomial expressed in the translated passive coordinate. -/
def shiftedRawContactColumn
    (x u0 u1 c : K) (a s y r z : Nat) : FlatContact K :=
  (MvPolynomial.C x + eps) ^ a * localS ^ s *
    shiftedContactedY u0 u1 c ^ y * localR ^ r * shiftedSeed c ^ z

/-- After the received-row shear, only the final seed power changes. -/
theorem shiftedRawContactColumn_eq
    (x u0 u1 c : K) (a s y r z : Nat) :
    shiftedRawContactColumn x u0 u1 c a s y r z =
      (MvPolynomial.C x + eps) ^ a * localS ^ s *
        contactedY u0 u1 ^ y * localR ^ r *
          (localZ - MvPolynomial.C c) ^ z := by
  simp only [shiftedRawContactColumn, shiftedSeed, shiftedContactedY_eq]

/-- The translated top seed monomial expands only into the same or lower
seed degrees.  The `j=z` summand has coefficient one, so this change of basis
is unitriangular; applying the same identity with `-c` gives the inverse. -/
theorem shiftedSeed_pow_expansion (c : K) (z : Nat) :
    shiftedSeed c ^ z =
      ∑ j ∈ Finset.range (z + 1),
        (-1) ^ (j + z) * localZ ^ j *
          (MvPolynomial.C c) ^ (z - j) *
            (z.choose j : FlatContact K) := by
  unfold shiftedSeed
  exact sub_pow localZ (MvPolynomial.C c) z

/-- The scalar received line is invariant under the same shear. -/
theorem receivedLine_seed_translation
    (u0 u1 gamma c : K) :
    (u0 + c * u1) + (gamma - c) * u1 = u0 + gamma * u1 := by
  ring

/-- The canonical choice `c=gamma+1` moves every seed, including zero, to
the fixed nonzero value `-1`. -/
theorem canonical_seed_normalization (gamma : K) :
    gamma - (gamma + 1) = -1 := by
  ring

theorem canonical_seed_normalization_ne_zero (gamma : K) :
    gamma - (gamma + 1) ≠ 0 := by
  rw [canonical_seed_normalization]
  exact neg_ne_zero.mpr one_ne_zero

theorem canonical_seed_power_ne_zero (gamma : K) (z : Nat) :
    (gamma - (gamma + 1)) ^ z ≠ 0 :=
  pow_ne_zero z (canonical_seed_normalization_ne_zero gamma)

/-- Literal raw-source membership is monotone downwards in passive seed
degree.  This is the source fact needed term-by-term in the binomial
translation above. -/
theorem rawShapeLegal_seed_anti
    (D w L B sCap U a s y r z j : Nat) (hj : j ≤ z)
    (hlegal : rawShapeLegal D w L B sCap U a s y r z) :
    rawShapeLegal D w L B sCap U a s y r j := by
  unfold rawShapeLegal at hlegal ⊢
  omega

/-- Every term in the translated target analogue
`X^2 Y^48 (Z-c)^3709` is a legal target raw monomial.  In particular the
translation does not leave the cap-3757 source. -/
theorem target_X2_Y48_translatedSeed_term_legal
    (j : Nat) (hj : j ≤ 3709) :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      2 0 48 0 j := by
  unfold rawShapeLegal
  norm_num
  omega

/-- The leading `Z^3709` term is genuinely in the newly attached face,
whereas every lower term already lies at cap 3756. -/
theorem target_X2_Y48_translation_face_split :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        2 0 48 0 3709 ∧
      (∀ j < 3709,
        rawShapeLegal (47 * 180413) 131071 3756 16 8 64
          2 0 48 0 j) := by
  constructor
  · exact target_X2_Y48_translatedSeed_term_legal 3709 le_rfl
  · intro j hj
    unfold rawShapeLegal
    norm_num
    omega

/-- Translation by `c` followed by translation by `-c` is literally the
identity on the passive coordinate. -/
theorem shiftedSeed_inverse (c : K) :
    shiftedSeed c + MvPolynomial.C c = localZ := by
  simp [shiftedSeed]

#print axioms shiftedContactedY_eq
#print axioms shiftedSeed_pow_expansion
#print axioms receivedLine_seed_translation
#print axioms canonical_seed_normalization_ne_zero
#print axioms canonical_seed_power_ne_zero
#print axioms rawShapeLegal_seed_anti
#print axioms target_X2_Y48_translatedSeed_term_legal
#print axioms target_X2_Y48_translation_face_split
#print axioms shiftedSeed_inverse

end

end ProximityPrize.SubmissionLower.K0PassiveSeedTranslationAlgebra6900
