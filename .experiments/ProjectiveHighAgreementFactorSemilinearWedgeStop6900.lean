import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Semilinear wedge of an agreement factor: exact identity-debt STOP

Suppose a same-witness residual has the form

`A = B * S + H * R`,

where the scalar `S` and agreement locator `H` are coefficient-Frobenius
fixed.  Eliminating `S` against its conjugate does produce an exact relation:

`B^sigma * A - A^sigma * B`

is divisible by `H`.  The first theorem proves this factorization.

The remaining theorems expose the load-bearing failure.  Whenever the two
underlying affine residual rows are both identities against one fixed centre,
the wedge is the zero function of a fresh seed variable.  An affine row can
be active for at most one candidate per coordinate, so a family of the size
retained by the sharp TwoSource bridge leaves essentially its whole mass in
these identity fibres.  The direct wedge also uses seed exponent `p+1`, well
above the old univariate nonidentity-degree budget.

This is deliberately an abstract, small-import certificate.  The exact
projective-high leaf supplies `H` and its fixedness; the sharp TwoSource scalar
identity supplies `A`, `B`, `S`, the fixed centre, and retained mass.  No
replacement witness or generic nonvanishing premise is used.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighAgreementFactorSemilinearWedgeStop6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

/-- Eliminating a coefficient-Frobenius-fixed scalar preserves the fixed
agreement factor. -/
theorem semilinear_wedge_factor
    {K : Type*} [Field K] (sigma : K →+* K)
    (A B S H R : K[X])
    (hA : A = B * S + H * R)
    (hS : S.map sigma = S) (hH : H.map sigma = H) :
    B.map sigma * A - A.map sigma * B =
      H * (B.map sigma * R - R.map sigma * B) := by
  rw [hA, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    hS, hH]
  ring

/-- Evaluation-level semilinear wedge for an affine seed line. -/
def affineSemilinearWedge
    {K : Type*} [Field K] (sigma : K →+* K)
    (A0 A1 B0 B1 gamma : K) : K :=
  sigma (B0 + gamma * B1) * (A0 + gamma * A1) -
    sigma (A0 + gamma * A1) * (B0 + gamma * B1)

/-- If both natural residual rows are identities against one fixed centre,
the semilinear wedge is an identity for every fresh seed value. -/
theorem affineSemilinearWedge_eq_zero_of_identity_rows
    {K : Type*} [Field K] (sigma : K →+* K)
    (A0 A1 B0 B1 centre : K)
    (hcentre : sigma centre = centre)
    (h0 : A0 - B0 * centre = 0)
    (h1 : A1 - B1 * centre = 0)
    (gamma : K) :
    affineSemilinearWedge sigma A0 A1 B0 B1 gamma = 0 := by
  have hA0 : A0 = B0 * centre := by linear_combination h0
  have hA1 : A1 = B1 * centre := by linear_combination h1
  simp only [affineSemilinearWedge, hA0, hA1, map_add, map_mul, hcentre]
  ring

/-- Seeds owning at least one coordinate where the affine residual is not the
zero polynomial. -/
def activeSeeds
    {I K : Type*} [Field K] [DecidableEq K]
    (Good : Finset K) (agreement : K → Finset I) (row0 row1 : I → K) :
    Finset K :=
  Good.filter fun gamma ↦
    ∃ i ∈ agreement gamma, ¬ (row0 i = 0 ∧ row1 i = 0)

/-- A coordinate can be owned nonidentically by at most one seed. -/
theorem activeSeeds_card_le
    {I K : Type*} [Fintype I] [Field K] [DecidableEq K]
    (Good : Finset K) (agreement : K → Finset I) (row0 row1 : I → K)
    (hrelation : ∀ gamma ∈ Good, ∀ i ∈ agreement gamma,
      row0 i + gamma * row1 i = 0) :
    (activeSeeds Good agreement row0 row1).card ≤ Fintype.card I := by
  classical
  let owner : ↑(activeSeeds Good agreement row0 row1) → I := fun gamma ↦
    Classical.choose ((Finset.mem_filter.mp gamma.property).2)
  have owner_mem (gamma : ↑(activeSeeds Good agreement row0 row1)) :
      owner gamma ∈ agreement gamma.1 :=
    (Classical.choose_spec ((Finset.mem_filter.mp gamma.property).2)).1
  have owner_nonidentity
      (gamma : ↑(activeSeeds Good agreement row0 row1)) :
      ¬ (row0 (owner gamma) = 0 ∧ row1 (owner gamma) = 0) :=
    (Classical.choose_spec ((Finset.mem_filter.mp gamma.property).2)).2
  have owner_injective : Function.Injective owner := by
    intro gamma delta howner
    apply Subtype.ext
    by_contra hne
    have hgamma := hrelation gamma.1
      (Finset.mem_filter.mp gamma.property).1
      (owner gamma) (owner_mem gamma)
    have hdelta := hrelation delta.1
      (Finset.mem_filter.mp delta.property).1
      (owner delta) (owner_mem delta)
    rw [← howner] at hdelta
    have hrow1 : row1 (owner gamma) = 0 := by
      have hseed : gamma.1 - delta.1 ≠ 0 := sub_ne_zero.mpr hne
      apply (mul_eq_zero.mp ?_).resolve_left hseed
      linear_combination hgamma - hdelta
    have hrow0 : row0 (owner gamma) = 0 := by
      rw [hrow1, mul_zero, add_zero] at hgamma
      exact hgamma
    exact owner_nonidentity gamma ⟨hrow0, hrow1⟩
  have hcard : Fintype.card ↑(activeSeeds Good agreement row0 row1) ≤
      Fintype.card I :=
    Fintype.card_le_of_injective owner owner_injective
  simpa only [Fintype.card_coe] using hcard

/-- Complementary identity-fibre lower bound. -/
theorem identityOnlySeeds_card_lower
    {I K : Type*} [Fintype I] [Field K] [DecidableEq K]
    (Good : Finset K) (agreement : K → Finset I) (row0 row1 : I → K)
    (hrelation : ∀ gamma ∈ Good, ∀ i ∈ agreement gamma,
      row0 i + gamma * row1 i = 0) :
    Good.card - Fintype.card I ≤
      (Good \ activeSeeds Good agreement row0 row1).card := by
  have hactiveSub : activeSeeds Good agreement row0 row1 ⊆ Good := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).1
  have hpartition := Finset.card_sdiff_add_card_eq_card hactiveSub
  have hactive := activeSeeds_card_le Good agreement row0 row1 hrelation
  omega

/-- Every agreement owned by an identity-only seed makes the semilinear wedge
identically zero in a fresh seed variable. -/
theorem identityOnlySeeds_semilinear_wedge_eq_zero
    {I K : Type*} [Fintype I] [Field K] [DecidableEq K]
    (sigma : K →+* K)
    (Good : Finset K) (agreement : K → Finset I)
    (A0 A1 B0 B1 : I → K) (centre : I → K)
    (hcentre : ∀ i, sigma (centre i) = centre i)
    {delta : K}
    (hdelta : delta ∈ Good \ activeSeeds Good agreement
      (fun i ↦ A0 i - B0 i * centre i)
      (fun i ↦ A1 i - B1 i * centre i))
    {i : I} (hi : i ∈ agreement delta) (z : K) :
    affineSemilinearWedge sigma (A0 i) (A1 i) (B0 i) (B1 i) z = 0 := by
  have hnotActive := (Finset.mem_sdiff.mp hdelta).2
  have hrows :
      A0 i - B0 i * centre i = 0 ∧
        A1 i - B1 i * centre i = 0 := by
    by_contra hnot
    exact hnotActive (Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp hdelta).1, ⟨i, hi, hnot⟩⟩)
  apply affineSemilinearWedge_eq_zero_of_identity_rows
    sigma (A0 i) (A1 i) (B0 i) (B1 i) (centre i)
  · exact hcentre i
  · exact hrows.1
  · exact hrows.2

/-- Sharp TwoSource retained mass minus the 262144 possible active owners. -/
theorem sharp_twoSource_semilinear_identity_mass :
    263611557201785350 - 262144 = 263611557201523206 := by
  norm_num

/-- The direct semilinear seed polynomial uses exponent `p+1`; even one such
relation is above the earlier univariate nonidentity-degree budget. -/
theorem direct_frobenius_wedge_seed_degree_exceeds_old_budget :
    42700739 < 2130706433 + 1 := by
  norm_num

/-- The sharp TwoSource MCA allowance has only this much room above its
retained scalar subfamily. -/
theorem sharp_twoSource_outer_slack :
    263836564062556785 - 263611557201785350 = 225006860771435 := by
  norm_num

#print axioms semilinear_wedge_factor
#print axioms affineSemilinearWedge_eq_zero_of_identity_rows
#print axioms activeSeeds_card_le
#print axioms identityOnlySeeds_card_lower
#print axioms identityOnlySeeds_semilinear_wedge_eq_zero
#print axioms sharp_twoSource_semilinear_identity_mass
#print axioms direct_frobenius_wedge_seed_degree_exceeds_old_budget
#print axioms sharp_twoSource_outer_slack

end
end ProximityPrize.SubmissionLower.ProjectiveHighAgreementFactorSemilinearWedgeStop6900
