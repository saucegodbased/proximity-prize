import ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900

/-!
# Exact identity debt of the natural residual-coordinate eliminants

For every retained scalar candidate the fixed-scalar residual gives one
affine relation in the seed at each owned agreement coordinate.  Two distinct
seeds cannot use the same coordinate nonidentically: subtracting their two
affine relations makes the linear coefficient zero, and then the constant
coefficient is zero too.

Consequently the nonidentity parts of the agreement sets are pairwise
disjoint.  There are only `262144` coordinates, whereas the retained family
has at least `253511670984674103` seeds.  Thus the obvious one-coordinate
eliminant puts at least `253511670984411959` candidates in identity fibres.
This is far above the exact admissible identity debt `1121769749`.

The result is deliberately scoped to the natural two residual rows.  It does
not assert that every possible eliminant has this defect, and it does not
replace the same-witness leaf by an abstract family.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighLeafResidualIdentityDebt6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open ActualAdjacentFilteredHardCornerElimination6900
open ProjectiveHighDataElevenHighEClosedFrontier6900
open ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Seeds which own at least one coordinate on which the affine relation is
not the zero polynomial. -/
def activeSeeds {I K : Type*} [Field K] [DecidableEq K]
    (Good : Finset K) (agreement : K → Finset I) (row0 row1 : I → K) :
    Finset K :=
  Good.filter fun gamma ↦
    ∃ i ∈ agreement gamma, ¬ (row0 i = 0 ∧ row1 i = 0)

/-- The literal degree-one source-coordinate relation. -/
def residualCoordinateRelation {I K : Type*} [Field K]
    (row0 row1 : I → K) (i : I) : K[X] :=
  C (row1 i) * (Polynomial.X : K[X]) + C (row0 i)

@[simp]
theorem residualCoordinateRelation_eval
    {I K : Type*} [Field K] (row0 row1 : I → K) (i : I) (gamma : K) :
    (residualCoordinateRelation row0 row1 i).eval gamma =
      row0 i + gamma * row1 i := by
  simp only [residualCoordinateRelation, eval_add, eval_mul, eval_C, eval_X]
  ring

theorem residualCoordinateRelation_eq_zero_iff
    {I K : Type*} [Field K] (row0 row1 : I → K) (i : I) :
    residualCoordinateRelation row0 row1 i = 0 ↔
      row0 i = 0 ∧ row1 i = 0 := by
  constructor
  · intro hzero
    have hcoeff0 := congrArg (fun P : K[X] ↦ P.coeff 0) hzero
    have hcoeff1 := congrArg (fun P : K[X] ↦ P.coeff 1) hzero
    constructor
    · simpa [residualCoordinateRelation] using hcoeff0
    · simpa [residualCoordinateRelation] using hcoeff1
  · rintro ⟨hzero0, hzero1⟩
    simp [residualCoordinateRelation, hzero0, hzero1]

/-- Every owned relation of a seed outside `activeSeeds` is literally the
zero polynomial, rather than merely a polynomial which happens to vanish at
that seed. -/
theorem identityOnlySeeds_relation_eq_zero
    {I K : Type*} [Field K] [DecidableEq K]
    (Good : Finset K) (agreement : K → Finset I) (row0 row1 : I → K)
    {gamma : K} (hgamma : gamma ∈
      Good \ activeSeeds Good agreement row0 row1)
    {i : I} (hi : i ∈ agreement gamma) :
    residualCoordinateRelation row0 row1 i = 0 := by
  apply (residualCoordinateRelation_eq_zero_iff row0 row1 i).2
  by_contra hnonidentity
  exact (Finset.mem_sdiff.mp hgamma).2
    (Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp hgamma).1, ⟨i, hi, hnonidentity⟩⟩)

/-- A coordinate can be owned nonidentically by at most one seed.  Choosing
one such coordinate for every active seed therefore injects active seeds into
the coordinate set. -/
theorem activeSeeds_card_le
    {I K : Type*} [Fintype I] [Field K] [DecidableEq K]
    (Good : Finset K) (agreement : K → Finset I) (row0 row1 : I → K)
    (hrelation : ∀ gamma ∈ Good, ∀ i ∈ agreement gamma,
      row0 i + gamma * row1 i = 0) :
    (activeSeeds Good agreement row0 row1).card ≤ Fintype.card I := by
  classical
  let owner : ↑(activeSeeds Good agreement row0 row1) → I := fun gamma ↦
    Classical.choose
      ((Finset.mem_filter.mp gamma.property).2)
  have owner_mem (gamma : ↑(activeSeeds Good agreement row0 row1)) :
      owner gamma ∈ agreement gamma.1 := by
    exact (Classical.choose_spec
      ((Finset.mem_filter.mp gamma.property).2)).1
  have owner_nonidentity
      (gamma : ↑(activeSeeds Good agreement row0 row1)) :
      ¬ (row0 (owner gamma) = 0 ∧ row1 (owner gamma) = 0) := by
    exact (Classical.choose_spec
      ((Finset.mem_filter.mp gamma.property).2)).2
  have owner_injective : Function.Injective owner := by
    intro gamma delta howner
    apply Subtype.ext
    by_contra hne
    have hgammaGood : gamma.1 ∈ Good :=
      (Finset.mem_filter.mp gamma.property).1
    have hdeltaGood : delta.1 ∈ Good :=
      (Finset.mem_filter.mp delta.property).1
    have hgamma := hrelation gamma.1 hgammaGood
      (owner gamma) (owner_mem gamma)
    have hdelta := hrelation delta.1 hdeltaGood
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

/-- Complementary form: all but at most `|I|` seeds own only identity
specializations of the natural affine relation. -/
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

/-- The actual same-witness leaf exposes residual rows whose identity debt is
already essentially the entire retained family.  The final conjunct records
the exact failure of the endpoint identity allowance. -/
theorem projectiveHigh_leaf_natural_residual_identity_debt
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected) :
    ∃ Good : Finset ExtensionField, ∃ row0 row1 : Index → ExtensionField,
      Good ⊆ Gamma ∧ 253511670984674103 ≤ Good.card ∧
      (∀ gamma ∈ Good, ∀ i ∈ agreement gamma,
        row0 i + gamma * row1 i = 0) ∧
      253511670984411959 ≤
        (Good \ activeSeeds Good agreement row0 row1).card ∧
      1121769749 < (Good \ activeSeeds Good agreement row0 row1).card := by
  classical
  let base := leaf.toProjectiveHighDataElevenHighEClosedLeaf.toDataElevenHighEClosedLeaf
  let R := base.toWeightedLeaf.cross
  obtain ⟨Bfac, E0, N0, Q, hBfac, hE0, hRE, hRN, hproper, hcopQ,
    hQ, hhom, hmin, hcap, hroot, hcopadj, hmixed, Good, scalar, centre,
    a, b, hsub, hexception, hretained, hWlo0, hWhi0, hcentre, hab,
    hinj, hQroot, hscalar, houtside, hsmall, hh, hlow, hWlo, hexcess,
    hsum, heUpper, hWupper, hcorner⟩ :=
      base.cross_no_adjacent_hard_corner
  let row0 : Index → ExtensionField := fun i ↦
    E0.eval (IRSProfile.domain i) * U 0 i - a.eval (IRSProfile.domain i) -
      Q.eval (IRSProfile.domain i) * R.c.eval (IRSProfile.domain i) * centre i
  let row1 : Index → ExtensionField := fun i ↦
    E0.eval (IRSProfile.domain i) * U 1 i - b.eval (IRSProfile.domain i) -
      Q.eval (IRSProfile.domain i) * R.d.eval (IRSProfile.domain i) * centre i
  have hrelation : ∀ gamma ∈ Good, ∀ i ∈ agreement gamma,
      row0 i + gamma * row1 i = 0 := by
    intro gamma hgamma i hi
    have hres := congrArg
      (fun P : ExtensionField[X] ↦ P.eval (IRSProfile.domain i))
      ((hscalar gamma hgamma).2.2.1)
    simp only [eval_mul, eval_add, eval_C] at hres
    rw [leaf.selected_agrees gamma (hsub hgamma) i hi,
      (hscalar gamma hgamma).2.2.2 i hi] at hres
    dsimp only [row0, row1]
    linear_combination hres
  refine ⟨Good, row0, row1, hsub, hretained, hrelation, ?_, ?_⟩
  · have hlower := identityOnlySeeds_card_lower
      Good agreement row0 row1 hrelation
    have hI : Fintype.card Index = 262144 := by
      norm_num [Index, IRSProfile.Index]
    rw [hI] at hlower
    omega
  · have hlower := identityOnlySeeds_card_lower
      Good agreement row0 row1 hrelation
    have hI : Fintype.card Index = 262144 := by
      norm_num [Index, IRSProfile.Index]
    rw [hI] at hlower
    omega

theorem natural_residual_identity_debt_excess :
    253511670984411959 - 1121769749 = 253511669862642210 := by
  norm_num

#print axioms activeSeeds_card_le
#print axioms identityOnlySeeds_relation_eq_zero
#print axioms identityOnlySeeds_card_lower
#print axioms projectiveHigh_leaf_natural_residual_identity_debt
#print axioms natural_residual_identity_debt_excess

end
end ProximityPrize.SubmissionLower.ProjectiveHighLeafResidualIdentityDebt6900
