import TwoSourceSharpProjectiveResidualPackage6900
import DataElevenHighEClosedFrontier6900

/-!
# Two-source sharp projective/high-E incidence frontier

This file closes the two mechanical witness-packaging seams identified by the
two-source audit:

* it runs the sharp refilter while the literal `content < 16000` proof is
  still in scope; and
* it runs that refilter from the literal no-adjacent/high-E witness, so the
  sharp output itself retains `E0.natDegree < 18415` and hence `W <= 149485`.

The final endpoint keeps the original `U/Gamma/agreement/selected`, the exact
DataEleven/conic/cross leaf, projective-highness, all incidence assumptions,
and the joined sharp scalar/projective-residual package.
-/

namespace ProximityPrize.SubmissionLower.TwoSourceSharpProjectiveHighEIncidenceFrontier6900

open Polynomial ProximityPrize.Benchmark
open SupportRecurrence6900 SupportRecurrence6900.Target
open RecurrenceFiniteHilbertAssembly TargetTwoActiveHorizontalSource6900
open LowReceivedDirectionScalarSplit1331196900
open ActualDataNinePrimitiveConic6900 TargetRemainingCorankNineFrontier6900
open TargetRemainingCorankTenFrontier6900 TargetRemainingCorankElevenFrontier6900
open ActualPrimitiveRankThreeShape6900 ActualAlignedRationalCrossData6900
open ActualAlignedCrossRealization6900 ConicPrimitiveSeedDegreeGate6900
open ActualProperFixedScalarFamilySharpExceptions6900
open ActualFixedScalarWeightedLowWindow6900
open ActualAdjacentFilteredHardCornerElimination6900
open OddBlockActualHighEClosed6900
open TargetWeightedLowPoleWindowFrontier6900
open DataElevenWeightedLowPoleIntersection6900
open DataElevenHighEClosedFrontier6900
open ProjectiveHighDataElevenHighEClosedFrontier6900
open ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900
open UniversalProjectiveHighDirectionEndpointCut6900
open TwoSourceSharpFixedScalarRetarget6900
open TwoSourceSharpFixedScalarW133224Bridge6900
open TwoSourceSharpProjectiveResidualPackage6900
open ProjectiveHighLeafAgreementResidualFactor6900
open RawConicRestrictionSeedLedger6900 K0ReceivedPairTopSupport6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP ExtensionField 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- The lossless joined package with the high-E upper endpoint attached to
the very same `E0` returned by the sharp refilter. -/
structure HighESharpProjectiveResidualPackage
    {U : Fin 2 → Index → ExtensionField}
    (D : DataNine U) (A : PrimitiveConicData U D.horizontal.grade)
    (R : AlignedCrossData U D.horizontal.grade)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X]) where
  toSharpProjectiveResidualPackage :
    SharpProjectiveResidualPackage D A R Gamma agreement selected
  highE_small : toSharpProjectiveResidualPackage.E0.natDegree < 18415
  scalar_allowance_le_149485 :
    ((131071 + toSharpProjectiveResidualPackage.E0.natDegree) -
      max R.c.natDegree R.d.natDegree) -
        toSharpProjectiveResidualPackage.Q.natDegree ≤ 149485
  E0_root_free : ∀ i,
    toSharpProjectiveResidualPackage.E0.eval (IRSProfile.domain i) ≠ 0
  E0_adjacent_coprime : IsCoprime
    toSharpProjectiveResidualPackage.E0
    (toSharpProjectiveResidualPackage.E0.map sigma)
  E0_mixed_coprime :
    IsCoprime toSharpProjectiveResidualPackage.E0
        (toSharpProjectiveResidualPackage.E0.map (sigma.comp sigma)) ∨
      IsCoprime toSharpProjectiveResidualPackage.E0
        (toSharpProjectiveResidualPackage.E0.map
          (sigma.comp (sigma.comp sigma)))

/-- Refilter the literal high-E witness.  Unlike an existential join of the
old sharp and high-E theorems, this construction shares `B/E0/N0/Q`, so the
`E0 < 18415` refund really applies to the sharp retained `Good`. -/
theorem exists_highE_sharp_projective_residual_package
    {U : Fin 2 → Index → ExtensionField}
    (D : DataNine U) (A : PrimitiveConicData U D.horizontal.grade)
    (R : AlignedCrossData U D.horizontal.grade) (H : Realizes A R)
    (hcop : IsRelPrime A.P.x A.P.y) (hx : A.P.x ≠ 0) (hy : A.P.y ≠ 0)
    (hrank : actualCoefficientRank A ≤ 3)
    (hcontent : A.content.natDegree < 16000)
    (hgrade : D.horizontal.grade ≤ 24932)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X])
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i)
    (hlarge : twoSourceMcaBudget ≤ Gamma.card)
    (hclosed : FixedScalarWeightedNoAdjacentHardCornerCondition
      Gamma agreement selected R)
    (hprojective : CanonicalHighTailDirectionIndependent IRSProfile.domain U) :
    Nonempty (HighESharpProjectiveResidualPackage
      D A R Gamma agreement selected) := by
  classical
  obtain ⟨B, E0, N0, Q, hB, hE0, hRE, hRN, hproper, hcopQ, hQ,
    hsource, hminimal, hcap, hroot, hcopadj, hmixed,
    GoodOld, scalarOld, centreOld, aOld, bOld, hsubOld, hdiscardedOld,
    hretainedOld, hWloOld, hWhiOld, hcentreOld, habOld, hinjOld,
    hQrootOld, hscalarOld, houtside, hsmall, hsumlt, hlowQ, hWloOld',
    hexcess, hsum, hEupper, hWupper, hEsmall⟩ := hclosed
  obtain ⟨hxSeed, hySeed, hcSeed, hline⟩ :=
    PrimitiveConicData.rank_three_line_seed_degree_le_two
      D A hcop hx hy hrank
  have hcontent' : A.content.natDegree ≤ 15999 := by omega
  have ht : max R.c.natDegree R.d.natDegree ≤ 8836 := by omega
  have hEpositive : 0 < E0.natDegree := by omega
  obtain ⟨Good, scalar, centre, a, b, hsub, hdiscarded, hcentre, hab,
    hinj, hQroot, hscalar⟩ :=
    exists_actual_proper_fixed_scalar_family_sharp
      U D A R H hcop hx hy hrank hxSeed hySeed hcSeed hcontent' hgrade ht
      B E0 N0 hRE hRN Q hQ hsource hminimal hproper hEpositive
      Gamma agreement selected hdegree hcard hagrees
      (hlarge.trans' (by norm_num [twoSourceMcaBudget]))
  have hsplit : (Gamma \ Good).card + Good.card = Gamma.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hretained : sharpRetainedBudget ≤ Good.card := by
    change 263611557201785350 ≤ Good.card
    change 263836564062556785 ≤ Gamma.card at hlarge
    change (Gamma \ Good).card ≤ 225006860771435 at hdiscarded
    omega
  let W : Nat := ((131071 + E0.natDegree) -
    max R.c.natDegree R.d.natDegree) - Q.natDegree
  have hWlo : 133225 ≤ W := by
    apply retained_actual_scalar_degree_ge_133225
      Gamma Good agreement scalar centre W hsub hretained hinj
    · intro gamma hgamma
      exact (hscalar gamma hgamma).2.1
    · exact hcard
    · intro gamma hgamma i hi
      exact (hscalar gamma hgamma).2.2.2 i hi
  have hWhi : W ≤ 149485 := by
    dsimp only [W]
    omega
  have hresidual : ∀ gamma ∈ Good, ∃ residual : ExtensionField[X],
      residual ≠ 0 ∧
      receivedDirectionInterpolant IRSProfile.domain
          (fun i ↦ U 0 i + gamma * U 1 i) - selected gamma =
        supportLocator IRSProfile.domain (agreement gamma) * residual ∧
      residual.natDegree ≤ 81730 := by
    intro gamma hgamma
    have hgammaGamma : gamma ∈ Gamma := hsub hgamma
    have hQlower : 180413 ≤
        (receivedDirectionInterpolant IRSProfile.domain
          (fun i ↦ U 0 i + gamma * U 1 i)).natDegree := by
      exact projectiveHigh_combination_degree_ge_agreement
        IRSProfile.domain U hprojective gamma (agreement gamma)
        (selected gamma) (hdegree gamma hgammaGamma)
        (hcard gamma hgammaGamma) (hagrees gamma hgammaGamma)
    exact agreement_residual_factor_of_bounds IRSProfile.domain
      (by norm_num [Index, IRSProfile.Index])
      (fun i ↦ U 0 i + gamma * U 1 i)
      (agreement gamma) (selected gamma) hQlower
      (hdegree gamma hgammaGamma) (hcard gamma hgammaGamma)
      (hagrees gamma hgammaGamma)
  let sharp : SharpProjectiveResidualPackage
      D A R Gamma agreement selected :=
    { realizes := H
      conic_content_small := hcontent
      horizontal_grade_le := hgrade
      coefficient_rank_le_three := hrank
      coefficient_pair_relPrime := hcop
      coefficient_x_ne := hx
      coefficient_y_ne := hy
      B := B
      E0 := E0
      N0 := N0
      Q := Q
      B_ne := hB
      E0_ne := hE0
      cross_denominator_factor := hRE
      cross_numerator_factor := hRN
      reduced_factor := hproper
      minimal_solution_coprime := hcopQ
      minimal_solution_ne := hQ
      source_equation := hsource
      minimal_solution := hminimal
      Good := Good
      scalar := scalar
      centre := centre
      a := a
      b := b
      good_subset := hsub
      discarded_card_le := hdiscarded
      retained_card_ge := hretained
      centre_fixed := hcentre
      numerator_bezout := hab
      scalar_injective := hinj
      minimal_solution_root_free := hQroot
      scalar_data := hscalar
      scalar_allowance_ge := hWlo
      scalar_allowance_le := hWhi.trans (by norm_num)
      agreement_residual := hresidual }
  exact ⟨⟨sharp, hEsmall, hWhi, hroot, hcopadj, hmixed⟩⟩

/-- The benchmark-facing enriched leaf.  Its first five fields are precisely
the old projective-high/high-E/incidence leaf data, while `sharpPackage` keeps
the stronger two-source refilter on those same nested witnesses. -/
structure TwoSourceSharpProjectiveHighEIncidenceLeaf
    (U : Fin 2 → Index → ExtensionField)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X]) where
  toWeightedLeaf :
    DataElevenWeightedLowPoleLeaf U Gamma agreement selected
  cross_no_adjacent_hard_corner :
    FixedScalarWeightedNoAdjacentHardCornerCondition
      Gamma agreement selected toWeightedLeaf.cross
  projectiveHigh :
    CanonicalHighTailDirectionIndependent IRSProfile.domain U
  selected_degree :
    ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071
  agreement_card :
    ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card
  selected_agrees :
    ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (IRSProfile.domain i) =
        U 0 i + gamma * U 1 i
  selected_bad :
    ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code IRSProfile.domain 131072) (agreement gamma)
  sharpPackage :
    HighESharpProjectiveResidualPackage
      toWeightedLeaf.data.toDataTen.toDataNine
      toWeightedLeaf.conic toWeightedLeaf.cross
      Gamma agreement selected

/-- Forget only the new sharp package.  This demonstrates definitionally that
the enriched endpoint is a strengthening of the exact old incidence leaf,
not a parallel existential witness. -/
def TwoSourceSharpProjectiveHighEIncidenceLeaf.toIncidenceLeaf
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : TwoSourceSharpProjectiveHighEIncidenceLeaf
      U Gamma agreement selected) :
    ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected :=
  { toProjectiveHighDataElevenHighEClosedLeaf :=
      { toDataElevenHighEClosedLeaf :=
          { toWeightedLeaf := leaf.toWeightedLeaf
            cross_no_adjacent_hard_corner :=
              leaf.cross_no_adjacent_hard_corner }
        projectiveHigh := leaf.projectiveHigh }
    selected_degree := leaf.selected_degree
    agreement_card := leaf.agreement_card
    selected_agrees := leaf.selected_agrees
    selected_bad := leaf.selected_bad }

/-- Under the larger two-source MCA threshold, construct the enriched leaf at
the point where `content < 16000` is still available.  Every object in the
result uses the input `U/Gamma/agreement/selected`; no old-leaf witness is
reselected after projection. -/
theorem target_bad_family_small_or_twoSource_sharp_projective_highE_leaf
    (U : Fin 2 → Index → ExtensionField)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X])
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i)
    (hbad : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code IRSProfile.domain 131072) (agreement gamma)) :
    Gamma.card < twoSourceMcaBudget ∨
      Nonempty (TwoSourceSharpProjectiveHighEIncidenceLeaf
        U Gamma agreement selected) := by
  classical
  by_cases hsmall : Gamma.card < twoSourceMcaBudget
  · exact Or.inl hsmall
  · right
    have hlarge : twoSourceMcaBudget ≤ Gamma.card := Nat.le_of_not_gt hsmall
    have hlargeOld : 254684620614660120 ≤ Gamma.card :=
      hlarge.trans' (by norm_num [twoSourceMcaBudget])
    have hI : Fintype.card Index = 262144 := by
      norm_num [Index, IRSProfile.Index]
    have hprojective :
        CanonicalHighTailDirectionIndependent IRSProfile.domain U := by
      rcases bad_family_small_or_canonicalHighTailDirectionIndependent
          IRSProfile.domain hI U Gamma agreement selected hdegree hcard
            hagrees hbad with
        hsmallOld | hprojective
      · omega
      · exact hprojective
    rcases target_bad_family_small_or_weighted_low_pole_window
        U Gamma agreement selected hdegree hcard hagrees hbad with
      hsmallOld | ⟨D, A, hlo, hcontent, hremaining, hcop, hx, hy, hshape,
        hseven, htwelve, hfixed, hrank, hgrade, hprimitive, haligned, hfour,
        hwindow, hquadratic, htwofold, hreduced, hpole, hthree, hgradecap,
        hneed, hnine, hpositive, height8, heightcapPos, hquad, hseven',
        hgrade', h7window, hfive, h5window, hcost, hcorner, hshort, hsharp,
        hfourdeg, hfourwindow, hlargewindow, hcornerfour, hthreeRank,
        hweightedTwo, hcap, hwedge, hlowgrade, horbits, hscalar, houtside,
        hhomogeneous, hlow, hweighted⟩
    · omega
    · have hnullity :
          7459 ≤ recurrenceFinrank (targetTwoFunctionals U) 131071 81731 := by
        have hsumRank := D.horizontal.rank_sum
        omega
      have hlineTwo : lineSeedDegree ExtensionField A.P ≤ 2 := by
        rcases hshape with hfourRank | hsmallShape
        · omega
        · exact hsmallShape.2.2.2
      let R : AlignedCrossData U D.horizontal.grade :=
        Classical.choose (haligned hthreeRank hwedge)
      have hR := Classical.choose_spec (haligned hthreeRank hwedge)
      have hRrealizes : Realizes A R := hR.1
      have hRnonpolynomial : ¬ R.E ∣ R.N := hR.2.1
      let D10 : DataTen U :=
        { toDataNine := D
          originalNullity_ge_ten := hnullity.trans' (by omega) }
      let D11 : DataEleven U :=
        { toDataTen := D10
          originalNullity_ge_eleven := hnullity.trans' (by omega) }
      let weightedLeaf : DataElevenWeightedLowPoleLeaf
          U Gamma agreement selected :=
        { data := D11
          conic := A
          nullity_ge_7459 := hnullity
          grade_le_24932 := hlowgrade
          lineSeedDegree_le_two := hlineTwo
          weightedLineSeedDegree_le_two := hweightedTwo
          coefficientRank_le_three := hthreeRank
          restoredCap_le := hcap
          movingWedge_zero := hwedge
          coefficient_pair_relPrime := hcop
          coefficient_x_ne := hx
          coefficient_y_ne := hy
          proper_pole_orbits := horbits
          fixed_scalar_poles := hscalar
          outside_window := houtside
          small_homogeneous := hhomogeneous
          low_window := hlow
          weighted_low_window := hweighted
          cross := R
          cross_realizes := hRrealizes
          cross_nonpolynomial := hRnonpolynomial
          cross_proper_pole := horbits R hRrealizes hRnonpolynomial
          cross_fixed_scalar := hscalar R hRrealizes hRnonpolynomial
          cross_outside_window := houtside R hRrealizes hRnonpolynomial
          cross_small_homogeneous :=
            hhomogeneous R hRrealizes hRnonpolynomial
          cross_low_window := hlow R hRrealizes hRnonpolynomial
          cross_weighted_low_window :=
            hweighted R hRrealizes hRnonpolynomial }
      have hclosed : FixedScalarWeightedNoAdjacentHardCornerCondition
          Gamma agreement selected R :=
        actual_fixed_scalar_weighted_no_adjacent_hard_corner_closed
          R Gamma agreement selected hdegree hcard hagrees hbad
          (hweighted R hRrealizes hRnonpolynomial)
      obtain ⟨sharpPackage⟩ :=
        exists_highE_sharp_projective_residual_package
          D A R hRrealizes hcop hx hy hthreeRank hcontent hlowgrade
          Gamma agreement selected hdegree hcard hagrees hlarge hclosed
          hprojective
      refine ⟨⟨weightedLeaf, ?_, hprojective, hdegree, hcard, hagrees,
        hbad, ?_⟩⟩
      · simpa only [weightedLeaf] using hclosed
      · simpa only [weightedLeaf, D11, D10] using sharpPackage

#print axioms HighESharpProjectiveResidualPackage
#print axioms exists_highE_sharp_projective_residual_package
#print axioms TwoSourceSharpProjectiveHighEIncidenceLeaf
#print axioms TwoSourceSharpProjectiveHighEIncidenceLeaf.toIncidenceLeaf
#print axioms target_bad_family_small_or_twoSource_sharp_projective_highE_leaf

end
end ProximityPrize.SubmissionLower.TwoSourceSharpProjectiveHighEIncidenceFrontier6900
