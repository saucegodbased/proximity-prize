import TwoSourceSharpFixedScalarW133224Bridge6900
import ProjectiveHighLeafAgreementResidualFactor6900

/-!
# Same-witness sharp scalar family and projective agreement residuals

This is a lossless join, not a counting claim.  The sharp two-source refilter
constructs a retained family `Good` of size at least `263611557201785350`.
If the received two-row word is also in the projective-high branch, every seed
of that *same* `Good` carries its actual agreement-locator factorization

`interp(U₀ + γ U₁) - selected γ = supportLocator(agreement γ) * residual γ`

with a nonzero residual of degree at most `81730`.

The record deliberately retains the literal `DataNine`, primitive conic,
aligned cross, realizability proof, and content bound used by the sharp
refilter.  Thus a downstream eliminant cannot silently exchange any of those
witnesses while using the projective residual.
-/

namespace ProximityPrize.SubmissionLower.TwoSourceSharpProjectiveResidualPackage6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open SupportRecurrence6900 LowReceivedDirectionScalarSplit1331196900
open ActualDataNinePrimitiveConic6900 TargetRemainingCorankNineFrontier6900
open ActualPrimitiveRankThreeShape6900 ActualAlignedRationalCrossData6900
open ActualAlignedCrossRealization6900 ConicPrimitiveSeedDegreeGate6900
open ActualFixedScalarWeightedLowWindow6900
open RawConicRestrictionSeedLedger6900 K0ReceivedPairTopSupport6900
open TwoSourceSharpFixedScalarRetarget6900
open TwoSourceSharpFixedScalarW133224Bridge6900
open UniversalProjectiveHighDirectionEndpointCut6900
open ProjectiveHighLeafAgreementResidualFactor6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP ExtensionField 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- The exact sharp scalar witness, augmented on the same retained seeds by
the canonical projective-high agreement residual.  Structural source data and
the content hypothesis are fields, rather than discarded constructor inputs.
-/
structure SharpProjectiveResidualPackage
    {U : Fin 2 → Index → ExtensionField}
    (D : DataNine U) (A : PrimitiveConicData U D.horizontal.grade)
    (R : AlignedCrossData U D.horizontal.grade)
    (Gamma : Finset ExtensionField)
    (agreement : ExtensionField → Finset Index)
    (selected : ExtensionField → ExtensionField[X]) where
  realizes : Realizes A R
  conic_content_small : A.content.natDegree < 16000
  horizontal_grade_le : D.horizontal.grade ≤ 24932
  coefficient_rank_le_three : actualCoefficientRank A ≤ 3
  coefficient_pair_relPrime : IsRelPrime A.P.x A.P.y
  coefficient_x_ne : A.P.x ≠ 0
  coefficient_y_ne : A.P.y ≠ 0
  B : ExtensionField[X]
  E0 : ExtensionField[X]
  N0 : ExtensionField[X]
  Q : ExtensionField[X]
  B_ne : B ≠ 0
  E0_ne : E0 ≠ 0
  cross_denominator_factor : R.E = B * E0
  cross_numerator_factor : R.N = B * N0
  reduced_factor : IsCoprime E0 N0
  minimal_solution_coprime : IsCoprime E0 Q
  minimal_solution_ne : Q ≠ 0
  source_equation :
    (B * R.L) * Q + (B.map sigma * R.M) * Q.map sigma = 0
  minimal_solution : ∀ P : ExtensionField[X], P ≠ 0 →
    (B * R.L) * P + (B.map sigma * R.M) * P.map sigma = 0 →
      Q.natDegree ≤ P.natDegree
  Good : Finset ExtensionField
  scalar : ExtensionField → ExtensionField[X]
  centre : Index → ExtensionField
  a : ExtensionField[X]
  b : ExtensionField[X]
  good_subset : Good ⊆ Gamma
  discarded_card_le : (Gamma \ Good).card ≤ sharpExceptionBudget
  retained_card_ge : sharpRetainedBudget ≤ Good.card
  centre_fixed : ∀ i, sigma (centre i) = centre i
  numerator_bezout : a * R.d - b * R.c = N0
  scalar_injective : Set.InjOn scalar (↑Good : Set ExtensionField)
  minimal_solution_root_free : ∀ i, Q.eval (IRSProfile.domain i) ≠ 0
  scalar_data : ∀ gamma ∈ Good,
    (scalar gamma).map sigma = scalar gamma ∧
    (scalar gamma).natDegree ≤
      ((131071 + E0.natDegree) - max R.c.natDegree R.d.natDegree) -
        Q.natDegree ∧
    E0 * selected gamma = a + C gamma * b +
      Q * (R.c + C gamma * R.d) * scalar gamma ∧
    ∀ i ∈ agreement gamma,
      (scalar gamma).eval (IRSProfile.domain i) = centre i
  scalar_allowance_ge :
    133225 ≤
      ((131071 + E0.natDegree) - max R.c.natDegree R.d.natDegree) -
        Q.natDegree
  scalar_allowance_le :
    ((131071 + E0.natDegree) - max R.c.natDegree R.d.natDegree) -
      Q.natDegree ≤ 149776
  agreement_residual : ∀ gamma ∈ Good, ∃ residual : ExtensionField[X],
    residual ≠ 0 ∧
    receivedDirectionInterpolant IRSProfile.domain
        (fun i ↦ U 0 i + gamma * U 1 i) - selected gamma =
      supportLocator IRSProfile.domain (agreement gamma) * residual ∧
    residual.natDegree ≤ 81730

/-- Build the joined package without changing `D`, `A`, `R`, `Gamma`, the
selected family, or the sharp producer's retained `Good`. -/
theorem exists_sharp_projective_residual_package
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
    (hmodel : FixedScalarWeightedLowWindowCondition
      Gamma agreement selected R)
    (hprojective : CanonicalHighTailDirectionIndependent IRSProfile.domain U) :
    Nonempty (SharpProjectiveResidualPackage
      D A R Gamma agreement selected) := by
  classical
  have hshape : actualCoefficientRank A = 4 ∨
      CoeffBound 1 A.P.x ∧ CoeffBound 1 A.P.y ∧
        CoeffBound 2 A.P.constant ∧
          lineSeedDegree ExtensionField A.P ≤ 2 :=
    Or.inr (PrimitiveConicData.rank_three_line_seed_degree_le_two
      D A hcop hx hy hrank)
  obtain ⟨B, E0, N0, Q, hB, hE0, hRE, hRN, hproper, hcopQ, hQ,
    hsource, hminimal, Good, scalar, centre, a, b, hsub, hdiscarded,
    hretained, hcentre, hab, hinj, hQroot, hscalar, hWlo, hWhi⟩ :=
    exists_sharp_retained_fixed_scalar_family_W133225
      D A R H hcop hx hy hrank hshape hcontent hgrade
      Gamma agreement selected hdegree hcard hagrees hlarge hmodel
  refine ⟨⟨H, hcontent, hgrade, hrank, hcop, hx, hy,
    B, E0, N0, Q, hB, hE0, hRE, hRN, hproper, hcopQ, hQ,
    hsource, hminimal, Good, scalar, centre, a, b, hsub, hdiscarded,
    hretained, hcentre, hab, hinj, hQroot, hscalar, hWlo, hWhi, ?_⟩⟩
  intro gamma hgamma
  have hgammaGamma : gamma ∈ Gamma := hsub hgamma
  have hQlower : 180413 ≤
      (receivedDirectionInterpolant IRSProfile.domain
        (fun i ↦ U 0 i + gamma * U 1 i)).natDegree := by
    exact projectiveHigh_combination_degree_ge_agreement
      IRSProfile.domain U hprojective gamma (agreement gamma) (selected gamma)
      (hdegree gamma hgammaGamma) (hcard gamma hgammaGamma)
      (hagrees gamma hgammaGamma)
  exact agreement_residual_factor_of_bounds IRSProfile.domain
    (by norm_num [Index, IRSProfile.Index])
    (fun i ↦ U 0 i + gamma * U 1 i)
    (agreement gamma) (selected gamma) hQlower
    (hdegree gamma hgammaGamma) (hcard gamma hgammaGamma)
    (hagrees gamma hgammaGamma)

#print axioms SharpProjectiveResidualPackage
#print axioms exists_sharp_projective_residual_package

end
end ProximityPrize.SubmissionLower.TwoSourceSharpProjectiveResidualPackage6900
