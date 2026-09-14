import FixedScalarSmallSCountergate6900

/-! Exact countergate for the agreement-size field omitted by the terminal
DataEleven interface.  Kept separate from the lossless DataEleven wrapper so
the legacy and modern valuation import closures need not be elaborated in one
new module. -/

namespace ProximityPrize.SubmissionLower.FixedScalarIncidencePayloadLoss6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open ActualAdjacentFilteredHardCornerElimination6900
open FixedScalarSmallSCountergate6900
open ProjectiveHighReciprocalCrossCountergate6900
open TZeroReciprocalResiduePlaneCountergate6900
open UniversalProjectiveHighDirectionEndpointCut6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 30000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The terminal fixed-scalar payload alone still remembers that its retained
`Good` family is huge, hence the ambient seed family is huge. -/
theorem fixedScalar_noAdjacent_Gamma_card_ge
    {U : Fin 2 → Index → ExtensionField} {j : Nat}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    {R : AlignedCrossData U j}
    (hmodel : FixedScalarWeightedNoAdjacentHardCornerCondition
      Gamma agreement selected R) :
    253511670984674103 ≤ Gamma.card := by
  rcases hmodel with ⟨B, E0, N0, Q, hB, hE0, hRE, hRN, hproper,
    hcopQ, hQ, hhom, hmin, hcap, hroot, hcopadj, hmixed, Good,
    scalar, centre, a, b, hsub, hexception, hretained, hWlo0, hWhi0,
    hcentre, hab, hinj, hQroot, hscalar, houtside, hsmall, hh, hlow,
    hWlo, hexcess, hsum, heUpper, hWupper, hcorner⟩
  exact hretained.trans (Finset.card_le_card hsub)

/-- Exact API countergate: constant `c,d`, projectively high reciprocal rows,
and the complete no-adjacent fixed-scalar payload coexist with a huge ambient
family whose agreement sets are all empty.  Consequently agreement size
`180413` is not a consequence of that payload.

This deliberately does not construct the deep `DataEleven` ancestry; it
isolates the information erased at the old terminal interface. -/
theorem exists_projectiveHigh_scalarPayload_without_large_agreement :
    ∃ theta : ExtensionField, sigma theta ≠ theta ∧
    let E : ExtensionField[X] := denominator theta 2049
    ∃ R : AlignedCrossData (reciprocalDomainU E) E.natDegree,
      R.c = 1 ∧ R.d = 0 ∧
      CanonicalHighTailDirectionIndependent IRSProfile.domain
        (reciprocalDomainU E) ∧
      ∃ Gamma : Finset ExtensionField,
      ∃ selected : ExtensionField → ExtensionField[X],
        FixedScalarWeightedNoAdjacentHardCornerCondition
          Gamma emptyAgreement selected R ∧
        253511670984674103 ≤ Gamma.card ∧
        ¬ (∀ gamma ∈ Gamma,
          180413 ≤ (emptyAgreement gamma).card) := by
  obtain ⟨theta, htheta, R, hc, hd, hs, hhigh, Gamma, selected,
    hpayload⟩ := exists_projectiveHigh_fixedScalar_condition_with_s_zero
  refine ⟨theta, htheta, R, hc, hd, hhigh, Gamma, selected, hpayload,
    fixedScalar_noAdjacent_Gamma_card_ge hpayload, ?_⟩
  intro hlargeAgreement
  have hGammaCard := fixedScalar_noAdjacent_Gamma_card_ge hpayload
  have hGammaNonempty : Gamma.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨gamma, hgamma⟩ := hGammaNonempty
  have := hlargeAgreement gamma hgamma
  simp only [emptyAgreement, Finset.card_empty] at this
  omega

#print axioms fixedScalar_noAdjacent_Gamma_card_ge
#print axioms exists_projectiveHigh_scalarPayload_without_large_agreement

end
end ProximityPrize.SubmissionLower.FixedScalarIncidencePayloadLoss6900
