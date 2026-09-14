import LowReceivedDirectionScalarSplit1331196900
import Order2ProtocolBadFamily6900

/-!
# Exact two-high-row cut for the universal score-6900 endpoint

Once the second received row is in the surviving degree-`133120` branch, a
bad selected family with more than one seed also forces the canonical
interpolant of the first row above code degree.  Indeed, if the first row is
a degree-`131071` codeword, then at every nonzero seed the selected
interpolant can be divided by the seed after subtracting that codeword.  This
puts the second row in the projected Reed--Solomon code on the same agreement
set, contradicting the retained bad-row witness.

This is a universal endpoint reduction.  It makes no Full187/source claim.
-/

namespace ProximityPrize.SubmissionLower.UniversalBothRowsHighEndpointCut6900

open Polynomial
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.AffineLineBadFamilyContract6900
open ProximityPrize.SubmissionLower.LowReceivedDirectionScalarSplit1331196900
open ProximityPrize.SubmissionLower.Order2ProtocolBadFamily6900
open ProximityPrize.SubmissionLower.Order2Protocol6900

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

local instance {A : Type*} : DecidableEq A := Classical.decEq A

/-- If the first received row has a global code-degree interpolant, every bad
selected seed is zero. -/
theorem low_first_row_bad_family_card_le_one
    {I K : Type} [Fintype I] [Field K] [Fintype K]
    [CharP K 2130706433]
    (nodes : I ↪ K) (u0 u1 : I → K) (V0 : K[X])
    (hV0degree : V0.natDegree ≤ 131071)
    (hV0eval : ∀ i, V0.eval (nodes i) = u0 i)
    (seeds : Finset K) (A : K → Finset I)
    (selected : K → K[X])
    (hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ 131071)
    (hagrees : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    (hbad : ∀ gamma ∈ seeds, ∃ j : Fin 2,
      LinearCode.projectedWord (![u0, u1] j) (A gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (A gamma)) :
    seeds.card ≤ 1 := by
  classical
  have hsubset : seeds ⊆ ({0} : Finset K) := by
    intro gamma hgamma
    by_contra hgammaZero
    have hgammaNe : gamma ≠ 0 := by simpa using hgammaZero
    let P1 : K[X] :=
      C gamma⁻¹ * (selected gamma - V0)
    have hP1degree : P1.natDegree ≤ 131071 := by
      dsimp only [P1]
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_sub_le _ _).trans
          (max_le (hdegree gamma hgamma) hV0degree))
    have hP1eval : ∀ i ∈ A gamma, P1.eval (nodes i) = u1 i := by
      intro i hi
      dsimp only [P1]
      rw [eval_mul, eval_C, eval_sub, hagrees gamma hgamma i hi,
        hV0eval i]
      field_simp [hgammaNe]
      ring
    have hzero :
        LinearCode.projectedWord u0 (A gamma) ∈
          LinearCode.projectedCodeSubmod
            (ReedSolomon.code nodes 131072) (A gamma) := by
      exact projected_mem_of_polynomial nodes u0 (A gamma) 131071 V0
        hV0degree (fun i _ ↦ hV0eval i)
    have hone :
        LinearCode.projectedWord u1 (A gamma) ∈
          LinearCode.projectedCodeSubmod
            (ReedSolomon.code nodes 131072) (A gamma) := by
      exact projected_mem_of_polynomial nodes u1 (A gamma) 131071 P1
        hP1degree hP1eval
    obtain ⟨j, hj⟩ := hbad gamma hgamma
    fin_cases j
    · exact hj hzero
    · exact hj hone
  exact (Finset.card_le_card hsubset).trans (by simp)

/-- The genuinely open source/count theorem after both exact scalar/codeword
cuts. -/
def UniversalBothRowsHighBadFamilyBound
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) : Prop :=
  ∀ (U : Fin 2 → I → K) (seeds : Finset K)
      (A : K → Finset I) (selected : K → K[X]),
    (∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071) →
    (∀ gamma ∈ seeds, 180413 ≤ (A gamma).card) →
    (∀ gamma ∈ seeds, ∀ i ∈ A gamma,
      (selected gamma).eval (nodes i) = U 0 i + gamma * U 1 i) →
    (∀ gamma ∈ seeds, ∃ j : Fin 2,
      LinearCode.projectedWord (U j) (A gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (A gamma)) →
    131072 ≤ (receivedDirectionInterpolant nodes (U 0)).natDegree →
    133120 ≤ (receivedDirectionInterpolant nodes (U 1)).natDegree →
    seeds.card ≤ 254684620614660120

/-- The two scalar/codeword cuts reduce the exact bad-family contract to the
two-high-row predicate above. -/
theorem selectedBadGivenSetsBound_of_bothRowsHigh
    {I K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2130706433]
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (hhigh : UniversalBothRowsHighBadFamilyBound nodes) :
    SelectedBadGivenSetsBound nodes 131071 81731
      254684620614660120 := by
  intro U seeds A selected hdegree hcard hagreement hbad
  have hcard' : ∀ gamma ∈ seeds, 180413 ≤ (A gamma).card := by
    intro gamma hgamma
    have h := hcard gamma hgamma
    omega
  have hbad' : ∀ gamma ∈ seeds, ∃ j : Fin 2,
      LinearCode.projectedWord (![U 0, U 1] j) (A gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (A gamma) := by
    intro gamma hgamma
    obtain ⟨j, hj⟩ := hbad gamma hgamma
    refine ⟨j, ?_⟩
    fin_cases j <;> simpa using hj
  let V1 := receivedDirectionInterpolant nodes (U 1)
  by_cases hV1small : V1.natDegree ≤ 133119
  · exact Nat.le_of_lt
      (low_received_direction_bad_family_lt_mca
        (nodes := nodes) hI (U 0) (U 1) V1 hV1small
        (fun i ↦ receivedDirectionInterpolant_eval nodes (U 1) i)
        seeds A selected hdegree hcard' hagreement hbad')
  · have hV1 : 133120 ≤ V1.natDegree := by omega
    let V0 := receivedDirectionInterpolant nodes (U 0)
    by_cases hV0small : V0.natDegree ≤ 131071
    · exact (low_first_row_bad_family_card_le_one nodes (U 0) (U 1) V0
          hV0small
          (fun i ↦ receivedDirectionInterpolant_eval nodes (U 0) i)
          seeds A selected hdegree hagreement hbad').trans (by norm_num)
    · have hV0 : 131072 ≤ V0.natDegree := by omega
      exact hhigh U seeds A selected hdegree hcard' hagreement hbad hV0 hV1

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : CharP IRSProfile.Field 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

abbrev UniversalBothRowsHighBadFamilyBound6900 : Prop :=
  UniversalBothRowsHighBadFamilyBound IRSProfile.domain

theorem protocolClaim6900_of_bothRowsHigh
    (hhigh : UniversalBothRowsHighBadFamilyBound6900) :
    ProtocolClaim 6900 Order2Protocol6900.radiusNumerator
      Order2Protocol6900.radiusDenominator :=
  protocolClaim6900_of_bad_family
    (by
      have hI : Fintype.card IRSProfile.Index = 262144 := by
        norm_num [IRSProfile.Index]
      have h := selectedBadGivenSetsBound_of_bothRowsHigh
        IRSProfile.domain hI hhigh
      simpa [TargetBadFamilyBound6900, Order2Protocol6900.errors,
        Order2Protocol6900.mcaBudget] using h)

end
end ProximityPrize.SubmissionLower.UniversalBothRowsHighEndpointCut6900

#print axioms ProximityPrize.SubmissionLower.UniversalBothRowsHighEndpointCut6900.low_first_row_bad_family_card_le_one
#print axioms ProximityPrize.SubmissionLower.UniversalBothRowsHighEndpointCut6900.selectedBadGivenSetsBound_of_bothRowsHigh
#print axioms ProximityPrize.SubmissionLower.UniversalBothRowsHighEndpointCut6900.protocolClaim6900_of_bothRowsHigh
