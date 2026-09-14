import ProjectiveHighReciprocalCrossCountergate6900
import TZeroReciprocalResiduePlaneCountergate6900

/-! Small algebraic seed for the scoped `s=0` scalar countergate. -/

namespace ProximityPrize.SubmissionLower.FixedScalarSmallSReciprocalSeed6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open PolynomialReciprocalAlignedControl6900
open ProjectiveHighReciprocalCrossCountergate6900
open TZeroReciprocalResiduePlaneCountergate6900
open UniversalProjectiveHighDirectionEndpointCut6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem hostileDenominator_ne_zero (theta : ExtensionField) :
    denominator theta 2049 ≠ 0 := by
  exact denominator_ne_zero theta 2049 (by omega)

theorem hostileDenominator_natDegree (theta : ExtensionField) :
    (denominator theta 2049).natDegree = 2049 := by
  exact denominator_degree theta 2049

theorem hostileDenominator_root_free (theta : ExtensionField)
    (htheta : sigma theta ≠ theta) (i : Index) :
    (denominator theta 2049).eval (IRSProfile.domain i) ≠ 0 := by
  simpa only [denominator] using
    power_denominator_root_free sigma theta
      (IRSProfile.domain i) 2049 htheta (sigma_domain i)

theorem hostileDenominator_conjugate_coprime (theta : ExtensionField)
    (htheta : sigma theta ≠ theta) :
    IsCoprime (denominator theta 2049)
      ((denominator theta 2049).map sigma) := by
  simpa only [denominator] using
    power_denominator_conjugate_coprime sigma theta 2049 htheta

theorem exists_reciprocalCross_full_fields (E : ExtensionField[X])
    (hE : E ≠ 0) (hroot : ∀ i, E.eval (IRSProfile.domain i) ≠ 0) :
    ∃ R : AlignedCrossData (reciprocalDomainU E) E.natDegree,
      R.E = E ∧ R.L = 1 ∧ R.M = -1 ∧ R.c = 1 ∧ R.d = 0 ∧
      R.N = -1 := by
  let R := reciprocalCross E (fun i ↦ IRSProfile.domain i)
    hE hroot (fun i ↦ sigma_domain i)
  exact ⟨R, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms hostileDenominator_ne_zero
#print axioms hostileDenominator_natDegree
#print axioms hostileDenominator_root_free
#print axioms hostileDenominator_conjugate_coprime
#print axioms exists_reciprocalCross_full_fields

end
end ProximityPrize.SubmissionLower.FixedScalarSmallSReciprocalSeed6900
