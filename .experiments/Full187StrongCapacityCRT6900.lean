import PolynomialHermiteCRTDegree

/-!
# Full187 strong-capacity CRT adapter

This file turns the numerical predicate

`width >= 180413 * depth + 81731`

used in the conservative 103-shape audit into its exact polynomial
interpolation consequence: arbitrary Hermite residues at every agreement and
arbitrary scalar values at every error fit strictly inside that coefficient
strip.  It does not prove that a particular contact recurrence supplies the
residues or that the four packet columns propagate globally.
-/

namespace ProximityPrize.SubmissionLower.Full187StrongCapacityCRT6900

open PolynomialHermiteCRTDegree

noncomputable section

set_option autoImplicit false

variable {K Agreement Error : Type*}
  [Field K]
  [Fintype Agreement] [Nonempty Agreement]
  [Fintype Error] [Nonempty Error]

/-- Exact target specialization of mixed agreement-Hermite/error-value CRT.
The half-open coefficient strip `0 <= degree < width` is respected. -/
theorem exists_target_strong_capacity_polynomial
    (agreementNode : Agreement → K) (errorNode : Error → K)
    (hAgreement : Function.Injective agreementNode)
    (hError : Function.Injective errorNode)
    (hDisjoint : ∀ i j, agreementNode i ≠ errorNode j)
    (hAgreementCard : Fintype.card Agreement = 180413)
    (hErrorCard : Fintype.card Error = 81731)
    (depth width : Nat) (hdepth : 0 < depth)
    (hwidth : 180413 * depth + 81731 ≤ width)
    (residue : Agreement → Polynomial K) (value : Error → K) :
    ∃ P : Polynomial K,
      P.natDegree < width ∧
      (∀ i, P - residue i ∈ nodePowerIdeal agreementNode depth i) ∧
      ∀ j, P.eval (errorNode j) = value j := by
  obtain ⟨P, hPdegree, hPagreement, hPerror⟩ :=
    exists_degree_lt_agreement_mul_add_error_of_residues_values
      agreementNode errorNode hAgreement hError hDisjoint depth hdepth
      residue value
  have hbound :
      Fintype.card Agreement * depth + Fintype.card Error ≤ width := by
    rw [hAgreementCard, hErrorCard]
    exact hwidth
  exact ⟨P, hPdegree.trans_le hbound, hPagreement, hPerror⟩

/-- Arithmetic identity behind the target's strong capacity threshold. -/
theorem target_strong_capacity_size :
    262144 - 180413 = 81731 := by
  norm_num

#print axioms exists_target_strong_capacity_polynomial
#print axioms target_strong_capacity_size

end


end ProximityPrize.SubmissionLower.Full187StrongCapacityCRT6900
