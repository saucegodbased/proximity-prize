import WeightedScalarListW1332216900

/-!
# W=133221 same-witness endpoint arithmetic

This file deliberately states the bridge without importing the current
DataEleven module chain: that chain contains the legacy local declaration in
`V6`, which conflicts with the newer Mathlib valuation module pulled by the
finite-prefix stack.  The theorem below has exactly the quantifiers used after
destructuring the DataEleven scalar witness and isolates that integration issue
without weakening the mathematical statement.
-/
namespace ProximityPrize.SubmissionLower.DataElevenWeightedScalarW133221Endpoint6900

open Polynomial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- Any retained injected family of degree bounded by the literal low-E
window forces the endpoint excess `e - (max c d + q) >= 2151`.

The hypotheses are universal in the field, node set, received word, and seed
family.  Neither Frobenius fixedness nor the modular residual equation is used.
Those are extra hypotheses on the DataEleven witness, so this theorem applies
to that same witness once its `Good/scalar/centre` fields are exposed. -/
theorem retained_same_witness_excess_ge_2151
    {Seed K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
    (nodes received : I → K) (hinjNodes : Function.Injective nodes)
    (hI : Fintype.card I = 262144)
    (selected : Finset Seed) (scalar : Seed → K[X])
    (hinjScalar : Set.InjOn scalar (↑selected : Set Seed))
    (e c d q : Nat)
    (hdegree : ∀ s ∈ selected,
      (scalar s).natDegree ≤ ((131071 + e) - max c d) - q)
    (hagreement : ∀ s ∈ selected, 180413 ≤
      (Finset.univ.filter fun i ↦
        (scalar s).eval (nodes i) = received i).card)
    (hretained : 253511670984674103 ≤ selected.card) :
    max c d + q + 2151 ≤ e := by
  have hW :=
    WeightedScalarListW1332216900.scalarized_large_family_degree_obstruction
      nodes received hinjNodes hI selected scalar hinjScalar
      (((131071 + e) - max c d) - q) hdegree hagreement hretained
  omega

end
end ProximityPrize.SubmissionLower.DataElevenWeightedScalarW133221Endpoint6900

#print axioms ProximityPrize.SubmissionLower.DataElevenWeightedScalarW133221Endpoint6900.retained_same_witness_excess_ge_2151
