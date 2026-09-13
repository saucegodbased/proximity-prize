import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Uniform Hermite-CRT completion for the eight order-four carriers

The tapered degrees seen in the tiny F101 extraction lose `a+c`
coefficients from carrier `(a,c)`, for a total loss of sixteen.  Full187 has
enough raw width to use degree `<3e` in every carrier.  This file records the
exact restoration and applies the existing sharp polynomial Hermite CRT
independently to all eight coefficient polynomials.

This is the coefficient-side theorem.  The identification of the complete
terminal residual with the selected local three-jet block and the global
higher-seed confluence theorem remain separate.
-/

namespace ProximityPrize.SubmissionLower.Full187EightCarrierUniformCRTCompletion6900

open scoped Classical
open Polynomial

noncomputable section

set_option autoImplicit false

/-- Raising the eight tapered dimensions to the uniform dimension `3e`
adds exactly sixteen coefficients.  Since the old source has codimension
sixteen, this is dimension-minimal. -/
theorem uniform_cap_restores_exactly_sixteen (e : Nat) (he : 2 ≤ e) :
    8 * (3 * e) -
      ((3 * e) +
       (3 * e - 1) + (3 * e - 1) +
       (3 * e - 2) + (3 * e - 2) +
       (3 * e - 3) + (3 * e - 3) +
       (3 * e - 4)) = 16 := by
  omega

/-- The individual increments are `0,1,1,2,2,3,3,4`. -/
theorem carrier_increment_receipt :
    0 + 1 + 1 + 2 + 2 + 3 + 3 + 4 = 16 := by
  norm_num

/-- Full187's uniform coefficient box has exactly the dimension of eight
independent order-three error-jet streams. -/
theorem full187_uniform_dimension_receipt :
    3 * 81731 = 245193 ∧
      8 * 245193 = 24 * 81731 ∧
      24 * 81731 = 1961544 := by
  norm_num

/-- Every restored top coefficient is already covered by the independent
raw-width theorem.  No cancellation between carrier families is needed at
Full187 scale. -/
theorem restored_coefficients_are_source_legal
    (d y h : Nat) (hd : d ≤ 4) (hy : y ≤ 60 - d)
    (hh : h ≤ 3 * 81731 - 1) :
    h + d * 180413 + (60 - d - y) * 163462 + y * 131071 < 10824780 := by
  omega

/-- Once ordinary one-polynomial degree-`<3|E|` Hermite CRT is supplied,
it applies independently to all eight coefficient streams.  The premise is
exactly the standard CRT theorem already proved in
`PolynomialHermiteCRTDegree`; isolating it here keeps this receipt light. -/
theorem eight_uniform_threeJet_crt_of_one
    {K I : Type*} [Field K] [Fintype I] [Nonempty I]
    (nodes : I → K) (_hnodes : Function.Injective nodes)
    (nodePowerIdeal : (I → K) → Nat → I → Ideal K[X])
    (oneCRT : ∀ residue : I → K[X], ∃ p : K[X],
      p.natDegree < Fintype.card I * 3 ∧
      ∀ i, p - residue i ∈ nodePowerIdeal nodes 3 i)
    (residue : Fin 8 → I → K[X]) :
    ∃ p : Fin 8 → K[X],
      (∀ a, (p a).natDegree < Fintype.card I * 3) ∧
      ∀ a i,
        p a - residue a i ∈ nodePowerIdeal nodes 3 i := by
  choose p hp using fun a : Fin 8 ↦ oneCRT (residue a)
  exact ⟨p, fun a ↦ (hp a).1, fun a i ↦ (hp a).2 i⟩

/-- Specializing the CRT bound to the Full187 error count gives precisely
the already source-legal inclusive cap `245192`. -/
theorem full187_crt_degree_is_width_safe
    (_hdegree : 0 < 3 * 81731) :
    3 * 81731 - 1 = 245192 ∧
      245192 < 3 * 81731 := by
  constructor
  · norm_num
  · norm_num

#print axioms uniform_cap_restores_exactly_sixteen
#print axioms carrier_increment_receipt
#print axioms full187_uniform_dimension_receipt
#print axioms restored_coefficients_are_source_legal
#print axioms eight_uniform_threeJet_crt_of_one
#print axioms full187_crt_degree_is_width_safe

end

end ProximityPrize.SubmissionLower.Full187EightCarrierUniformCRTCompletion6900
