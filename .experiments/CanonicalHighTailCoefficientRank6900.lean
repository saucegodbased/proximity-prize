import UniversalProjectiveHighDirectionEndpointCut6900

/-!
# The exact coefficient-rank content of the projective high-tail endpoint

`CanonicalHighTailDirectionIndependent` says that every nonzero constant
combination of the two received rows has canonical interpolant degree at least
`133120`.  This file packages the equivalent linear-algebraic fact needed by
downstream consumers: after restricting coefficients to degrees at least
`133120`, the two canonical interpolants are linearly independent.  Thus their
tail span has finrank exactly two.

The result is also exported directly from the same-witness DataEleven leaf.
-/

namespace ProximityPrize.SubmissionLower.CanonicalHighTailCoefficientRank6900

open Polynomial ProximityPrize.Benchmark
open LowReceivedDirectionScalarSplit1331196900
open UniversalProjectiveHighDirectionEndpointCut6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- The canonical interpolant of each of the two received rows. -/
def canonicalReceivedInterpolant
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K) (r : Fin 2) : K[X] :=
  receivedDirectionInterpolant nodes (U r)

/-- The coefficient tail beginning in degree `133120`.  The codomain is an
honest `K`-module, so it can be fed directly to rank and span consumers. -/
def canonicalHighCoefficientTail
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K) (r : Fin 2) :
    {n : Nat // 133120 ≤ n} → K :=
  fun n ↦ (canonicalReceivedInterpolant nodes U r).coeff n

theorem receivedDirectionInterpolant_linear_combination
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K) (a b : K) :
    receivedDirectionInterpolant nodes
        (fun i ↦ a * U 0 i + b * U 1 i) =
      C a * canonicalReceivedInterpolant nodes U 0 +
        C b * canonicalReceivedInterpolant nodes U 1 := by
  change Lagrange.interpolate Finset.univ nodes
      (fun i ↦ a * U 0 i + b * U 1 i) = _
  change Lagrange.interpolate Finset.univ nodes
      (a • U 0 + b • U 1) = _
  rw [map_add, map_smul, map_smul]
  simp only [canonicalReceivedInterpolant, receivedDirectionInterpolant,
    smul_eq_C_mul]

/-- Exact bridge: the two high coefficient tails are linearly independent. -/
theorem canonicalHighCoefficientTail_linearIndependent
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K)
    (hhigh : CanonicalHighTailDirectionIndependent nodes U) :
    LinearIndependent K (canonicalHighCoefficientTail nodes U) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum r
  have htailZero : ∀ n : Nat, 133120 ≤ n →
      (C (g 0) * canonicalReceivedInterpolant nodes U 0 +
        C (g 1) * canonicalReceivedInterpolant nodes U 1).coeff n = 0 := by
    intro n hn
    have h := congrFun hsum (⟨n, hn⟩ : {m : Nat // 133120 ≤ m})
    simpa only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul,
      canonicalHighCoefficientTail, coeff_add, coeff_C_mul] using h
  have hdegreeLow :
      (C (g 0) * canonicalReceivedInterpolant nodes U 0 +
        C (g 1) * canonicalReceivedInterpolant nodes U 1).natDegree ≤ 133119 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    exact htailZero n (by omega)
  have hnoDirection : ¬ (g 0 ≠ 0 ∨ g 1 ≠ 0) := by
    intro hnonzero
    have hdegreeHigh := hhigh (g 0) (g 1) hnonzero
    rw [receivedDirectionInterpolant_linear_combination] at hdegreeHigh
    omega
  have hzero0 : g 0 = 0 := by
    by_contra hne
    exact hnoDirection (Or.inl hne)
  have hzero1 : g 1 = 0 := by
    by_contra hne
    exact hnoDirection (Or.inr hne)
  fin_cases r
  · exact hzero0
  · exact hzero1

/-- Rank form of the same bridge. -/
theorem canonicalHighCoefficientTail_span_finrank_eq_two
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K)
    (hhigh : CanonicalHighTailDirectionIndependent nodes U) :
    Module.finrank K
      (Submodule.span K (Set.range (canonicalHighCoefficientTail nodes U))) = 2 := by
  simpa using finrank_span_eq_card
    (canonicalHighCoefficientTail_linearIndependent nodes U hhigh)

/-- Generic root-rigidity lemma used to test rational-cross consumers without
specializing the polynomial root argument to the very large benchmark field.
If `E*P` agrees with a nonzero affine polynomial on all nodes and
`deg E + d` fits below the node count, then `P` cannot have degree `< d`. -/
theorem affine_reciprocal_interpolant_not_degree_lt
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (E P : K[X]) (e d : Nat)
    (hcard : e + d ≤ Fintype.card I) (hcardTwo : 2 ≤ Fintype.card I)
    (heTwo : 2 ≤ e) (hEdegree : E.natDegree = e)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0)
    (hcleared : ∀ i, E.eval (nodes i) * P.eval (nodes i) = a * nodes i + b) :
    ¬ P.natDegree < d := by
  classical
  let linear : K[X] := Polynomial.C a * Polynomial.X + Polynomial.C b
  have hlinearDegree : linear.natDegree ≤ 1 := by
    dsimp only [linear]
    exact (natDegree_add_le _ _).trans
      (max_le
        ((natDegree_C_mul_le a Polynomial.X).trans (by simp))
        (by simp))
  have hlinearNe : linear ≠ 0 := by
    intro hzero
    have ha : a = 0 := by
      have h := congrArg (fun Q : K[X] ↦ Q.coeff 1) hzero
      simpa [linear] using h
    have hb : b = 0 := by
      have h := congrArg (fun Q : K[X] ↦ Q.coeff 0) hzero
      simpa [linear] using h
    exact hab.elim (fun h ↦ h ha) (fun h ↦ h hb)
  intro hPdegree
  let H : K[X] := E * P - linear
  have hHdegree : H.natDegree < Fintype.card I := by
    apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · apply natDegree_mul_le.trans_lt
      omega
    · omega
  have hHeval : ∀ i, H.eval (nodes i) = 0 := by
    intro i
    dsimp only [H, linear]
    simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X]
    rw [hcleared]
    ring
  have hHzero : H = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      H (Finset.univ.image nodes)
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hHeval i
    · rw [Finset.card_image_of_injective _ nodes.injective,
        Finset.card_univ]
      exact hHdegree
  have hproduct : E * P = linear := sub_eq_zero.mp hHzero
  have hdiv : E ∣ linear := ⟨P, hproduct.symm⟩
  have hdegreeDiv := natDegree_le_of_dvd hdiv hlinearNe
  rw [hEdegree] at hdegreeDiv
  omega

#print axioms receivedDirectionInterpolant_linear_combination
#print axioms canonicalHighCoefficientTail_linearIndependent
#print axioms canonicalHighCoefficientTail_span_finrank_eq_two
#print axioms affine_reciprocal_interpolant_not_degree_lt

end
end ProximityPrize.SubmissionLower.CanonicalHighTailCoefficientRank6900
