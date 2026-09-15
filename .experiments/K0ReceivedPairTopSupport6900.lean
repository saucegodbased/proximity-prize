import UniversalProjectiveHighDirectionEndpointCut6900

/-!
# A bad two-row family exposes a received coefficient above the agreement cut

The locator-lifted order-seven approximant only needs one of the two full
received interpolants to have degree at least the agreement size.  This file
proves that target-facing fact directly.  It is deliberately about the full
received pair, not the much smaller projective scalar direction used by the
weighted scalar endpoint.

If both received interpolants had degree below `180413`, then for every seed
the selected polynomial and the corresponding received affine combination
would be two degree-`<180413` polynomials agreeing at `180413` distinct
points, hence equal globally.  Two distinct seeds then recover both received
rows as degree-`<=131071` Reed--Solomon words, contradicting the retained
bad-row hypothesis.
-/

namespace ProximityPrize.SubmissionLower.K0ReceivedPairTopSupport6900

open Polynomial
open ProximityPrize.SubmissionLower.AffineLineBadFamilyContract6900
open ProximityPrize.SubmissionLower.LowReceivedDirectionScalarSplit1331196900
open ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

local instance {T : Type*} : DecidableEq T := Classical.decEq T

/-- On the projective-high branch, the canonical received combination at
the *actual* boundary parameter has degree at least the agreement size.  The
key point is that its degree is already above the selected-polynomial cap,
so agreement at `180413` points cannot be a polynomial identity below the
agreement cut. -/
theorem projectiveHigh_combination_degree_ge_agreement
    {I K : Type} [Fintype I] [Nonempty I]
    [Field K] [Fintype K] [CharP K 2130706433]
    (nodes : I ↪ K)
    (U : Fin 2 → I → K)
    (hprojective : CanonicalHighTailDirectionIndependent nodes U)
    (gamma : K)
    (A : Finset I)
    (P : K[X])
    (hPdegree : P.natDegree ≤ 131071)
    (hcard : 180413 ≤ A.card)
    (hagrees : ∀ i ∈ A,
      P.eval (nodes i) = U 0 i + gamma * U 1 i) :
    180413 ≤
      (receivedDirectionInterpolant nodes
        (fun i ↦ U 0 i + gamma * U 1 i)).natDegree := by
  classical
  let V : K[X] := receivedDirectionInterpolant nodes
    (fun i ↦ U 0 i + gamma * U 1 i)
  have hVhigh : 133120 ≤ V.natDegree := by
    dsimp only [V]
    simpa only [one_mul] using
      hprojective 1 gamma (Or.inl one_ne_zero)
  by_contra hlow
  change ¬ 180413 ≤ V.natDegree at hlow
  have hVdegree : V.natDegree ≤ 180412 := by omega
  have hAcard : 180412 < A.card := by omega
  have hPV : P = V := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq A
      nodes.injective.injOn
    · apply ProximityPrize.SubmissionLower.RCN147.degree_lt_card_of_natDegree_le
        A 180412 hAcard
      exact hPdegree.trans (by norm_num)
    · exact ProximityPrize.SubmissionLower.RCN147.degree_lt_card_of_natDegree_le
        A 180412 hAcard V hVdegree
    · intro i hi
      exact (hagrees i hi).trans <|
        (receivedDirectionInterpolant_eval nodes
          (fun j ↦ U 0 j + gamma * U 1 j) i).symm
  rw [← hPV] at hVhigh
  omega

/-- Two distinct bad seeds force one of the two canonical full received
interpolants to reach the agreement degree. -/
theorem max_received_interpolant_degree_ge_agreement
    {I K : Type} [Fintype I] [Nonempty I]
    [Field K] [Fintype K] [CharP K 2130706433]
    (nodes : I ↪ K)
    (U : Fin 2 → I → K)
    (Gamma : Finset K)
    (agreement : K → Finset I)
    (selected : K → K[X])
    (hGamma : 2 ≤ Gamma.card)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ Gamma,
      180413 ≤ (agreement gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (nodes i) = U 0 i + gamma * U 1 i)
    (hbad : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (U r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (agreement gamma)) :
    180413 ≤ max
      (receivedDirectionInterpolant nodes (U 0)).natDegree
      (receivedDirectionInterpolant nodes (U 1)).natDegree := by
  classical
  let V0 : K[X] := receivedDirectionInterpolant nodes (U 0)
  let V1 : K[X] := receivedDirectionInterpolant nodes (U 1)
  by_contra hlow
  change ¬ 180413 ≤ max V0.natDegree V1.natDegree at hlow
  have hV0 : V0.natDegree ≤ 180412 := by
    omega
  have hV1 : V1.natDegree ≤ 180412 := by
    omega
  have hglobal : ∀ gamma ∈ Gamma,
      selected gamma = V0 + C gamma * V1 := by
    intro gamma hgamma
    have hgammaCard := hcard gamma hgamma
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (agreement gamma)
      nodes.injective.injOn
    · apply ProximityPrize.SubmissionLower.RCN147.degree_lt_card_of_natDegree_le
        (agreement gamma) 180412
      · omega
      · exact (hdegree gamma hgamma).trans (by norm_num)
    · apply ProximityPrize.SubmissionLower.RCN147.degree_lt_card_of_natDegree_le
        (agreement gamma) 180412
      · omega
      · exact (Polynomial.natDegree_add_le V0 (C gamma * V1)).trans
          (max_le hV0 ((Polynomial.natDegree_C_mul_le gamma V1).trans hV1))
    · intro i hi
      simp only [eval_add, eval_mul, eval_C]
      rw [show V0.eval (nodes i) = U 0 i by
        exact receivedDirectionInterpolant_eval nodes (U 0) i]
      rw [show V1.eval (nodes i) = U 1 i by
        exact receivedDirectionInterpolant_eval nodes (U 1) i]
      exact hagrees gamma hgamma i hi
  obtain ⟨gamma, hgamma, delta, hdelta, hne⟩ :=
    Finset.one_lt_card.mp (show 1 < Gamma.card by omega)
  have hdet : delta - gamma * (1 : K) ≠ 0 := by
    simpa [sub_ne_zero] using hne.symm
  have hdelta_on_gamma : ∀ i ∈ agreement gamma,
      (selected delta).eval (nodes i) =
        (1 : K) * U 0 i + delta * U 1 i := by
    intro i hi
    have heval := congrArg (Polynomial.eval (nodes i)) (hglobal delta hdelta)
    simpa [V0, V1, receivedDirectionInterpolant_eval] using heval
  obtain ⟨r, hr⟩ := hbad gamma hgamma
  apply hr
  exact projected_rows_mem_of_two_interpolants
    nodes 131071 U (agreement gamma) gamma 1 delta
      (selected gamma) (selected delta) hdet
      (hdegree gamma hgamma) (hdegree delta hdelta)
      (hagrees gamma hgamma) hdelta_on_gamma r

/-- Exact target arithmetic for the first boundary-capable optimized
`(M,K)=(e,2)` order-seven box. -/
theorem target_orderSeven_M_eq_errors_receipt :
    262144 - 180413 = 81731 /\
      4 * (81731 + 1) * (2 + 1) = 980784 /\
      (81731 + 30879) * (2 + 2) = 450440 /\
      980784 - 450440 = 530344 /\
      4 * 81731 + 4 ≤ 530344 /\
      37 * 180413 + 6 * 262144 + 131071 + 81731 = 8460947 /\
      8460947 < 47 * 180413 /\
      47 * 180413 - 8460947 = 18464 := by
  norm_num

#print axioms max_received_interpolant_degree_ge_agreement
#print axioms projectiveHigh_combination_degree_ge_agreement
#print axioms target_orderSeven_M_eq_errors_receipt

end
end ProximityPrize.SubmissionLower.K0ReceivedPairTopSupport6900
