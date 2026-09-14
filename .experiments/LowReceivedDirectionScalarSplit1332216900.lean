import ProximityPrize.Benchmark.TargetLower
import WeightedScalarListW1332216900

/-!
# Received-direction scalar split through degree 133221

This deliberately uses the already proved unconditional weighted scalar-list
theorem, rather than the newer but weaker degree-132210 endpoint.  No
fixed-gauge hypothesis enters this adapter: the scalar-list theorem is applied
only to the image of `P_gamma - gamma * V`, which agrees with the one fixed
word `u0`.
-/

namespace ProximityPrize.SubmissionLower.LowReceivedDirectionScalarSplit1332216900

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

local instance {A : Type*} : DecidableEq A := Classical.decEq A

variable {K I : Type} [Field K] [Fintype K] [Fintype I]
  [CharP K 2130706433]

def scalarized (V : K[X]) (selected : K → K[X]) (gamma : K) : K[X] :=
  selected gamma - Polynomial.C gamma * V

theorem scalarized_degree133221
    (V : K[X]) (selected : K → K[X]) (gamma : K)
    (hV : V.natDegree ≤ 133221)
    (hP : (selected gamma).natDegree ≤ 131071) :
    (scalarized V selected gamma).natDegree ≤ 133221 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact hP.trans (by norm_num)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hV

theorem scalarized_eval
    (V : K[X]) (selected : K → K[X]) (gamma x u0 u1 : K)
    (hP : (selected gamma).eval x = u0 + gamma * u1)
    (hV : V.eval x = u1) :
    (scalarized V selected gamma).eval x = u0 := by
  simp only [scalarized, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, hP, hV]
  ring

theorem scalarized_injOn_of_degree_gt
    (V : K[X]) (selected : K → K[X]) (Gamma : Finset K)
    (hV : 131071 < V.natDegree)
    (hP : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071) :
    Set.InjOn (scalarized V selected) (↑Gamma : Set K) := by
  intro a ha b hb heq
  by_contra hab
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hVne : V ≠ 0 := by
    intro hz
    simp [hz] at hV
  have hidentity :
      Polynomial.C (a - b) * V = selected a - selected b := by
    simp only [scalarized] at heq
    rw [Polynomial.C_sub]
    linear_combination -heq
  have hleft :
      (Polynomial.C (a - b) * V).natDegree = V.natDegree := by
    rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hab') hVne,
      Polynomial.natDegree_C, Nat.zero_add]
  have hright : (selected a - selected b).natDegree ≤ 131071 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hP a ha) (hP b hb))
  rw [hidentity] at hleft
  omega

theorem projected_mem_of_polynomial
    (nodes : I ↪ K) (word : I → K) (A : Finset I) (w : Nat)
    (P : K[X]) (hP : P.natDegree ≤ w)
    (heval : ∀ i ∈ A, P.eval (nodes i) = word i) :
    LinearCode.projectedWord word A ∈
      LinearCode.projectedCodeSubmod (ReedSolomon.code nodes (w + 1)) A := by
  classical
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨ReedSolomon.evalOnPoints nodes P,
    ReedSolomon.evalOnPoints_mem_code_of_degree_lt ?_, ?_⟩
  · rcases eq_or_ne P 0 with hzero | hnonzero
    · simp [hzero]
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hnonzero]
      omega
  · funext i
    exact (heval i.1 i.2).symm

theorem low_received_direction_bad_family_lt_mca
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (u0 u1 : I → K) (V : K[X])
    (hVdegree : V.natDegree ≤ 133221)
    (hVeval : ∀ i, V.eval (nodes i) = u1 i)
    (Gamma : Finset K) (agreement : K → Finset I)
    (selected : K → K[X])
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    (hbad : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (![u0, u1] r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (agreement gamma)) :
    Gamma.card < 254684620614660120 := by
  classical
  by_cases hsmall : V.natDegree ≤ 131071
  · have hempty : Gamma = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro gamma hgamma
      obtain ⟨r, hr⟩ := hbad gamma hgamma
      have hzero :
          LinearCode.projectedWord u0 (agreement gamma) ∈
            LinearCode.projectedCodeSubmod
              (ReedSolomon.code nodes 131072) (agreement gamma) := by
        apply projected_mem_of_polynomial nodes u0 (agreement gamma) 131071
          (scalarized V selected gamma)
          (by
            apply (Polynomial.natDegree_sub_le _ _).trans
            apply max_le
            · exact hdegree gamma hgamma
            · exact (Polynomial.natDegree_C_mul_le _ _).trans hsmall)
        intro i hi
        exact scalarized_eval V selected gamma (nodes i) (u0 i) (u1 i)
          (hagrees gamma hgamma i hi) (hVeval i)
      have hone :
          LinearCode.projectedWord u1 (agreement gamma) ∈
            LinearCode.projectedCodeSubmod
              (ReedSolomon.code nodes 131072) (agreement gamma) := by
        exact projected_mem_of_polynomial nodes u1 (agreement gamma) 131071 V
          hsmall (fun i _ ↦ hVeval i)
      fin_cases r
      · exact hr hzero
      · exact hr hone
    simp [hempty]
  · have hlarge : 131071 < V.natDegree := Nat.lt_of_not_ge hsmall
    have hinj : Set.InjOn (scalarized V selected) (↑Gamma : Set K) :=
      scalarized_injOn_of_degree_gt V selected Gamma hlarge hdegree
    have hcount :=
      WeightedScalarListW1332216900.scalarized_seed_family_card_le
        nodes u0 nodes.injective hI Gamma (scalarized V selected) hinj
        (fun gamma hgamma ↦
          scalarized_degree133221 V selected gamma hVdegree
            (hdegree gamma hgamma))
        (fun gamma hgamma ↦ by
          apply (hcard gamma hgamma).trans
          apply Finset.card_le_card
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            scalarized_eval V selected gamma (nodes i) (u0 i) (u1 i)
              (hagrees gamma hgamma i hi) (hVeval i)⟩)
    exact hcount.trans_lt (by norm_num)

def receivedDirectionInterpolant
    (nodes : I ↪ K) (u1 : I → K) : K[X] :=
  Lagrange.interpolate Finset.univ nodes u1

theorem receivedDirectionInterpolant_eval
    (nodes : I ↪ K) (u1 : I → K) (i : I) :
    (receivedDirectionInterpolant nodes u1).eval (nodes i) = u1 i := by
  exact Lagrange.eval_interpolate_at_node u1 nodes.injective.injOn
    (Finset.mem_univ i)

/-- Exhaustive theorem-facing split at the strongest currently proved
unconditional scalar-list endpoint. -/
theorem scalar_count_or_received_direction_degree_ge
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (u0 u1 : I → K)
    (Gamma : Finset K) (agreement : K → Finset I)
    (selected : K → K[X])
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ Gamma, 180413 ≤ (agreement gamma).card)
    (hagrees : ∀ gamma ∈ Gamma, ∀ i ∈ agreement gamma,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    (hbad : ∀ gamma ∈ Gamma, ∃ r : Fin 2,
      LinearCode.projectedWord (![u0, u1] r) (agreement gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (agreement gamma)) :
    Gamma.card < 254684620614660120 ∨
      133222 ≤ (receivedDirectionInterpolant nodes u1).natDegree := by
  let V := receivedDirectionInterpolant nodes u1
  by_cases hV : V.natDegree ≤ 133221
  · left
    exact low_received_direction_bad_family_lt_mca nodes hI u0 u1 V hV
      (fun i ↦ receivedDirectionInterpolant_eval nodes u1 i)
      Gamma agreement selected hdegree hcard hagrees hbad
  · right
    change 133222 ≤ V.natDegree
    omega

theorem target_high_branch_residual_degree_receipt :
    133222 - 131072 = 2150 ∧ 133222 - 131071 = 2151 := by
  norm_num

#print axioms low_received_direction_bad_family_lt_mca
#print axioms scalar_count_or_received_direction_degree_ge

end
end ProximityPrize.SubmissionLower.LowReceivedDirectionScalarSplit1332216900
