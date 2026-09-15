import ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900
import K0ReceivedPairTopSupport6900
import CanonicalHighTailCoefficientRank6900

/-!
# Exact agreement-locator residual on the projective-high incidence leaf

For every *actual* seed in the retained benchmark family, let `Q_gamma` be
the canonical full-domain interpolation of `U 0 + gamma * U 1`, and let
`P_gamma` be the selected degree-`131071` polynomial.  Projective-highness
forces `Q_gamma` to have degree at least the agreement size.  Consequently
`Q_gamma - P_gamma` is nonzero, is divisible by the locator of the actual
agreement set, and the residual quotient has degree at most `81730`.

Unlike a free-standing dimension wrapper, the endpoint theorem below takes
the exact `ProjectiveHighDataElevenHighEClosedIncidenceLeaf` and keeps its
`U`, `Gamma`, `agreement`, and `selected` witnesses unchanged.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighLeafAgreementResidualFactor6900

open Polynomial ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.SupportRecurrence6900
open ProximityPrize.SubmissionLower.SupportRecurrence6900.Target
open ProximityPrize.SubmissionLower.LowReceivedDirectionScalarSplit1331196900
open ProximityPrize.SubmissionLower.ProjectiveHighDataElevenHighEClosedIncidenceFrontier6900
open ProximityPrize.SubmissionLower.K0ReceivedPairTopSupport6900
open ProximityPrize.SubmissionLower.CanonicalHighTailCoefficientRank6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP IRSProfile.Field 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- A squarefree locator at injectively indexed nodes divides every
polynomial vanishing on those nodes. -/
theorem supportLocator_dvd_of_eval_zero
    {I K : Type*} [Field K]
    (nodes : I → K) (hinj : Function.Injective nodes)
    (A : Finset I) (F : K[X])
    (hzero : ∀ i ∈ A, F.eval (nodes i) = 0) :
    supportLocator nodes A ∣ F := by
  classical
  rw [supportLocator]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C hinj hij
  · intro i hi
    exact Polynomial.dvd_iff_isRoot.mpr (hzero i hi)

/-- Generic full-domain interpolation bound at the benchmark block length. -/
theorem receivedDirectionInterpolant_degree_le_of_card
    {I K : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (hI : Fintype.card I = 262144) (u : I → K) :
    (receivedDirectionInterpolant nodes u).natDegree ≤ 262143 := by
  have hdeg := Lagrange.degree_interpolate_lt (s := Finset.univ)
    u nodes.injective.injOn
  rw [Finset.card_univ, hI] at hdeg
  by_cases hp : receivedDirectionInterpolant nodes u = 0
  · simp [hp]
  · have hn : (receivedDirectionInterpolant nodes u).natDegree < 262144 :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
    omega

def canonicalReceivedCombination
    (U : Fin 2 → Index → ExtensionField) (gamma : ExtensionField) :
    ExtensionField[X] :=
  receivedDirectionInterpolant IRSProfile.domain
    (fun i ↦ U 0 i + gamma * U 1 i)

def actualAgreementLocator
    (agreement : ExtensionField → Finset Index) (gamma : ExtensionField) :
    ExtensionField[X] :=
  supportLocator IRSProfile.domain (agreement gamma)

def actualAgreementResidual
    (U : Fin 2 → Index → ExtensionField)
    (selected : ExtensionField → ExtensionField[X])
    (gamma : ExtensionField) : ExtensionField[X] :=
  canonicalReceivedCombination U gamma - selected gamma

/-- The canonical full-domain interpolation always has degree at most
`262143`.  This is separated from the leaf argument so checking the endpoint
certificate does not unfold the large nested leaf record. -/
theorem canonicalReceivedCombination_degree_le
    (U : Fin 2 → Index → ExtensionField) (gamma : ExtensionField) :
    (canonicalReceivedCombination U gamma).natDegree ≤ 262143 := by
  unfold canonicalReceivedCombination
  exact receivedDirectionInterpolant_degree_le_of_card IRSProfile.domain
    (by norm_num [Index, IRSProfile.Index])
    (fun i ↦ U 0 i + gamma * U 1 i)

/-- The purely algebraic residual factorization.  Keeping this helper generic
prevents the elaborator from expanding the large concrete index type while
the exact leaf theorem merely supplies its hypotheses. -/
theorem agreement_residual_factor_of_bounds
    {I K : Type} [Field K] [Fintype K] [Fintype I]
    [CharP K 2130706433]
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (u : I → K) (A : Finset I) (P : K[X])
    (hQlower : 180413 ≤ (receivedDirectionInterpolant nodes u).natDegree)
    (hPdegree : P.natDegree ≤ 131071)
    (hcard : 180413 ≤ A.card)
    (hagrees : ∀ i ∈ A, P.eval (nodes i) = u i) :
    ∃ R : K[X],
      R ≠ 0 ∧
      receivedDirectionInterpolant nodes u - P =
        supportLocator nodes A * R ∧
      R.natDegree ≤ 81730 := by
  let Q : K[X] := receivedDirectionInterpolant nodes u
  let H : K[X] := supportLocator nodes A
  let D : K[X] := Q - P
  have hQupper : Q.natDegree ≤ 262143 := by
    exact receivedDirectionInterpolant_degree_le_of_card nodes hI u
  have hP_lt_Q : P.natDegree < Q.natDegree :=
    hPdegree.trans_lt ((by norm_num : 131071 < 180413).trans_le hQlower)
  have hDdegree : D.natDegree = Q.natDegree := by
    exact Polynomial.natDegree_sub_eq_left_of_natDegree_lt hP_lt_Q
  have hDne : D ≠ 0 := by
    intro hzero
    have hz : D.natDegree = 0 := by simp [hzero]
    rw [hDdegree] at hz
    omega
  have hDzero : ∀ i ∈ A, D.eval (nodes i) = 0 := by
    intro i hi
    dsimp only [D, Q]
    rw [Polynomial.eval_sub, receivedDirectionInterpolant_eval nodes u i,
      hagrees i hi, sub_self]
  have hHdivD : H ∣ D := by
    exact supportLocator_dvd_of_eval_zero nodes nodes.injective A D hDzero
  obtain ⟨R, hfactor⟩ := hHdivD
  have hHne : H ≠ 0 := (supportLocator_monic nodes A).ne_zero
  have hRne : R ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hDne hfactor
  have hRdegree : R.natDegree ≤ 81730 := by
    have hmul : (H * R).natDegree = H.natDegree + R.natDegree :=
      Polynomial.natDegree_mul hHne hRne
    have hsum : H.natDegree + R.natDegree ≤ 262143 := by
      rw [← hmul, ← hfactor, hDdegree]
      exact hQupper
    have hHcard : H.natDegree = A.card := supportLocator_natDegree nodes A
    rw [hHcard] at hsum
    omega
  refine ⟨R, hRne, ?_, hRdegree⟩
  simpa only [D, H, Q] using hfactor

/-- Affine specialization of canonical-interpolant linearity. -/
theorem receivedDirectionInterpolant_affine_combination
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K) (gamma : K) :
    receivedDirectionInterpolant nodes
        (fun i ↦ U 0 i + gamma * U 1 i) =
      canonicalReceivedInterpolant nodes U 0 +
        C gamma * canonicalReceivedInterpolant nodes U 1 := by
  simpa only [one_mul, Polynomial.C_1] using
    (receivedDirectionInterpolant_linear_combination nodes U 1 gamma)

/-- The newly established top-support hinge, specialized without changing
any witness of the exact incidence leaf. -/
theorem projectiveHigh_incidence_leaf_received_degree_lower
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected)
    {gamma : ExtensionField} (hgamma : gamma ∈ Gamma) :
    180413 ≤
      (receivedDirectionInterpolant IRSProfile.domain
        (fun i ↦ U 0 i + gamma * U 1 i)).natDegree := by
  exact projectiveHigh_combination_degree_ge_agreement
    IRSProfile.domain U
    leaf.toProjectiveHighDataElevenHighEClosedLeaf.projectiveHigh
    gamma (agreement gamma) (selected gamma)
    (leaf.selected_degree gamma hgamma)
    (leaf.agreement_card gamma hgamma)
    (leaf.selected_agrees gamma hgamma)

/-- Every actual seed on the exact projective-high incidence leaf has a
canonical, nonzero residual quotient after removing its actual agreement
locator.  The quotient degree `81730` is sharp from the available data:
`262143 - 180413 = 81730`.

The coefficient fixedness field records that the varying agreement locator
is nevertheless defined over the base field. -/
theorem projectiveHigh_incidence_leaf_residual_factor
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected)
    {gamma : ExtensionField} (hgamma : gamma ∈ Gamma) :
    ∃ R : ExtensionField[X],
      R ≠ 0 ∧
      receivedDirectionInterpolant IRSProfile.domain
          (fun i ↦ U 0 i + gamma * U 1 i) - selected gamma =
        supportLocator IRSProfile.domain (agreement gamma) * R ∧
      R.natDegree ≤ 81730 := by
  exact agreement_residual_factor_of_bounds IRSProfile.domain
    (by norm_num [Index, IRSProfile.Index])
    (fun i ↦ U 0 i + gamma * U 1 i)
    (agreement gamma) (selected gamma)
    (projectiveHigh_incidence_leaf_received_degree_lower leaf hgamma)
    (leaf.selected_degree gamma hgamma)
    (leaf.agreement_card gamma hgamma)
    (leaf.selected_agrees gamma hgamma)

/-- Endpoint-facing Padé form of the factorization.  Above the selected
degree cutoff, the product of the actual agreement locator and its short
residual is not arbitrary: every coefficient lies on the same affine
two-row canonical pencil, with the original seed `gamma` unchanged. -/
theorem projectiveHigh_incidence_leaf_residual_high_coefficients
    {U : Fin 2 → Index → ExtensionField}
    {Gamma : Finset ExtensionField}
    {agreement : ExtensionField → Finset Index}
    {selected : ExtensionField → ExtensionField[X]}
    (leaf : ProjectiveHighDataElevenHighEClosedIncidenceLeaf
      U Gamma agreement selected)
    {gamma : ExtensionField} (hgamma : gamma ∈ Gamma) :
    ∃ R : ExtensionField[X],
      R ≠ 0 ∧ R.natDegree ≤ 81730 ∧
      ∀ k : Nat, 131071 < k →
        (supportLocator IRSProfile.domain (agreement gamma) * R).coeff k =
          (canonicalReceivedInterpolant IRSProfile.domain U 0).coeff k +
            gamma *
              (canonicalReceivedInterpolant IRSProfile.domain U 1).coeff k := by
  obtain ⟨R, hRne, hfactor, hRdegree⟩ :=
    projectiveHigh_incidence_leaf_residual_factor leaf hgamma
  refine ⟨R, hRne, hRdegree, ?_⟩
  intro k hk
  have hPcoeff : (selected gamma).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((leaf.selected_degree gamma hgamma).trans_lt hk)
  have hlinear :
      receivedDirectionInterpolant IRSProfile.domain
          (fun i ↦ U 0 i + gamma * U 1 i) =
        canonicalReceivedInterpolant IRSProfile.domain U 0 +
          C gamma * canonicalReceivedInterpolant IRSProfile.domain U 1 := by
    exact receivedDirectionInterpolant_affine_combination
      IRSProfile.domain U gamma
  have hcoeff := congrArg (fun P : ExtensionField[X] ↦ P.coeff k) hfactor
  rw [Polynomial.coeff_sub, hPcoeff, sub_zero, hlinear,
    Polynomial.coeff_add, Polynomial.coeff_C_mul] at hcoeff
  exact hcoeff.symm

/-- The exact agreement locator used by the residual factorization is monic,
has the actual agreement cardinality as degree, and is coefficientwise fixed
by the target Frobenius. -/
theorem actualAgreementLocator_shape
    (agreement : ExtensionField → Finset Index) (gamma : ExtensionField) :
    (supportLocator IRSProfile.domain (agreement gamma)).Monic ∧
    (supportLocator IRSProfile.domain (agreement gamma)).natDegree =
      (agreement gamma).card ∧
    ∀ l : Nat,
      sigma ((supportLocator IRSProfile.domain (agreement gamma)).coeff l) =
        (supportLocator IRSProfile.domain (agreement gamma)).coeff l := by
  refine ⟨supportLocator_monic IRSProfile.domain (agreement gamma),
    supportLocator_natDegree IRSProfile.domain (agreement gamma), ?_⟩
  intro l
  exact supportLocator_coeff_map_fixed sigma IRSProfile.domain sigma_domain
    (agreement gamma) l

end
end ProximityPrize.SubmissionLower.ProjectiveHighLeafAgreementResidualFactor6900
