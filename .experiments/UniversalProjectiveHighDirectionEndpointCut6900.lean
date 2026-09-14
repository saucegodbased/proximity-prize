import UniversalBothRowsHighEndpointCut6900

/-!
# Projectively high received directions at the lower-6900 endpoint

The weighted scalar-list theorem is invariant under changing the affine chart
on the received two-plane.  Fix a nonzero pair `(a,b)` and let `V` interpolate

`a * u0 + b * u1`.

If `a = 0`, rescaling `V` gives the already proved low-direction scalar split.
If `a != 0`, remove the one pole `gamma = b / a` and use

`T_gamma = (a * gamma - b)⁻¹ * (a * P_gamma - V)`.

The `T_gamma` agree with the fixed word `u1`.  Above code degree they are
injective; below code degree every bad seed must be the pole.  Consequently a
bad family admitting any nonzero canonical direction of degree at most
`133119` has size at most the scalar-list cap plus one, still strictly below
the exact MCA budget.

The exceptional seed cannot in general be deleted: at the pole the one known
combination need not separate the two received rows.
-/

namespace ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900

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

def projectiveScalarized {K : Type*} [Field K]
    (a b : K) (V : K[X]) (selected : K → K[X]) (gamma : K) : K[X] :=
  C (a * gamma - b)⁻¹ * (C a * selected gamma - V)

theorem projectiveScalarized_degree133119
    {K : Type*} [Field K]
    (a b : K) (V : K[X]) (selected : K → K[X]) (gamma : K)
    (hV : V.natDegree ≤ 133119)
    (hP : (selected gamma).natDegree ≤ 131071) :
    (projectiveScalarized a b V selected gamma).natDegree ≤ 133119 := by
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_sub_le _ _).trans
      (max_le
        ((natDegree_C_mul_le a (selected gamma)).trans
          (hP.trans (by norm_num)))
        hV))

theorem projectiveScalarized_eval
    {K : Type*} [Field K]
    (a b : K) (V : K[X]) (selected : K → K[X])
    (gamma x u0 u1 : K) (hden : a * gamma - b ≠ 0)
    (hP : (selected gamma).eval x = u0 + gamma * u1)
    (hV : V.eval x = a * u0 + b * u1) :
    (projectiveScalarized a b V selected gamma).eval x = u1 := by
  simp only [projectiveScalarized, eval_mul, eval_C, eval_sub, hP, hV]
  field_simp [hden]
  ring

/-- Away from the unique projective pole, scalarization by a direction whose
interpolant is above code degree is injective. -/
theorem projectiveScalarized_injOn_of_degree_gt
    {K : Type*} [Field K]
    (a b : K) (V : K[X]) (selected : K → K[X]) (Gamma : Finset K)
    (ha : a ≠ 0) (hV : 131071 < V.natDegree)
    (hP : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hpole : ∀ gamma ∈ Gamma, a * gamma - b ≠ 0) :
    Set.InjOn (projectiveScalarized a b V selected) (↑Gamma : Set K) := by
  intro gamma hgamma delta hdelta heq
  have hgammaGamma : gamma ∈ Gamma := hgamma
  have hdeltaGamma : delta ∈ Gamma := hdelta
  have hgammaDen : a * gamma - b ≠ 0 :=
    hpole gamma hgammaGamma
  have hdeltaDen : a * delta - b ≠ 0 :=
    hpole delta hdeltaGamma
  by_contra hne
  have hdeltaGammaNe : delta - gamma ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hne)
  have hcoeff :
      (a * delta - b) - (a * gamma - b) ≠ 0 := by
    rw [show (a * delta - b) - (a * gamma - b) =
      a * (delta - gamma) by ring]
    exact mul_ne_zero ha hdeltaGammaNe
  have hVne : V ≠ 0 := by
    intro hz
    simp [hz] at hV
  have hscaled :
      C (a * delta - b) * (C a * selected gamma - V) =
        C (a * gamma - b) * (C a * selected delta - V) := by
    have hrecover : ∀ z : K, a * z - b ≠ 0 →
        C (a * z - b) * projectiveScalarized a b V selected z =
          C a * selected z - V := by
      intro z hz
      dsimp only [projectiveScalarized]
      rw [← mul_assoc, ← C_mul]
      simp [hz]
    calc
      C (a * delta - b) * (C a * selected gamma - V) =
          C (a * delta - b) *
            (C (a * gamma - b) *
              projectiveScalarized a b V selected gamma) := by
            rw [hrecover gamma hgammaDen]
      _ = C (a * gamma - b) *
            (C (a * delta - b) *
              projectiveScalarized a b V selected gamma) := by ring
      _ = C (a * gamma - b) *
            (C (a * delta - b) *
              projectiveScalarized a b V selected delta) := by rw [heq]
      _ = C (a * gamma - b) * (C a * selected delta - V) := by
            rw [hrecover delta hdeltaDen]
  have hidentity :
      C ((a * delta - b) - (a * gamma - b)) * V =
        C (a * delta - b) * (C a * selected gamma) -
          C (a * gamma - b) * (C a * selected delta) := by
    rw [C_sub]
    linear_combination -hscaled
  have hleft :
      (C ((a * delta - b) - (a * gamma - b)) * V).natDegree =
        V.natDegree := by
    rw [natDegree_mul (C_ne_zero.mpr hcoeff) hVne, natDegree_C,
      Nat.zero_add]
  have hright :
      (C (a * delta - b) * (C a * selected gamma) -
        C (a * gamma - b) * (C a * selected delta)).natDegree ≤
          131071 := by
    exact (natDegree_sub_le _ _).trans
      (max_le
        ((natDegree_C_mul_le (a * delta - b) (C a * selected gamma)).trans
          ((natDegree_C_mul_le a (selected gamma)).trans
            (hP gamma hgammaGamma)))
        ((natDegree_C_mul_le (a * gamma - b) (C a * selected delta)).trans
          ((natDegree_C_mul_le a (selected delta)).trans
            (hP delta hdeltaGamma))))
  rw [hidentity] at hleft
  omega

/-- A code-degree interpolant of one nonzero received direction leaves at
most its projective pole as a bad seed. -/
theorem low_projective_direction_bad_family_card_le_one
    {I K : Type} [Fintype I] [Nonempty I] [Field K] [Fintype K]
    [CharP K 2130706433]
    (nodes : I ↪ K) (u0 u1 : I → K) (a b : K)
    (hab : a ≠ 0 ∨ b ≠ 0) (V : K[X])
    (hVdegree : V.natDegree ≤ 131071)
    (hVeval : ∀ i, V.eval (nodes i) = a * u0 i + b * u1 i)
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
  apply Finset.card_le_one.mpr
  intro gamma hgamma delta hdelta
  have hsingular : ∀ z ∈ seeds, b - z * a = 0 := by
    intro z hz
    by_contra hdet
    have hall := projected_rows_mem_of_two_interpolants
      (domain := nodes) (w := 131071) (U := ![u0, u1]) (A := A z)
      (gamma := z) (c := a) (d := b) (P := selected z) (Q := V)
      hdet (hdegree z hz) hVdegree (hagrees z hz)
      (fun i _ ↦ by simpa using hVeval i)
    obtain ⟨j, hj⟩ := hbad z hz
    exact hj (hall j)
  have hgammaEq := hsingular gamma hgamma
  have hdeltaEq := hsingular delta hdelta
  rcases hab with ha | hb
  · have : a * (gamma - delta) = 0 := by
      linear_combination -hgammaEq + hdeltaEq
    rcases mul_eq_zero.mp this with ha0 | hgd
    · exact (ha ha0).elim
    · exact sub_eq_zero.mp hgd
  · by_cases ha : a = 0
    · subst a
      simp only [mul_zero, sub_zero] at hgammaEq
      exact (hb hgammaEq).elim
    · have : a * (gamma - delta) = 0 := by
        linear_combination -hgammaEq + hdeltaEq
      rcases mul_eq_zero.mp this with ha0 | hgd
      · exact (ha ha0).elim
      · exact sub_eq_zero.mp hgd

/-- Any nonzero canonical direction of degree at most `133119` closes the
exact bad family.  The numerical cost is

`242068243281965801 + 1 < 254684620614660120`.
-/
theorem low_projective_direction_degree133119_bad_family_lt_mca
    {I K : Type} [Fintype I] [Nonempty I] [Field K] [Fintype K]
    [CharP K 2130706433]
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (u0 u1 : I → K) (a b : K) (hab : a ≠ 0 ∨ b ≠ 0)
    (V : K[X])
    (hVdegree : V.natDegree ≤ 133119)
    (hVeval : ∀ i, V.eval (nodes i) = a * u0 i + b * u1 i)
    (seeds : Finset K) (A : K → Finset I)
    (selected : K → K[X])
    (hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ 131071)
    (hcard : ∀ gamma ∈ seeds, 180413 ≤ (A gamma).card)
    (hagrees : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    (hbad : ∀ gamma ∈ seeds, ∃ j : Fin 2,
      LinearCode.projectedWord (![u0, u1] j) (A gamma) ∉
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code nodes 131072) (A gamma)) :
    seeds.card < 254684620614660120 := by
  classical
  by_cases hcode : V.natDegree ≤ 131071
  · have hone := low_projective_direction_bad_family_card_le_one
      nodes u0 u1 a b hab V hcode hVeval seeds A selected hdegree
        hagrees hbad
    omega
  · have hVlarge : 131071 < V.natDegree := Nat.lt_of_not_ge hcode
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        rcases hab with ha' | hb
        · exact (ha' ha).elim
        · exact hb
      let V1 : K[X] := C b⁻¹ * V
      have hV1degree : V1.natDegree ≤ 133119 := by
        exact (natDegree_C_mul_le b⁻¹ V).trans hVdegree
      have hV1eval : ∀ i, V1.eval (nodes i) = u1 i := by
        intro i
        dsimp only [V1]
        rw [eval_mul, eval_C, hVeval]
        simp only [ha, zero_mul, zero_add]
        field_simp [hb]
      exact low_received_direction_bad_family_lt_mca (nodes := nodes) hI u0 u1 V1
        hV1degree hV1eval seeds A selected hdegree hcard hagrees hbad
    · let pole : K := b * a⁻¹
      let regularSeeds := seeds.erase pole
      have hregularSub : regularSeeds ⊆ seeds := Finset.erase_subset pole seeds
      have hregular : ∀ gamma ∈ regularSeeds, a * gamma - b ≠ 0 := by
        intro gamma hgamma hzero
        have hgammaPole : gamma = pole := by
          dsimp only [pole]
          apply (mul_left_cancel₀ ha)
          field_simp [ha]
          linear_combination hzero
        subst gamma
        exact (Finset.mem_erase.mp hgamma).1 rfl
      have hinj : Set.InjOn (projectiveScalarized a b V selected)
          (↑regularSeeds : Set K) :=
        projectiveScalarized_injOn_of_degree_gt a b V selected
          regularSeeds ha hVlarge
          (fun gamma hgamma ↦ hdegree gamma (hregularSub hgamma)) hregular
      have hcount :=
        WeightedScalarList133119.scalarized_seed_family_card_le
          nodes u1 nodes.injective hI regularSeeds
          (projectiveScalarized a b V selected) hinj
          (fun gamma hgamma ↦
            projectiveScalarized_degree133119 a b V selected gamma hVdegree
              (hdegree gamma (hregularSub hgamma)))
          (fun gamma hgamma ↦ by
            have hgammaSeed : gamma ∈ seeds := hregularSub hgamma
            apply (hcard gamma hgammaSeed).trans
            apply Finset.card_le_card
            intro i hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              projectiveScalarized_eval a b V selected gamma (nodes i)
                (u0 i) (u1 i) (hregular gamma hgamma)
                (hagrees gamma hgammaSeed i hi) (hVeval i)⟩)
      have hseedCard : seeds.card ≤ regularSeeds.card + 1 := by
        by_cases hpole : pole ∈ seeds
        · have heq := Finset.card_erase_add_one hpole
          change (seeds.erase pole).card + 1 = seeds.card at heq
          simpa [regularSeeds] using heq.symm.le
        · simp [regularSeeds, hpole]
      omega

/-- The exact invariant left after all unconditional projective scalar cuts:
every nonzero direction in the canonical received two-plane has degree at
least `133120`. -/
def CanonicalHighTailDirectionIndependent
    {I K : Type} [Fintype I] [Field K]
    (nodes : I ↪ K) (U : Fin 2 → I → K) : Prop :=
  ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) →
    133120 ≤
      (receivedDirectionInterpolant nodes
        (fun i ↦ a * U 0 i + b * U 1 i)).natDegree

/-- The genuinely open universal theorem after the projective degree cut. -/
def UniversalProjectiveHighDirectionBadFamilyBound
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
    CanonicalHighTailDirectionIndependent nodes U →
    seeds.card ≤ 254684620614660120

/-- The projective scalar cut reduces the selected bad-family target to the
single high-tail-independent endpoint above. -/
theorem selectedBadGivenSetsBound_of_projectiveHighDirection
    {I K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2130706433]
    (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (hhigh : UniversalProjectiveHighDirectionBadFamilyBound nodes) :
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
  by_cases hdirections : CanonicalHighTailDirectionIndependent nodes U
  · exact hhigh U seeds A selected hdegree hcard' hagreement hbad
      hdirections
  · simp only [CanonicalHighTailDirectionIndependent, not_forall] at hdirections
    obtain ⟨a, b, hab, hlow⟩ := hdirections
    let V := receivedDirectionInterpolant nodes
      (fun i ↦ a * U 0 i + b * U 1 i)
    have hVdegree : V.natDegree ≤ 133119 := by
      dsimp only [V] at hlow ⊢
      omega
    exact Nat.le_of_lt
      (low_projective_direction_degree133119_bad_family_lt_mca
        nodes hI (U 0) (U 1) a b hab V hVdegree
        (fun i ↦ receivedDirectionInterpolant_eval nodes
          (fun x ↦ a * U 0 x + b * U 1 x) i)
        seeds A selected hdegree hcard' hagreement hbad')

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : CharP IRSProfile.Field 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

abbrev UniversalProjectiveHighDirectionBadFamilyBound6900 : Prop :=
  UniversalProjectiveHighDirectionBadFamilyBound IRSProfile.domain

theorem protocolClaim6900_of_projectiveHighDirection
    (hhigh : UniversalProjectiveHighDirectionBadFamilyBound6900) :
    ProtocolClaim 6900 Order2Protocol6900.radiusNumerator
      Order2Protocol6900.radiusDenominator :=
  protocolClaim6900_of_bad_family
    (by
      have hI : Fintype.card IRSProfile.Index = 262144 := by
        norm_num [IRSProfile.Index]
      have h := selectedBadGivenSetsBound_of_projectiveHighDirection
        IRSProfile.domain hI hhigh
      simpa [TargetBadFamilyBound6900, Order2Protocol6900.errors,
        Order2Protocol6900.mcaBudget] using h)

end
end ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900

#print axioms ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900.projectiveScalarized_injOn_of_degree_gt
#print axioms ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900.low_projective_direction_degree133119_bad_family_lt_mca
#print axioms ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900.selectedBadGivenSetsBound_of_projectiveHighDirection
#print axioms ProximityPrize.SubmissionLower.UniversalProjectiveHighDirectionEndpointCut6900.protocolClaim6900_of_projectiveHighDirection
