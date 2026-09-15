import WeightedCutoff2SourcesW1332256900
import WeightedBatchFactorChoice6900
import WeightedCutoff2DeflatedCapacityW1332256900

/-! Per-factor helper certificates from the cutoff-two source. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2BatchHelperW1332256900

open scoped BigOperators
open Order2SourceBasisScaffold Order2SourceSpecializationScaffold
open Order2ValueYCapAllFactorScaffold
open WeightedSourceBoxQuotient6900 WeightedActualProductBandGate6900
open WeightedBatchFactorChoice6900
open WeightedCutoff2SourcesW1332256900
open WeightedCutoff2DeflatedCapacityW1332256900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

variable {K I : Type*} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

def RegularHelper (nodes values : I→K) (F H : MvPolynomial (Fin 4) K) : Prop :=
  Prime F ∧ H≠0 ∧
  H∈globalOrder2CoefficientBox K 2130677530 133225 15993 5248 2624 ∧
  ¬F∣H ∧
  ∀ (P : Polynomial K) (support : Finset I),P.natDegree≤133225→
    180413≤support.card→(∀ i∈support,P.eval (nodes i)=values i)→
    localJetSpecialization2 P F=0→
    localJetSpecialization2 P (MvPolynomial.pderiv (3 : Fin 4) F)≠0→
    localJetSpecialization2 P H=0

def BatchHelperCertificate (Q : MvPolynomial (Fin 4) K) (nodes values : I→K)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∃ (s : Finset (MvPolynomial (Fin 4) K)) (j : Nat)
    (C G : MvPolynomial (Fin 4) K),
    s⊆positiveTFactors Q ∧ F∈s ∧ (∏ A∈s,A)=F*C ∧
    j≤2624 ∧ C≠0 ∧ G≠0 ∧ ¬F∣C ∧ ¬F∣G ∧
    RegularHelper nodes values F (C^j*G)

theorem batchHelperCertificate_regular (Q : MvPolynomial (Fin 4) K)
    (nodes values : I→K) (F : MvPolynomial (Fin 4) K)
    (hcert : BatchHelperCertificate Q nodes values F) :
    ∃ H,RegularHelper nodes values F H := by
  obtain ⟨s,j,C,G,hs,hF,hprod,hj,hC,hG,hFC,hFG,hreg⟩ := hcert
  exact ⟨C^j*G,hreg⟩

theorem heavy_subset_certificate [Fintype I]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s.Nonempty) (hsub : s⊆positiveTFactors Q)
    (nodes values : I→K) (hinj : Function.Injective nodes)
    (hn : Fintype.card I≤262142) (h2 : (2:K)≠0)
    (prime : Nat) [CharP K prime] (hprime : prime.Prime) (hchar : 2624<prime)
    (hheavy : 212≤jetDegree (∏ F∈s,F) ∨
      56≤derivativeDegree (∏ F∈s,F)) :
    ∃ F∈s,BatchHelperCertificate Q nodes values F := by
  classical
  let product : MvPolynomial (Fin 4) K := ∏ F∈s,F
  have hirr : ∀ F∈s,Irreducible F := fun F hF =>
    (positiveTFactors_spec Q F (hsub hF)).1
  have hproduct : product≠0 := product_ne_zero s id hirr
  have hrho : 2≤derivativeDegree product :=
    positiveT_product_derivativeDegree s id hs hirr
      (fun F hF => (positiveTFactors_spec Q F (hsub hF)).2.2)
  obtain ⟨j,G,hj,hG,hnot,hkernel,hquotient,htight,hcontact,horiginal,hmain,hder⟩ :=
    heavy_product_escape K I h2 nodes values hn product hproduct hrho hheavy
  obtain ⟨_,_,F,hFs,C,hFprime,hFG,hprod,hFC,hC⟩ :=
    positiveT_subset_escape Q G s hsub hnot
  have hp : product=F*C := hprod
  have htight' : (F*C)^j*G∈WeightedSourceIndex6900.weightedCoefficientBox K
      (2130677530-j*47190) 133225 5248 := by
    rw [← hp]
    exact htight
  have horiginal' : (F*C)^j*G≠0 := by rw [← hp]; exact horiginal
  have hcontact' : ∀ i:I,contactTruncation K 11810
      (localSubstitution K (nodes i) (values i) ((F*C)^j*G))=0 := by
    intro i
    rw [← hp]
    exact hcontact i
  have hH : C^j*G≠0 := mul_ne_zero (pow_ne_zero j hC) hG
  have hbox := deflated_helper_mem_legacyBox F C G j hFprime.ne_zero
    horiginal' htight'
  have hproper := deflated_helper_proper F C G j hFprime hFC hFG
  have hregular : RegularHelper nodes values F (C^j*G) := by
    refine ⟨hFprime,hH,hbox,hproper,?_⟩
    intro P support hP ha hvalues hFzero hFregular
    exact deflated_helper_vanishes F C G P nodes values support j prime
      hprime hchar hj hinj.injOn h2 hP ha horiginal'
      (fun i _ => hcontact' i) hvalues htight' hFzero hFregular
  exact ⟨F,hFs,s,j,C,G,hsub,hFs,hprod,hj,hC,hG,hFC,hFG,hregular⟩

theorem heavy_subset_regular_helper [Fintype I]
    (Q : MvPolynomial (Fin 4) K) (s : Finset (MvPolynomial (Fin 4) K))
    (hs : s.Nonempty) (hsub : s⊆positiveTFactors Q)
    (nodes values : I→K) (hinj : Function.Injective nodes)
    (hn : Fintype.card I≤262142) (h2 : (2:K)≠0)
    (prime : Nat) [CharP K prime] (hprime : prime.Prime) (hchar : 2624<prime)
    (hheavy : 212≤jetDegree (∏ F∈s,F) ∨
      56≤derivativeDegree (∏ F∈s,F)) :
    ∃ F∈s,∃ H,RegularHelper nodes values F H := by
  obtain ⟨F,hF,hcert⟩ := heavy_subset_certificate Q s hs hsub nodes values
    hinj hn h2 prime hprime hchar hheavy
  exact ⟨F,hF,batchHelperCertificate_regular Q nodes values F hcert⟩

end
end ProximityPrize.SubmissionLower.WeightedCutoff2BatchHelperW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2BatchHelperW1332256900.heavy_subset_certificate
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2BatchHelperW1332256900.heavy_subset_regular_helper
