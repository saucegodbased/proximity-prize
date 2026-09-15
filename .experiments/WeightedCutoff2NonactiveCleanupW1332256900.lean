import Order2SeedlessCleanupAggregate6900
import WeightedCutoff2RepresentativeLedgerW1332256900

/-! Nonactive cleanup for the cutoff-two primary `739/244/122` source. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2NonactiveCleanupW1332256900

open scoped BigOperators
open RCN081 RCN135 RCN290 RCN293
open Order2ValueYCapAllFactorScaffold Order2SeedlessCleanupAggregate6900
open WeightedCutoff2RepresentativeLedgerW1332256900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
variable {K : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem seedless_row_card_le {I : Type} [Fintype I] [CharP K prime]
    (J : MvPolynomial (Fin 4) K) (hJ : J≠0) (yCap R cap : Nat)
    (hYchar : yCap<prime) (hRchar : R<prime) (hRp : 1≤R)
    (hY : J.degreeOf 1≤yCap) (hR : J.degreeOf 2≤R) (hT : J.degreeOf 3=0)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card≤n) (hAn : a≤nodes.card)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P J=0)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcap : firstOrderRegularNumerator yCap R≤cap*(a-w)) :
    Gamma.card≤cap+firstOrderSingularCap yCap R := by
  apply all_card_le J hJ w a prime yCap R cap
    (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,a])
    hYchar hRchar hRp hY hR hT Gamma nodes x u hinj hAn hdegree hsolution hagreement
  have hnW : nodes.card-w≤n-w := Nat.sub_le_sub_right hn w
  calc
    (nodes.card-w)*((1+2*w*yCap)*R+w*(2*R-1)*yCap)
        ≤ (n-w)*((1+2*w*yCap)*R+w*(2*R-1)*yCap) := Nat.mul_le_mul_right _ hnW
    _ ≤ cap*(a-w) := by simpa [firstOrderRegularNumerator,firstOrderMixedCost] using hcap

def tFreeSolutions (Q : MvPolynomial (Fin 4) K) (Gamma : Finset (Polynomial K)) :=
  Gamma.filter fun P => jetSpecialization2 P (tFreeProduct Q)=0

theorem actual_nonactive_bound {I : Type} [Fintype I] [CharP K prime]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hY : Q.degreeOf 1≤739) (hR : Q.degreeOf 2≤244) (hT : Q.degreeOf 3≤122)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card≤n) (hAn : a≤nodes.card)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    Gamma.card≤(activeTRegularPolynomials Q Gamma).card+15501626357806302 := by
  classical
  let S := positiveTSingularAuxiliary Q
  have hSne : S≠0 := positiveTSingularAuxiliary_nonzero Q hQ prime
    (hT.trans_lt cleanup_characteristic_gates.1)
  have hST : S.degreeOf (3 : Fin 4)=0 := positiveTSingularAuxiliary_T_degree Q
  have hSY : S.degreeOf (1 : Fin 4)≤positiveTAuxY := by
    have h := positiveTSingularAuxiliary_weight_le Q hQ
      (Pi.single (1 : Fin 4) 1) 122 (by norm_num) hT
    simpa only [MvPolynomial.weightedTotalDegree_piSingle,positiveTAuxY] using
      h.trans (Nat.mul_le_mul_left (2*122-1) (by
        simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hY))
  have hSR : S.degreeOf (2 : Fin 4)≤positiveTAuxR := by
    have h := positiveTSingularAuxiliary_weight_le Q hQ
      (Pi.single (2 : Fin 4) 1) 122 (by norm_num) hT
    simpa only [MvPolynomial.weightedTotalDegree_piSingle,positiveTAuxR] using
      h.trans (Nat.mul_le_mul_left (2*122-1) (by
        simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hR))
  have hpositive : (positiveTSingularPolynomials Q Gamma).card≤positiveTSingularCap := by
    apply seedless_row_card_le S hSne positiveTAuxY positiveTAuxR
      (firstOrderRegularCap positiveTAuxY positiveTAuxR)
      cleanup_characteristic_gates.2.2.2.1 cleanup_characteristic_gates.2.2.2.2
      (by norm_num [positiveTAuxR]) hSY hSR hST
      (positiveTSingularPolynomials Q Gamma) nodes x u hinj hn hAn
      (fun P hP => hdegree P (Finset.mem_filter.mp hP).1)
      (fun P hP => (Finset.mem_filter.mp hP).2)
      (fun P hP => hagreement P (Finset.mem_filter.mp hP).1)
      cleanup_scaled_caps.1
  have hJY : (tFreeProduct Q).degreeOf (1 : Fin 4)≤739 :=
    (RCN081.degreeOf_le_of_dvd 1 (tFreeProduct Q) Q (tFreeProduct_dvd Q hQ) hQ).trans hY
  have hJR : (tFreeProduct Q).degreeOf (2 : Fin 4)≤244 :=
    (RCN081.degreeOf_le_of_dvd 2 (tFreeProduct Q) Q (tFreeProduct_dvd Q hQ) hQ).trans hR
  have htfree : (tFreeSolutions Q Gamma).card≤tFreeRegularCap+tFreeSingularCap := by
    apply seedless_row_card_le (tFreeProduct Q) (tFreeProduct_nonzero Q)
      739 244 tFreeRegularCap cleanup_characteristic_gates.2.2.1
      cleanup_characteristic_gates.2.1 (by norm_num) hJY hJR (tFreeProduct_T_degree Q)
      (tFreeSolutions Q Gamma) nodes x u hinj hn hAn
      (fun P hP => hdegree P (Finset.mem_filter.mp hP).1)
      (fun P hP => (Finset.mem_filter.mp hP).2)
      (fun P hP => hagreement P (Finset.mem_filter.mp hP).1)
      cleanup_scaled_caps.2
  have hcover : Gamma⊆activeTRegularPolynomials Q Gamma ∪
      (positiveTSingularPolynomials Q Gamma ∪ tFreeSolutions Q Gamma) := by
    intro P hP
    obtain hreg | hsing | hfree :=
      jet_zero_regular_or_positiveT_singular_or_tFree Q hQ P (hsolution P hP)
    · obtain ⟨F,hF,_,_,_,hz,hr⟩ := hreg
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP,F,hF,hz,hr⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP,hsing⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP,hfree⟩))
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le (activeTRegularPolynomials Q Gamma)
    (positiveTSingularPolynomials Q Gamma ∪ tFreeSolutions Q Gamma)
  have h2 := Finset.card_union_le (positiveTSingularPolynomials Q Gamma) (tFreeSolutions Q Gamma)
  have hnumbers : positiveTSingularCap+tFreeRegularCap+tFreeSingularCap≤15501626357806302 := by
    rw [cleanup_caps_exact.2.2.2.2.1,cleanup_caps_exact.2.2.2.2.2.1,
      cleanup_caps_exact.2.2.2.2.2.2.1]
  omega

end
end ProximityPrize.SubmissionLower.WeightedCutoff2NonactiveCleanupW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2NonactiveCleanupW1332256900.actual_nonactive_bound
