import Order2SeedlessCleanupAggregate6900
import WeightedRepresentativeCountLedgerW1332216900

/-! Nonactive cleanup for the actual primary 721/236/118 source.
The whole T-free solution family includes its regular, singular and Y-only
branches, so no separate copy of the old concrete wrappers is needed. -/
namespace ProximityPrize.SubmissionLower.Order2WeightedNonactiveCleanupW1332216900
open scoped BigOperators
open RCN081 RCN135 RCN290 RCN293
open Order2ValueYCapAllFactorScaffold Order2SeedlessCleanupAggregate6900
open WeightedRepresentativeCountLedgerW1332216900
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
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P J=0)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card)
    (hcap : firstOrderRegularNumerator yCap R≤cap*(a-w)) :
    Gamma.card≤cap+firstOrderSingularCap yCap R := by
  apply all_card_le J hJ w a prime yCap R cap
    (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,a])
    hYchar hRchar hRp hY hR hT Gamma nodes x u hinj
    (by rw [hn]; norm_num [a,n]) hdegree hsolution hagreement
  simpa only [hn,firstOrderRegularNumerator,firstOrderMixedCost] using hcap

def tFreeSolutions (Q : MvPolynomial (Fin 4) K) (Gamma : Finset (Polynomial K)) :=
  Gamma.filter fun P => jetSpecialization2 P (tFreeProduct Q)=0

theorem actual_nonactive_bound {I : Type} [Fintype I] [CharP K prime]
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0)
    (hY : Q.degreeOf 1≤721) (hR : Q.degreeOf 2≤236) (hT : Q.degreeOf 3≤118)
    (Gamma : Finset (Polynomial K)) (nodes : Finset I) (x u : I → K)
    (hinj : Set.InjOn x nodes) (hn : nodes.card=n)
    (hdegree : ∀ P∈Gamma,P.natDegree≤w)
    (hsolution : ∀ P∈Gamma,jetSpecialization2 P Q=0)
    (hagreement : ∀ P∈Gamma,a≤(nodes.filter fun i => P.eval (x i)=u i).card) :
    Gamma.card≤(activeTRegularPolynomials Q Gamma).card+13679939831507851 := by
  classical
  let S := positiveTSingularAuxiliary Q
  have hSne : S≠0 := positiveTSingularAuxiliary_nonzero Q hQ prime
    (hT.trans_lt cleanup_characteristic_gates.1)
  have hST : S.degreeOf (3 : Fin 4)=0 := positiveTSingularAuxiliary_T_degree Q
  have hSY : S.degreeOf (1 : Fin 4)≤positiveTAuxY := by
    have h := positiveTSingularAuxiliary_weight_le Q hQ
      (Pi.single (1 : Fin 4) 1) 118 (by norm_num) hT
    simpa only [MvPolynomial.weightedTotalDegree_piSingle,positiveTAuxY] using
      h.trans (Nat.mul_le_mul_left (2*118-1) (by
        simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hY))
  have hSR : S.degreeOf (2 : Fin 4)≤positiveTAuxR := by
    have h := positiveTSingularAuxiliary_weight_le Q hQ
      (Pi.single (2 : Fin 4) 1) 118 (by norm_num) hT
    simpa only [MvPolynomial.weightedTotalDegree_piSingle,positiveTAuxR] using
      h.trans (Nat.mul_le_mul_left (2*118-1) (by
        simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hR))
  have hpositive : (positiveTSingularPolynomials Q Gamma).card≤positiveTSingularCap := by
    apply seedless_row_card_le S hSne positiveTAuxY positiveTAuxR
      (firstOrderRegularCap positiveTAuxY positiveTAuxR)
      cleanup_characteristic_gates.2.2.2.1 cleanup_characteristic_gates.2.2.2.2
      (by norm_num [positiveTAuxR]) hSY hSR hST
      (positiveTSingularPolynomials Q Gamma) nodes x u hinj hn
      (fun P hP => hdegree P (Finset.mem_filter.mp hP).1)
      (fun P hP => (Finset.mem_filter.mp hP).2)
      (fun P hP => hagreement P (Finset.mem_filter.mp hP).1)
      cleanup_scaled_caps.1
  have hJY : (tFreeProduct Q).degreeOf (1 : Fin 4)≤721 :=
    (RCN081.degreeOf_le_of_dvd 1 (tFreeProduct Q) Q (tFreeProduct_dvd Q hQ) hQ).trans hY
  have hJR : (tFreeProduct Q).degreeOf (2 : Fin 4)≤236 :=
    (RCN081.degreeOf_le_of_dvd 2 (tFreeProduct Q) Q (tFreeProduct_dvd Q hQ) hQ).trans hR
  have htfree : (tFreeSolutions Q Gamma).card≤tFreeRegularCap+tFreeSingularCap := by
    apply seedless_row_card_le (tFreeProduct Q) (tFreeProduct_nonzero Q)
      721 236 tFreeRegularCap cleanup_characteristic_gates.2.2.1
      cleanup_characteristic_gates.2.1 (by norm_num) hJY hJR (tFreeProduct_T_degree Q)
      (tFreeSolutions Q Gamma) nodes x u hinj hn
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
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP,hsing⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hP,hfree⟩))
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le (activeTRegularPolynomials Q Gamma)
    (positiveTSingularPolynomials Q Gamma ∪ tFreeSolutions Q Gamma)
  have h2 := Finset.card_union_le (positiveTSingularPolynomials Q Gamma) (tFreeSolutions Q Gamma)
  have hnumbers : positiveTSingularCap+tFreeRegularCap+tFreeSingularCap≤13679939831507851 := by
    rw [cleanup_caps_exact.2.2.2.2.1,cleanup_caps_exact.2.2.2.2.2.1,
      cleanup_caps_exact.2.2.2.2.2.2.1]
  omega

#print axioms seedless_row_card_le
#print axioms actual_nonactive_bound
end
end ProximityPrize.SubmissionLower.Order2WeightedNonactiveCleanupW1332216900
