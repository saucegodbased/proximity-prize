import WeightedActualProductBandGate6900
import Order2HereditaryActiveSurface6900

/-! Cumulative exact-flag budgets for original factors. No independent
per-factor rectangle is charged: all three sums come from one product. -/
namespace ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900
open scoped BigOperators
open RCN071 RCN081 RCN084 RCN095 RCN135
open Order2ValueYCapAllFactorScaffold Order2ValueYCapFlagSupport
open Order2FlagTwoCutAdapter WeightedSourceBoxQuotient6900
open WeightedActualProductBandGate6900
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
variable {K : Type} [Field K]
local instance {T : Type*} : DecidableEq T := Classical.decEq T

theorem exactFlag_cumulative_of_product_dvd
    (s : Finset (MvPolynomial (Fin 4) K)) (Q : MvPolynomial (Fin 4) K)
    (hQ : Q≠0) (hprod : (∏ F∈s,F)∣Q) :
    (∑ F : ↥s, (exactFlag (rtySource F.1)).all)≤
      MvPolynomial.weightedTotalDegree ![0,0,0,1] Q ∧
    (∑ F : ↥s, ((exactFlag (rtySource F.1)).yz+(exactFlag (rtySource F.1)).all))≤
      MvPolynomial.weightedTotalDegree ![0,0,1,1] Q ∧
    (∑ F : ↥s, ((exactFlag (rtySource F.1)).zOnly+
      (exactFlag (rtySource F.1)).yz+(exactFlag (rtySource F.1)).all))≤
      MvPolynomial.weightedTotalDegree ![0,1,1,1] Q := by
  have hw (weights : Fin 4 → Nat) :
      (∑ F : ↥s, MvPolynomial.weightedTotalDegree weights F.1)≤
        MvPolynomial.weightedTotalDegree weights Q := by
    simpa only [Finset.sum_coe_sort,id_eq] using
      sum_weightedTotalDegree_le_of_prod_dvd weights s id Q hQ hprod
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ ∑ F : ↥s, MvPolynomial.weightedTotalDegree ![0,0,0,1] F.1 := by
        apply Finset.sum_le_sum
        intro F _
        rw [(exactFlag_cumulative (rtySource F.1)).1]
        exact (rtySurfaceMap_nested_weights_le (polynomialEmbedding K) F.1).1
      _ ≤ _ := hw ![0,0,0,1]
  · calc
      _ ≤ ∑ F : ↥s, MvPolynomial.weightedTotalDegree ![0,0,1,1] F.1 := by
        apply Finset.sum_le_sum
        intro F _
        rw [(exactFlag_cumulative (rtySource F.1)).2.1]
        exact (rtySurfaceMap_nested_weights_le (polynomialEmbedding K) F.1).2.1
      _ ≤ _ := hw ![0,0,1,1]
  · calc
      _ ≤ ∑ F : ↥s, MvPolynomial.weightedTotalDegree ![0,1,1,1] F.1 := by
        apply Finset.sum_le_sum
        intro F _
        rw [(exactFlag_cumulative (rtySource F.1)).2.2]
        exact (rtySurfaceMap_nested_weights_le (polynomialEmbedding K) F.1).2.2
      _ ≤ _ := hw ![0,1,1,1]

theorem exactFlag_cumulative_of_weight_bounds
    (s : Finset (MvPolynomial (Fin 4) K)) (Q : MvPolynomial (Fin 4) K)
    (hQ : Q≠0) (hprod : (∏ F∈s,F)∣Q) (p : FlagDegree)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] Q≤p.all)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] Q≤p.yz+p.all)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] Q≤p.zOnly+p.yz+p.all) :
    (∑ F : ↥s, (exactFlag (rtySource F.1)).all)≤p.all ∧
    (∑ F : ↥s, ((exactFlag (rtySource F.1)).yz+(exactFlag (rtySource F.1)).all))≤p.yz+p.all ∧
    (∑ F : ↥s, ((exactFlag (rtySource F.1)).zOnly+
      (exactFlag (rtySource F.1)).yz+(exactFlag (rtySource F.1)).all))≤p.zOnly+p.yz+p.all := by
  have h := exactFlag_cumulative_of_product_dvd s Q hQ hprod
  exact ⟨h.1.trans hT,h.2.1.trans hRT,h.2.2.trans hJ⟩

theorem positiveT_subset_product_dvd (s : Finset (MvPolynomial (Fin 4) K))
    (Q : MvPolynomial (Fin 4) K) (hQ : Q≠0) (hs : s⊆positiveTFactors Q) :
    (∏ F∈s,F)∣Q :=
  (Finset.prod_dvd_prod_of_subset s (positiveTFactors Q) id hs).trans
    (positiveTFactors_product_dvd Q hQ)

theorem rtySource_in_flag_of_weights (F : MvPolynomial (Fin 4) K) (p : FlagDegree)
    (hT : MvPolynomial.weightedTotalDegree ![0,0,0,1] F≤p.all)
    (hRT : MvPolynomial.weightedTotalDegree ![0,0,1,1] F≤p.yz+p.all)
    (hJ : MvPolynomial.weightedTotalDegree ![0,1,1,1] F≤p.zOnly+p.yz+p.all) :
    PolynomialInFlag p (rtySource F) := by
  have h := rtySurfaceMap_nested_weights_le (polynomialEmbedding K) F
  apply (support_subset_flagSupport_iff p (rtySource F)).mp
  exact support_subset_flagSupport_of_weighted_degrees p (rtySource F)
    (h.1.trans hT) (h.2.1.trans hRT) (h.2.2.trans hJ)

theorem derivative_nested_bounds (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤derivativeDegree P/2 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤derivativeDegree P := by
  constructor
  · apply (weightedTotalDegree_le_iff _ P _).mpr
    intro e he
    have hd := MvPolynomial.le_weightedTotalDegree derivativeWeights he
    rw [derivativeWeight_eq] at hd
    change e 2+2*e 3≤derivativeDegree P at hd
    rw [RCN081.weight_fin4]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    omega
  · apply (weightedTotalDegree_le_iff _ P _).mpr
    intro e he
    have hd := MvPolynomial.le_weightedTotalDegree derivativeWeights he
    rw [derivativeWeight_eq] at hd
    change e 2+2*e 3≤derivativeDegree P at hd
    rw [RCN081.weight_fin4]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    omega

theorem T_weight_eq_degreeOf (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] P=P.degreeOf 3 := by
  have hw : (![0,0,0,1] : Fin 4 → Nat)=Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  rw [hw,MvPolynomial.weightedTotalDegree_piSingle]

theorem cheap_product_weight_bounds (P : MvPolynomial (Fin 4) K)
    (hJ : jetDegree P≤207) (hrho : derivativeDegree P≤54) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤27 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤54 ∧
    MvPolynomial.weightedTotalDegree ![0,1,1,1] P≤207 := by
  have h := derivative_nested_bounds P
  exact ⟨h.1.trans (by omega),h.2.trans hrho,hJ⟩

end
end ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900.exactFlag_cumulative_of_product_dvd
#print axioms ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900.exactFlag_cumulative_of_weight_bounds
#print axioms ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900.positiveT_subset_product_dvd
#print axioms ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900.rtySource_in_flag_of_weights
#print axioms ProximityPrize.SubmissionLower.WeightedFactorFlagBudgetW1332216900.cheap_product_weight_bounds
