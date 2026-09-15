import WeightedSourceBoxQuotient6900
import Order2DeflatedHelperSpecialization6900

/-! Deflated helper capacity at the cutoff-two W=133225 profile. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2DeflatedCapacityW1332256900

open Order2SourceBasisScaffold Order2SourceSpecializationScaffold
open WeightedSourceIndex6900 WeightedSourceSpace6900 WeightedSourceBoxQuotient6900
open Order2DerivativeContactCapacity6900 Order2DeflatedHelperSpecialization6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

abbrev Poly4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K
variable {K : Type*} [Field K]

theorem weightedBox_le_legacyBox (B W D : Nat) (hW : 3≤W) :
    weightedCoefficientBox K B W D≤
      globalOrder2CoefficientBox K B W (B/(W-2)) D (D/2) := by
  intro Q hQ
  have heq := reconstruct_all K B W D (show 0<W by omega) Q hQ
  rw [← heq]
  exact reconstruct_mem_legacyBox K B W D hW _

theorem helper_capacity (j a : Nat) (hj : j≤2624) (ha : 180413≤a) :
    2130677530-j*47190≤(11810-j)*a+j*(133225-2) := by
  have hbase :
      2130677530-j*47190=(11810-j)*180413+j*(133225-2) := by omega
  rw [hbase]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (11810-j) ha) _

theorem deflated_helper_vanishes
    {I : Type*} [DecidableEq K] [DecidableEq I]
    (F C G : Poly4 K) (P : Polynomial K) (nodes received : I→K)
    (support : Finset I) (j prime : Nat) [CharP K prime]
    (hprime : prime.Prime) (hchar : 2624<prime) (hj : j≤2624)
    (hinj : Set.InjOn nodes support) (h2 : (2:K)≠0)
    (hP : P.natDegree≤133225) (ha : 180413≤support.card)
    (hQ : (F*C)^j*G≠0)
    (hcontact : ∀ i∈support,contactTruncation K 11810
      (localSubstitution K (nodes i) (received i) ((F*C)^j*G))=0)
    (hvalues : ∀ i∈support,P.eval (nodes i)=received i)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (2130677530-j*47190) 133225 5248)
    (hFzero : localJetSpecialization2 P F=0)
    (hregular : localJetSpecialization2 P
      (MvPolynomial.pderiv (3 : Fin 4) F)≠0) :
    localJetSpecialization2 P (C^j*G)=0 := by
  have hd := ((mem_weightedBox_iff (2130677530-j*47190) 133225 5248
    ((F*C)^j*G)).mp htight).resolve_left hQ
  have hw : MvPolynomial.weightedTotalDegree (sourceWeights 133225)
      ((F*C)^j*G)<2130677530-j*47190 := hd.1
  exact deflated_helper_specialization_eq_zero_of_capacity
    ((F*C)^j*G) F C G P nodes received support 11810 j
    (2130677530-j*47190) 133225 prime hprime (by omega)
    hinj h2 hP hcontact hvalues hw (helper_capacity j support.card hj ha)
    rfl hFzero hregular

theorem deflated_helper_mem_box (F C G : Poly4 K) (j : Nat)
    (hF : F≠0) (hQ : (F*C)^j*G≠0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (2130677530-j*47190) 133225 5248) :
    C^j*G∈weightedCoefficientBox K 2130677530 133225 5248 := by
  have heq : (F*C)^j*G=F^j*(C^j*G) := by rw [mul_pow,mul_assoc]
  have hH : C^j*G≠0 := by
    intro hz
    apply hQ
    rw [heq,hz,mul_zero]
  have hbig : F^j*(C^j*G)∈weightedCoefficientBox K
      2130677530 133225 5248 := by
    rw [← heq]
    intro e he
    have hd := htight he
    exact ⟨hd.1,hd.2.trans_le (Nat.sub_le _ _)⟩
  have hquot := (quotient_mem_weightedBox 2130677530 133225 5248
    (F^j) (C^j*G) (pow_ne_zero j hF) hH hbig).2.2
  intro e he
  have hd := hquot he
  exact ⟨hd.1.trans (Nat.sub_le _ _),hd.2.trans_le (Nat.sub_le _ _)⟩

theorem deflated_helper_mem_legacyBox (F C G : Poly4 K) (j : Nat)
    (hF : F≠0) (hQ : (F*C)^j*G≠0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (2130677530-j*47190) 133225 5248) :
    C^j*G∈globalOrder2CoefficientBox K
      2130677530 133225 15993 5248 2624 := by
  have h := weightedBox_le_legacyBox 2130677530 133225 5248 (by norm_num)
    (deflated_helper_mem_box F C G j hF hQ htight)
  exact h

theorem deflated_helper_proper (F C G : Poly4 K) (j : Nat)
    (hF : Prime F) (hFC : ¬F∣C) (hFG : ¬F∣G) : ¬F∣C^j*G := by
  intro hd
  rcases hF.dvd_mul.mp hd with hc | hg
  · exact hFC (hF.dvd_of_dvd_pow hc)
  · exact hFG hg

end
end ProximityPrize.SubmissionLower.WeightedCutoff2DeflatedCapacityW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2DeflatedCapacityW1332256900.helper_capacity
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2DeflatedCapacityW1332256900.deflated_helper_vanishes
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2DeflatedCapacityW1332256900.deflated_helper_mem_legacyBox
