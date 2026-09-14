import WeightedSourceBoxQuotient6900
import Order2DeflatedHelperSpecialization6900

/-! Actual helper capacity and collision-safe enclosing box at the certified
parameters. The complementary factor is never cancelled at solutions. -/
namespace ProximityPrize.SubmissionLower.WeightedHelperDeflatedCapacityW1332216900
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
    weightedCoefficientBox K B W D ≤
      globalOrder2CoefficientBox K B W (B/(W-2)) D (D/2) := by
  intro Q hQ
  have heq := reconstruct_all K B W D (show 0<W by omega) Q hQ
  rw [← heq]
  exact reconstruct_mem_legacyBox K B W D hW _

theorem helper_capacity (j a : Nat) (hj : j≤2504) (ha : 180413≤a) :
    2032893684-j*47194≤(11268-j)*a+j*(133221-2) := by
  have hbase : 2032893684-j*47194=(11268-j)*180413+j*(133221-2) := by omega
  rw [hbase]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (11268-j) ha) _

theorem deflated_helper_vanishes
    {I : Type*} [DecidableEq K] [DecidableEq I]
    (F C G : Poly4 K) (P : Polynomial K) (nodes received : I → K)
    (support : Finset I) (j prime : Nat) [CharP K prime]
    (hprime : prime.Prime) (hchar : 2504<prime) (hj : j≤2504)
    (hinj : Set.InjOn nodes support) (h2 : (2 : K)≠0)
    (hP : P.natDegree≤133221) (ha : 180413≤support.card)
    (hQ : (F*C)^j*G≠0)
    (hcontact : ∀ i∈support, contactTruncation K 11268
      (localSubstitution K (nodes i) (received i) ((F*C)^j*G))=0)
    (hvalues : ∀ i∈support, P.eval (nodes i)=received i)
    (htight : (F*C)^j*G∈weightedCoefficientBox K (2032893684-j*47194) 133221 5008)
    (hFzero : localJetSpecialization2 P F=0)
    (hregular : localJetSpecialization2 P
      (MvPolynomial.pderiv (3 : Fin 4) F)≠0) :
    localJetSpecialization2 P (C^j*G)=0 := by
  have hd := ((mem_weightedBox_iff (2032893684-j*47194) 133221 5008
    ((F*C)^j*G)).mp htight).resolve_left hQ
  have hw : MvPolynomial.weightedTotalDegree (sourceWeights 133221)
      ((F*C)^j*G)<2032893684-j*47194 := hd.1
  exact deflated_helper_specialization_eq_zero_of_capacity
    ((F*C)^j*G) F C G P nodes received support 11268 j
    (2032893684-j*47194) 133221 prime hprime (by omega)
    hinj h2 hP hcontact hvalues hw (helper_capacity j support.card hj ha)
    rfl hFzero hregular

/-- The literal C^j*G helper retains the certified helper source box.
No nonvanishing assumption on C at a solution appears. -/
theorem deflated_helper_mem_box (F C G : Poly4 K) (j : Nat)
    (hF : F≠0) (hQ : (F*C)^j*G≠0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K (2032893684-j*47194) 133221 5008) :
    C^j*G∈weightedCoefficientBox K 2032893684 133221 5008 := by
  have heq : (F*C)^j*G=F^j*(C^j*G) := by rw [mul_pow,mul_assoc]
  have hH : C^j*G≠0 := by
    intro hz
    apply hQ
    rw [heq,hz,mul_zero]
  have hbig : F^j*(C^j*G)∈weightedCoefficientBox K 2032893684 133221 5008 := by
    rw [← heq]
    intro e he
    have hd := htight he
    exact ⟨hd.1,hd.2.trans_le (Nat.sub_le _ _)⟩
  have hquot := (quotient_mem_weightedBox 2032893684 133221 5008
    (F^j) (C^j*G) (pow_ne_zero j hF) hH hbig).2.2
  intro e he
  have hd := hquot he
  exact ⟨hd.1.trans (Nat.sub_le _ _),hd.2.trans_le (Nat.sub_le _ _)⟩

theorem deflated_helper_mem_legacyBox (F C G : Poly4 K) (j : Nat)
    (hF : F≠0) (hQ : (F*C)^j*G≠0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K (2032893684-j*47194) 133221 5008) :
    C^j*G∈globalOrder2CoefficientBox K 2032893684 133221 15259 5008 2504 := by
  have h := weightedBox_le_legacyBox 2032893684 133221 5008 (by norm_num)
    (deflated_helper_mem_box F C G j hF hQ htight)
  exact h

theorem deflated_helper_proper (F C G : Poly4 K) (j : Nat)
    (hF : Prime F) (hFC : ¬F∣C) (hFG : ¬F∣G) : ¬F∣C^j*G := by
  intro hd
  rcases hF.dvd_mul.mp hd with hc | hg
  · exact hFC (hF.dvd_of_dvd_pow hc)
  · exact hFG hg

#print axioms helper_capacity
#print axioms deflated_helper_vanishes
#print axioms deflated_helper_mem_box
#print axioms deflated_helper_mem_legacyBox
#print axioms deflated_helper_proper
end
end ProximityPrize.SubmissionLower.WeightedHelperDeflatedCapacityW1332216900
