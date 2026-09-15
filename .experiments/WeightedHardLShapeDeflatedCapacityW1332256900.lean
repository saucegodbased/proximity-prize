import WeightedSourceBoxQuotient6900
import Order2DeflatedHelperSpecialization6900

/-!
# Deflated-helper semantic adapter for the W=133225 hard L-shape

This is the exact W=133225 port of the accepted W=133224 adapter.  A source
element `(F*C)^j*G` retains order-11810 contact.  After selecting the prime
factor `F`, the literal helper `C^j*G` is nonzero, is not divisible by `F`,
lies in the joint helper box, and vanishes on every regular solution of `F`.

No nonvanishing assumption on the specialization of `C` is used.
-/
namespace ProximityPrize.SubmissionLower.WeightedHardLShapeDeflatedCapacityW1332256900

open Order2SourceBasisScaffold Order2SourceSpecializationScaffold
open WeightedSourceIndex6900 WeightedSourceSpace6900
open WeightedSourceBoxQuotient6900
open Order2DerivativeContactCapacity6900
open Order2DeflatedHelperSpecialization6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000

noncomputable section

abbrev Poly4 (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

variable {K : Type*} [Field K]

def contactOrder : Nat := 11810
def sourceCutoff : Nat := 2130677530
def wordDegree : Nat := 133225
def derivativeCap : Nat := 5248
def totalCap : Nat := 2624
def jetCap : Nat := 15993
def stageMax : Nat := 2624
def stageDelta : Nat := 47190
def agreement : Nat := 180413

theorem parameter_receipt :
    sourceCutoff=contactOrder*agreement ∧
    stageDelta=agreement-(wordDegree-2) ∧
    sourceCutoff/(wordDegree-2)=jetCap ∧
    derivativeCap/2=totalCap ∧
    stageMax=totalCap := by
  norm_num [sourceCutoff,contactOrder,agreement,stageDelta,wordDegree,
    jetCap,derivativeCap,totalCap,stageMax]

/-- Every literal weighted box embeds in the legacy four-cap box. -/
theorem weightedBox_le_globalBox (B W D : Nat) (hW : 3≤W) :
    weightedCoefficientBox K B W D≤
      globalOrder2CoefficientBox K B W (B/(W-2)) D (D/2) := by
  intro Q hQ
  have heq := reconstruct_all K B W D (show 0<W by omega) Q hQ
  rw [←heq]
  exact reconstruct_mem_legacyBox K B W D hW _

/-- The exact capacity identity is

`B-j*delta = (m-j)*agreement+j*(W-2)`.

The weak inequality allows a support larger than the agreement threshold.
-/
theorem helper_capacity (j supportCard : Nat)
    (hj : j≤stageMax) (ha : agreement≤supportCard) :
    sourceCutoff-j*stageDelta≤
      (contactOrder-j)*supportCard+j*(wordDegree-2) := by
  have hbase : sourceCutoff-j*stageDelta=
      (contactOrder-j)*agreement+j*(wordDegree-2) := by
    norm_num [sourceCutoff,stageDelta,contactOrder,agreement,wordDegree,
      stageMax] at hj ⊢
    omega
  rw [hbase]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left (contactOrder-j) ha) _

/-- Collision-safe solution vanishing.  The complement `C` remains inside
the helper; it is never cancelled after specialization. -/
theorem deflated_helper_vanishes
    {I : Type*} [DecidableEq K] [DecidableEq I]
    (F C G : Poly4 K) (P : Polynomial K) (nodes received : I→K)
    (support : Finset I) (j prime : Nat) [CharP K prime]
    (hprime : prime.Prime) (hchar : stageMax<prime) (hj : j≤stageMax)
    (hinj : Set.InjOn nodes support) (h2 : (2:K)≠0)
    (hP : P.natDegree≤wordDegree) (ha : agreement≤support.card)
    (hQ : (F*C)^j*G≠0)
    (hcontact : ∀ i∈support,contactTruncation K contactOrder
      (localSubstitution K (nodes i) (received i) ((F*C)^j*G))=0)
    (hvalues : ∀ i∈support,P.eval (nodes i)=received i)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (sourceCutoff-j*stageDelta) wordDegree derivativeCap)
    (hFzero : localJetSpecialization2 P F=0)
    (hregular : localJetSpecialization2 P
      (MvPolynomial.pderiv (3 : Fin 4) F)≠0) :
    localJetSpecialization2 P (C^j*G)=0 := by
  have hd := ((mem_weightedBox_iff (sourceCutoff-j*stageDelta)
    wordDegree derivativeCap ((F*C)^j*G)).mp htight).resolve_left hQ
  have hw : MvPolynomial.weightedTotalDegree (sourceWeights wordDegree)
      ((F*C)^j*G)<sourceCutoff-j*stageDelta := hd.1
  exact deflated_helper_specialization_eq_zero_of_capacity
    ((F*C)^j*G) F C G P nodes received support contactOrder j
    (sourceCutoff-j*stageDelta) wordDegree prime hprime
    (hj.trans_lt hchar) hinj h2 hP hcontact hvalues hw
    (helper_capacity j support.card hj ha) rfl hFzero hregular

/-- Nonzeroness descends from the multiplied source without assuming that
`C` evaluates nonzero at any solution. -/
theorem deflated_helper_ne_zero (F C G : Poly4 K) (j : Nat)
    (hQ : (F*C)^j*G≠0) : C^j*G≠0 := by
  intro hzero
  apply hQ
  rw [mul_pow,mul_assoc,hzero,mul_zero]

/-- Removing the selected factor from the source leaves the helper in the
original weighted source box. -/
theorem deflated_helper_mem_weightedBox (F C G : Poly4 K) (j : Nat)
    (hF : F≠0) (hQ : (F*C)^j*G≠0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (sourceCutoff-j*stageDelta) wordDegree derivativeCap) :
    C^j*G∈weightedCoefficientBox K sourceCutoff wordDegree derivativeCap := by
  have heq : (F*C)^j*G=F^j*(C^j*G) := by rw [mul_pow,mul_assoc]
  have hH : C^j*G≠0 := deflated_helper_ne_zero F C G j hQ
  have hbig : F^j*(C^j*G)∈
      weightedCoefficientBox K sourceCutoff wordDegree derivativeCap := by
    rw [←heq]
    intro e he
    have hd := htight he
    exact ⟨hd.1,hd.2.trans_le (Nat.sub_le _ _)⟩
  have hquot := (quotient_mem_weightedBox sourceCutoff wordDegree derivativeCap
    (F^j) (C^j*G) (pow_ne_zero j hF) hH hbig).2.2
  intro e he
  have hd := hquot he
  exact ⟨hd.1.trans (Nat.sub_le _ _),hd.2.trans_le (Nat.sub_le _ _)⟩

/-- Exact common helper box used by the one-source coupled count. -/
theorem deflated_helper_mem_globalBox (F C G : Poly4 K) (j : Nat)
    (hF : F≠0) (hQ : (F*C)^j*G≠0)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (sourceCutoff-j*stageDelta) wordDegree derivativeCap) :
    C^j*G∈globalOrder2CoefficientBox K sourceCutoff wordDegree
      jetCap derivativeCap totalCap := by
  have h := weightedBox_le_globalBox sourceCutoff wordDegree derivativeCap
    (K:=K) (by norm_num [wordDegree])
    (deflated_helper_mem_weightedBox F C G j hF hQ htight)
  simpa only [parameter_receipt.2.2.1,parameter_receipt.2.2.2.1] using h

/-- Prime properness is preserved under the literal complement power. -/
theorem deflated_helper_proper (F C G : Poly4 K) (j : Nat)
    (hF : Prime F) (hFC : ¬F∣C) (hFG : ¬F∣G) : ¬F∣C^j*G := by
  intro hd
  rcases hF.dvd_mul.mp hd with hc | hg
  · exact hFC (hF.dvd_of_dvd_pow hc)
  · exact hFG hg

/-- Count-facing semantic package after factor selection. -/
theorem deflated_helper_package
    {I : Type*} [DecidableEq K] [DecidableEq I]
    (F C G : Poly4 K) (P : Polynomial K) (nodes received : I→K)
    (support : Finset I) (j prime : Nat) [CharP K prime]
    (hF : Prime F) (hFC : ¬F∣C) (hFG : ¬F∣G)
    (hprime : prime.Prime) (hchar : stageMax<prime) (hj : j≤stageMax)
    (hinj : Set.InjOn nodes support) (h2 : (2:K)≠0)
    (hP : P.natDegree≤wordDegree) (ha : agreement≤support.card)
    (hC : C≠0) (hG : G≠0)
    (hcontact : ∀ i∈support,contactTruncation K contactOrder
      (localSubstitution K (nodes i) (received i) ((F*C)^j*G))=0)
    (hvalues : ∀ i∈support,P.eval (nodes i)=received i)
    (htight : (F*C)^j*G∈weightedCoefficientBox K
      (sourceCutoff-j*stageDelta) wordDegree derivativeCap)
    (hFzero : localJetSpecialization2 P F=0)
    (hregular : localJetSpecialization2 P
      (MvPolynomial.pderiv (3 : Fin 4) F)≠0) :
    C^j*G≠0 ∧
      C^j*G∈globalOrder2CoefficientBox K sourceCutoff wordDegree
        jetCap derivativeCap totalCap ∧
      ¬F∣C^j*G ∧ localJetSpecialization2 P (C^j*G)=0 := by
  have hQ : (F*C)^j*G≠0 :=
    mul_ne_zero (pow_ne_zero j (mul_ne_zero hF.ne_zero hC)) hG
  exact ⟨deflated_helper_ne_zero F C G j hQ,
    deflated_helper_mem_globalBox F C G j hF.ne_zero hQ htight,
    deflated_helper_proper F C G j hF hFC hFG,
    deflated_helper_vanishes F C G P nodes received support j prime hprime
      hchar hj hinj h2 hP ha hQ hcontact hvalues htight hFzero hregular⟩

#print axioms helper_capacity
#print axioms deflated_helper_vanishes
#print axioms deflated_helper_ne_zero
#print axioms deflated_helper_mem_weightedBox
#print axioms deflated_helper_mem_globalBox
#print axioms deflated_helper_proper
#print axioms deflated_helper_package

end
end ProximityPrize.SubmissionLower.WeightedHardLShapeDeflatedCapacityW1332256900
