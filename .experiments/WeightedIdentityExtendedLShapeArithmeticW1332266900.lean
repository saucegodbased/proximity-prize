import WeightedRepresentativeCountLedgerW1332246900
import Order2ReducedCutScaffold
import WeightedFactorFlagBudgetW1332246900

/-!
# Full-node extended-L arithmetic at W=133226

This is the arithmetic receipt for the uniform `N ≤ 262144` route.  Keep the
two old L-terminal arms and add two skinny terminals:

* `derivativeDegree ≤ 3`, embedded in the deliberately loose nested box
  `(J,RT,T)=(744,5,5)`;
* `jetDegree ≤ 32`, embedded in `(33,32,32)`.

The loosenings are semantic, not numerical decoration.  `T=1` gives a zero
`all` coordinate in the reduced agreement and cannot absorb small families;
`T=5` is the first integer that restores the curve absorption inequality.
Likewise `J=33` supplies the strict `RT<J` premise of the honest reduced-cut
support theorem.

Outside those skinny sets and the old L-shape, the three helper profiles are
`(jet,derivative)=(213,4)`, `(33,56)`, and the old corner `(212,55)`.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityExtendedLShapeArithmeticW1332266900

open RCN095
open Order2ReducedCutScaffold
open WeightedActualProductBandGate6900
open WeightedSourceBoxQuotient6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

def n : Nat := 262144
def w : Nat := 133226
def a : Nat := 180413
def v : Nat := 68769
def small : Nat := 1453806
def prime : Nat := 2130706433
def coreFloor : Nat := 263611557201523206

def primaryFlag : FlagDegree := ⟨500,122,122⟩
def helperFlag : FlagDegree := ⟨10745,2624,2624⟩
def primaryAgreement : FlagDegree := honestReducedAgreementFlag w 744 244 122

def armAFlag : FlagDegree := ⟨156,28,27⟩
def armBFlag : FlagDegree := ⟨158,27,27⟩
def armAExitFlag : FlagDegree := ⟨344,94,95⟩
def armBExitFlag : FlagDegree := ⟨342,95,95⟩
def armAAgreement : FlagDegree := honestReducedAgreementFlag w 211 55 27
def armBAgreement : FlagDegree := honestReducedAgreementFlag w 212 54 27

/-- Loose count box for an actual product of derivative degree at most three. -/
def derivativeSkinnyFlag : FlagDegree := ⟨739,0,5⟩
def derivativeSkinnyAgreement : FlagDegree :=
  honestReducedAgreementFlag w 744 5 5

/-- Loose count box for an actual product of jet degree at most 32. -/
def jetSkinnyFlag : FlagDegree := ⟨1,0,32⟩
def jetSkinnyAgreement : FlagDegree := honestReducedAgreementFlag w 33 32 32

def ceilQuotient (num den : Nat) : Nat := (num+den-1)/den

def commonNumerator (rest exit agreement : FlagDegree) : Nat :=
  (n-v)^2*flagMixed rest agreement agreement+
    (n-v)*(a-v)*flagMixed exit helperFlag primaryAgreement

def commonCap (rest exit agreement : FlagDegree) : Nat :=
  ceilQuotient (commonNumerator rest exit agreement) ((a-v)^2)

def helperExitCap : Nat :=
  ceilQuotient ((n-v)*flagMixed primaryFlag helperFlag primaryAgreement) (a-v)

def independentRestCap (source agreement : FlagDegree) : Nat :=
  ceilQuotient ((n-v)^2*flagMixed source agreement agreement) ((a-v)^2)

def firstOrderMixedCost (yCap rCap : Nat) : Nat :=
  (1+2*w*yCap)*rCap+w*(2*rCap-1)*yCap

def firstOrderRegularCap (yCap rCap : Nat) : Nat :=
  ceilQuotient ((n-w)*firstOrderMixedCost yCap rCap) (a-w)

def firstOrderSingularCap (yCap rCap : Nat) : Nat := (2*rCap-1)*yCap

def positiveTAuxY : Nat := (2*122-1)*744
def positiveTAuxR : Nat := (2*122-1)*244

def primaryCleanupCap : Nat :=
  firstOrderRegularCap positiveTAuxY positiveTAuxR+
    firstOrderSingularCap positiveTAuxY positiveTAuxR+
    firstOrderRegularCap 744 244+firstOrderSingularCap 744 244

def unitZ : FlagDegree := ⟨1,0,0⟩
def unitYZ : FlagDegree := ⟨0,1,0⟩
def unitAll : FlagDegree := ⟨0,0,1⟩

def cumulativeCosts (q r : FlagDegree) : Fin 3 → Nat :=
  ![flagMixed unitZ q r,
    flagMixed unitYZ q r-flagMixed unitZ q r,
    flagMixed unitAll q r-flagMixed unitYZ q r]

def ExtendedTerminalDegrees (J D : Nat) : Prop :=
  (J≤211 ∧ D≤55) ∨ (J≤212 ∧ D≤54) ∨ D≤3 ∨ J≤32

/-- Exact complement of the extended terminal.  These are precisely the
three joint band theorems listed in `formal_helper_band_margins`. -/
theorem helper_profiles_of_not_extended_terminal (J D : Nat)
    (h : ¬ExtendedTerminalDegrees J D) :
    (213≤J ∧ 4≤D) ∨ (33≤J ∧ 56≤D) ∨ (212≤J ∧ 55≤D) := by
  unfold ExtendedTerminalDegrees at h
  push Not at h
  rcases h with ⟨hA,hB,hD,hJ⟩
  by_cases hbigJ : 213≤J
  · exact Or.inl ⟨hbigJ,hD⟩
  by_cases hbigD : 56≤D
  · exact Or.inr (Or.inl ⟨hJ,hbigD⟩)
  right
  right
  constructor <;> omega

variable {K : Type} [Field K]

/-- A derivative-skinny product really does fit the loose `(744,5,5)` box.
The loosened T-cap, rather than the sharp cap one, is what keeps the reduced
agreement useful for small-family absorption. -/
theorem derivative_skinny_nested_bounds (P : MvPolynomial (Fin 4) K)
    (hJ : jetDegree P≤744) (hD : derivativeDegree P≤3) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤5 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤5 ∧ jetDegree P≤744 := by
  have hd := WeightedFactorFlagBudgetW1332246900.derivative_nested_bounds P
  exact ⟨hd.1.trans (by omega),hd.2.trans (by omega),hJ⟩

/-- A jet-skinny product fits `(33,32,32)`.  The one-unit J loosening supplies
the strict `RT<J` premise of the reduced-cut support theorem. -/
theorem jet_skinny_nested_bounds (P : MvPolynomial (Fin 4) K)
    (hJ : jetDegree P≤32) :
    MvPolynomial.weightedTotalDegree ![0,0,0,1] P≤32 ∧
    MvPolynomial.weightedTotalDegree ![0,0,1,1] P≤32 ∧ jetDegree P≤33 := by
  constructor
  · apply (RCN081.weightedTotalDegree_le_iff
      (![0,0,0,1] : Fin 4→Nat) P 32).mpr
    intro e he
    have hj := MvPolynomial.le_weightedTotalDegree jetWeights he
    rw [jetWeight_eq] at hj
    have hJ' : MvPolynomial.weightedTotalDegree jetWeights P≤32 := hJ
    have he3 : e 3≤e 1+e 2+e 3 := by omega
    rw [RCN081.weight_fin4]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    simpa using he3.trans (hj.trans hJ')
  constructor
  · apply (RCN081.weightedTotalDegree_le_iff
      (![0,0,1,1] : Fin 4→Nat) P 32).mpr
    intro e he
    have hj := MvPolynomial.le_weightedTotalDegree jetWeights he
    rw [jetWeight_eq] at hj
    have hJ' : MvPolynomial.weightedTotalDegree jetWeights P≤32 := hJ
    have he23 : e 2+e 3≤e 1+e 2+e 3 := by omega
    rw [RCN081.weight_fin4]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    simpa using he23.trans (hj.trans hJ')
  · omega

theorem flags_exact :
    primaryAgreement=⟨133092775,32640370,32240692⟩ ∧
    armAAgreement=⟨41433287,7593882,6927752⟩ ∧
    armBAgreement=⟨41966191,7327430,6927752⟩ ∧
    derivativeSkinnyAgreement=⟨196774803,133226,1065808⟩ ∧
    jetSkinnyAgreement=⟨133227,133226,8260012⟩ := by
  norm_num [primaryAgreement,armAAgreement,armBAgreement,
    derivativeSkinnyAgreement,jetSkinnyAgreement,
    honestReducedAgreementFlag,w]

/-- Exact conservative source dimensions used by the future kernel modules. -/
theorem source_dimension_receipts :
    394074801989406-262144*1503271269=1258448670 ∧
    82571120962332601259-262144*314478446061020=
      132483198112574379 := by
  norm_num

/-- These are the relaxed stage-band bounds, not the stronger exact-column
differences.  Thus these are the margins relevant to the existing Lean band
consumer. -/
theorem formal_helper_band_margins :
    131697390021082959<132483198112574379 ∧
    132414068905236615<132483198112574379 ∧
    90686016876092931<132483198112574379 ∧
    132483198112574379-131697390021082959=785808091491420 ∧
    132483198112574379-132414068905236615=69129207337764 ∧
    132483198112574379-90686016876092931=41797181236481448 := by
  norm_num

theorem uniform_shortened_Johnson_gate :
    (n-(v+1))*(n-w)<
      (small+1)*((a-(v+1))^2-(n-(v+1))*(w-(v+1))) ∧
    (small+1)*((a-(v+1))^2-(n-(v+1))*(w-(v+1)))-
      (n-(v+1))*(n-w)=40353814003 := by
  norm_num [n,v,w,a,small]

theorem armA_rest_resource_dominates_exit :
    ∀ i : Fin 3,
      (n-v)*(a-v)*cumulativeCosts helperFlag primaryAgreement i≤
        (n-v)^2*cumulativeCosts armAAgreement armAAgreement i := by
  intro i
  fin_cases i <;>
    norm_num [n,a,v,cumulativeCosts,unitZ,unitYZ,unitAll,helperFlag,
      primaryAgreement,armAAgreement,honestReducedAgreementFlag,w,flagMixed]

theorem armB_rest_resource_dominates_exit :
    ∀ i : Fin 3,
      (n-v)*(a-v)*cumulativeCosts helperFlag primaryAgreement i≤
        (n-v)^2*cumulativeCosts armBAgreement armBAgreement i := by
  intro i
  fin_cases i <;>
    norm_num [n,a,v,cumulativeCosts,unitZ,unitYZ,unitAll,helperFlag,
      primaryAgreement,armBAgreement,honestReducedAgreementFlag,w,flagMixed]

theorem active_caps_exact :
    commonCap armAFlag armAExitFlag armAAgreement=247945303343219481 ∧
    commonCap armBFlag armBExitFlag armBAgreement=244053597157924510 ∧
    helperExitCap=788423032100813 ∧
    independentRestCap derivativeSkinnyFlag derivativeSkinnyAgreement=
      10247951347274314 ∧
    independentRestCap jetSkinnyFlag jetSkinnyAgreement=7188982987108962 := by
  norm_num [commonCap,commonNumerator,helperExitCap,independentRestCap,
    ceilQuotient,n,a,v,primaryFlag,helperFlag,primaryAgreement,
    armAFlag,armAExitFlag,armAAgreement,armBFlag,armBExitFlag,armBAgreement,
    derivativeSkinnyFlag,derivativeSkinnyAgreement,jetSkinnyFlag,
    jetSkinnyAgreement,honestReducedAgreementFlag,w,flagMixed]

theorem cleanup_exact : primaryCleanupCap=15607077754697448 := by
  norm_num [primaryCleanupCap,positiveTAuxY,positiveTAuxR,
    firstOrderRegularCap,firstOrderSingularCap,firstOrderMixedCost,
    ceilQuotient,n,w,a]

theorem all_terminal_ledgers_green :
    commonCap armAFlag armAExitFlag armAAgreement+primaryCleanupCap=
      263552381097916929 ∧
    coreFloor-263552381097916929=59176103606277 ∧
    commonCap armBFlag armBExitFlag armBAgreement+primaryCleanupCap=
      259660674912621958 ∧
    independentRestCap derivativeSkinnyFlag derivativeSkinnyAgreement+
        helperExitCap+primaryCleanupCap=26643452134072575 ∧
    independentRestCap jetSkinnyFlag jetSkinnyAgreement+
        helperExitCap+primaryCleanupCap=23584483773907223 ∧
    263552381097916929<coreFloor ∧
    259660674912621958<coreFloor ∧
    26643452134072575<coreFloor ∧
    23584483773907223<coreFloor := by
  rw [active_caps_exact.1,active_caps_exact.2.1,
    active_caps_exact.2.2.1,active_caps_exact.2.2.2.1,
    active_caps_exact.2.2.2.2,cleanup_exact]
  norm_num [coreFloor]

/-- Every reduced-cut absorption and finite-characteristic gate needed by the
four terminal consumers.  In particular, the deliberately loose `T=5` skinny
box clears the formerly failing one-incidence absorption inequality. -/
theorem terminal_semantic_numeric_gates :
    small*(a-v)≤(n-v)*armAAgreement.all ∧
    small*(a-v)^2≤(n-v)^2*armAAgreement.all^2 ∧
    small*(a-v)≤(n-v)*armBAgreement.all ∧
    small*(a-v)^2≤(n-v)^2*armBAgreement.all^2 ∧
    small*(a-v)≤(n-v)*derivativeSkinnyAgreement.all ∧
    small*(a-v)^2≤(n-v)^2*derivativeSkinnyAgreement.all^2 ∧
    small*(a-v)≤(n-v)*jetSkinnyAgreement.all ∧
    small*(a-v)^2≤(n-v)^2*jetSkinnyAgreement.all^2 ∧
    (armAAgreement.yz+armAAgreement.all)*armAFlag.all+
      (armAFlag.yz+armAFlag.all)*armAAgreement.all<prime ∧
    (armBAgreement.yz+armBAgreement.all)*armBFlag.all+
      (armBFlag.yz+armBFlag.all)*armBAgreement.all<prime ∧
    (derivativeSkinnyAgreement.yz+derivativeSkinnyAgreement.all)*
        derivativeSkinnyFlag.all+
      (derivativeSkinnyFlag.yz+derivativeSkinnyFlag.all)*
        derivativeSkinnyAgreement.all<prime ∧
    (jetSkinnyAgreement.yz+jetSkinnyAgreement.all)*jetSkinnyFlag.all+
      (jetSkinnyFlag.yz+jetSkinnyFlag.all)*jetSkinnyAgreement.all<prime := by
  norm_num [small,a,v,n,armAAgreement,armBAgreement,
    derivativeSkinnyAgreement,jetSkinnyAgreement,armAFlag,armBFlag,
    derivativeSkinnyFlag,jetSkinnyFlag,honestReducedAgreementFlag,w,prime]

theorem helper_projection_gate :
    (helperFlag.yz+helperFlag.all)*primaryFlag.all+
      (primaryFlag.yz+primaryFlag.all)*helperFlag.all<prime := by
  norm_num [helperFlag,primaryFlag,prime]

#print axioms source_dimension_receipts
#print axioms helper_profiles_of_not_extended_terminal
#print axioms derivative_skinny_nested_bounds
#print axioms jet_skinny_nested_bounds
#print axioms formal_helper_band_margins
#print axioms uniform_shortened_Johnson_gate
#print axioms armA_rest_resource_dominates_exit
#print axioms active_caps_exact
#print axioms cleanup_exact
#print axioms all_terminal_ledgers_green
#print axioms terminal_semantic_numeric_gates

end ProximityPrize.SubmissionLower.WeightedIdentityExtendedLShapeArithmeticW1332266900
