import RootWeightedIdentityCoupledBudgetArithmeticW1332256900
import WeightedHeavyBatchPartitionW1332246900

/-!
# Independent coupled-flag critic for the W=133225 L-shaped terminal

This file supplies the algebra that is deliberately absent from the endpoint
arithmetic receipt.  The terminal rest and the helper exits are charged against
one partitioned cumulative flag budget.  In particular, it never charges the
full primary flag to both sides.

The final endpoint corollaries cover both the two-producer/common-D-box profile
and the slightly larger single-source helper profile.
-/
namespace ProximityPrize.SubmissionLower.IdentityLShapeCoupledFlagCriticW1332256900

open RCN095

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

namespace Ledger
def n : Nat := 262143
def a : Nat := 180413
def v : Nat := 68763
def primaryFlag : FlagDegree := ⟨496,122,122⟩
def maxHelperFlag : FlagDegree := ⟨10228,2480,2480⟩
def jointHelperFlag : FlagDegree := ⟨10745,2624,2624⟩
def primaryAgreement : FlagDegree := ⟨132025976,32640125,32240450⟩
def armAFlag : FlagDegree := ⟨156,28,27⟩
def armAExitFlag : FlagDegree := ⟨340,94,95⟩
def armAAgreement : FlagDegree := ⟨41432976,7593825,6927700⟩
def armBFlag : FlagDegree := ⟨158,27,27⟩
def armBExitFlag : FlagDegree := ⟨338,95,95⟩
def armBAgreement : FlagDegree := ⟨41965876,7327375,6927700⟩
def commonNumerator (rest exit agreement : FlagDegree) : Nat :=
  (n-v)^2*flagMixed rest agreement agreement+
    (n-v)*(a-v)*flagMixed exit maxHelperFlag primaryAgreement
def jointCommonNumerator (rest exit agreement : FlagDegree) : Nat :=
  (n-v)^2*flagMixed rest agreement agreement+
    (n-v)*(a-v)*flagMixed exit jointHelperFlag primaryAgreement
end Ledger

def cumulativeTotal (p : FlagDegree) : Nat := p.zOnly+p.yz+p.all
def cumulativeMiddle (p : FlagDegree) : Nat := p.yz+p.all
def cumulativeAll (p : FlagDegree) : Nat := p.all

/-- Coordinatewise order in the nested `(total,middle,all)` resources. -/
def CumulativeLE (p q : FlagDegree) : Prop :=
  cumulativeTotal p≤cumulativeTotal q ∧
  cumulativeMiddle p≤cumulativeMiddle q ∧
  cumulativeAll p≤cumulativeAll q

/-- The resources on two disjoint pieces fit in one ambient flag. -/
def CumulativeSumLE (p q ambient : FlagDegree) : Prop :=
  cumulativeTotal p+cumulativeTotal q≤cumulativeTotal ambient ∧
  cumulativeMiddle p+cumulativeMiddle q≤cumulativeMiddle ambient ∧
  cumulativeAll p+cumulativeAll q≤cumulativeAll ambient

/-- `out` represents the cumulative resource complement `ambient-cap`. -/
def CumulativeComplement (out ambient cap : FlagDegree) : Prop :=
  cumulativeTotal out=cumulativeTotal ambient-cumulativeTotal cap ∧
  cumulativeMiddle out=cumulativeMiddle ambient-cumulativeMiddle cap ∧
  cumulativeAll out=cumulativeAll ambient-cumulativeAll cap

def totalMarginal (q r : FlagDegree) : Nat :=
  flagMixed unitZFlag q r

def middleMarginal (q r : FlagDegree) : Nat :=
  flagMixed unitYZFlag q r-flagMixed unitZFlag q r

def allMarginal (q r : FlagDegree) : Nat :=
  flagMixed unitAllFlag q r-flagMixed unitYZFlag q r

/-- `flagMixed` is linear in the three cumulative resources. -/
theorem flagMixed_eq_cumulative (p q r : FlagDegree) :
    flagMixed p q r=
      totalMarginal q r*cumulativeTotal p+
      middleMarginal q r*cumulativeMiddle p+
      allMarginal q r*cumulativeAll p := by
  let z := flagMixed unitZFlag q r
  let y := flagMixed unitYZFlag q r
  let a := flagMixed unitAllFlag q r
  have hzy : z≤y := by
    simp [z,y,flagMixed,unitZFlag,unitYZFlag]
    nlinarith
  have hya : y≤a := by
    simp [y,a,flagMixed,unitYZFlag,unitAllFlag]
    nlinarith
  calc
    flagMixed p q r=p.zOnly*z+p.yz*y+p.all*a := by
      simp only [z,y,a,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
      ring
    _=z*(p.zOnly+p.yz+p.all)+(y-z)*(p.yz+p.all)+(a-y)*p.all :=
      RCN131.linear_cost_cumulative z y a p hzy hya
    _=_ := by
      simp only [totalMarginal,middleMarginal,allMarginal,cumulativeTotal,
        cumulativeMiddle,cumulativeAll,z,y,a]

/-- The scalar exchange lemma.  If a unit is at least as expensive on the
rest side as on the exit side, the worst allocation fills the rest cap first.
-/
theorem coupled_one_resource
    (rest exit ambient cap restCost exitCost : Nat)
    (hpartition : rest+exit≤ambient)
    (hrest : rest≤cap) (hcap : cap≤ambient)
    (hdominance : exitCost≤restCost) :
    restCost*rest+exitCost*exit≤
      restCost*cap+exitCost*(ambient-cap) := by
  calc
    restCost*rest+exitCost*exit=
        ((restCost-exitCost)+exitCost)*rest+exitCost*exit := by
      rw [Nat.sub_add_cancel hdominance]
    _=
        exitCost*(rest+exit)+(restCost-exitCost)*rest := by
      ring
    _≤exitCost*ambient+(restCost-exitCost)*cap :=
      Nat.add_le_add (Nat.mul_le_mul_left exitCost hpartition)
        (Nat.mul_le_mul_left (restCost-exitCost) hrest)
    _=exitCost*((ambient-cap)+cap)+(restCost-exitCost)*cap := by
      rw [Nat.sub_add_cancel hcap]
    _=((restCost-exitCost)+exitCost)*cap+
        exitCost*(ambient-cap) := by
      ring
    _=restCost*cap+exitCost*(ambient-cap) := by
      rw [Nat.sub_add_cancel hdominance]

/-- Generic three-resource coupling.  The hypotheses are exactly what a
strict disjoint factor partition and an L-terminal rest provide. -/
theorem coupled_flagMixed_le
    (rest exit ambient cap complement : FlagDegree)
    (restQ restR exitQ exitR : FlagDegree) (restScale exitScale : Nat)
    (hpartition : CumulativeSumLE rest exit ambient)
    (hrest : CumulativeLE rest cap)
    (hcap : CumulativeLE cap ambient)
    (hcomplement : CumulativeComplement complement ambient cap)
    (hTotalDominance :
      exitScale*totalMarginal exitQ exitR≤
        restScale*totalMarginal restQ restR)
    (hMiddleDominance :
      exitScale*middleMarginal exitQ exitR≤
        restScale*middleMarginal restQ restR)
    (hAllDominance :
      exitScale*allMarginal exitQ exitR≤
        restScale*allMarginal restQ restR) :
    restScale*flagMixed rest restQ restR+
        exitScale*flagMixed exit exitQ exitR≤
      restScale*flagMixed cap restQ restR+
        exitScale*flagMixed complement exitQ exitR := by
  rcases hpartition with ⟨hpartTotal,hpartMiddle,hpartAll⟩
  rcases hrest with ⟨hrestTotal,hrestMiddle,hrestAll⟩
  rcases hcap with ⟨hcapTotal,hcapMiddle,hcapAll⟩
  rcases hcomplement with ⟨hcompTotal,hcompMiddle,hcompAll⟩
  have hTotal := coupled_one_resource
    (cumulativeTotal rest) (cumulativeTotal exit) (cumulativeTotal ambient)
    (cumulativeTotal cap)
    (restScale*totalMarginal restQ restR)
    (exitScale*totalMarginal exitQ exitR)
    hpartTotal hrestTotal hcapTotal hTotalDominance
  have hMiddle := coupled_one_resource
    (cumulativeMiddle rest) (cumulativeMiddle exit) (cumulativeMiddle ambient)
    (cumulativeMiddle cap)
    (restScale*middleMarginal restQ restR)
    (exitScale*middleMarginal exitQ exitR)
    hpartMiddle hrestMiddle hcapMiddle hMiddleDominance
  have hAll := coupled_one_resource
    (cumulativeAll rest) (cumulativeAll exit) (cumulativeAll ambient)
    (cumulativeAll cap)
    (restScale*allMarginal restQ restR)
    (exitScale*allMarginal exitQ exitR)
    hpartAll hrestAll hcapAll hAllDominance
  rw [←hcompTotal] at hTotal
  rw [←hcompMiddle] at hMiddle
  rw [←hcompAll] at hAll
  simp only [flagMixed_eq_cumulative]
  calc
    restScale*(totalMarginal restQ restR*cumulativeTotal rest+
          middleMarginal restQ restR*cumulativeMiddle rest+
          allMarginal restQ restR*cumulativeAll rest)+
        exitScale*(totalMarginal exitQ exitR*cumulativeTotal exit+
          middleMarginal exitQ exitR*cumulativeMiddle exit+
          allMarginal exitQ exitR*cumulativeAll exit)=
      ((restScale*totalMarginal restQ restR)*cumulativeTotal rest+
        (exitScale*totalMarginal exitQ exitR)*cumulativeTotal exit)+
      ((restScale*middleMarginal restQ restR)*cumulativeMiddle rest+
        (exitScale*middleMarginal exitQ exitR)*cumulativeMiddle exit)+
      ((restScale*allMarginal restQ restR)*cumulativeAll rest+
        (exitScale*allMarginal exitQ exitR)*cumulativeAll exit) := by ring
    _≤
      ((restScale*totalMarginal restQ restR)*cumulativeTotal cap+
        (exitScale*totalMarginal exitQ exitR)*cumulativeTotal complement)+
      ((restScale*middleMarginal restQ restR)*cumulativeMiddle cap+
        (exitScale*middleMarginal exitQ exitR)*cumulativeMiddle complement)+
      ((restScale*allMarginal restQ restR)*cumulativeAll cap+
        (exitScale*allMarginal exitQ exitR)*cumulativeAll complement) :=
      Nat.add_le_add (Nat.add_le_add hTotal hMiddle) hAll
    _=restScale*(totalMarginal restQ restR*cumulativeTotal cap+
          middleMarginal restQ restR*cumulativeMiddle cap+
          allMarginal restQ restR*cumulativeAll cap)+
        exitScale*(totalMarginal exitQ exitR*cumulativeTotal complement+
          middleMarginal exitQ exitR*cumulativeMiddle complement+
          allMarginal exitQ exitR*cumulativeAll complement) := by ring

/-- Exact arithmetic classification of every nonterminal L-shape point. -/
def LTerminal (J D : Nat) : Prop :=
  (J≤211 ∧ D≤55) ∨ (J≤212 ∧ D≤54)

theorem not_LTerminal_cases (J D : Nat) (h : ¬LTerminal J D) :
    56≤D ∨ (D≤55 ∧ (213≤J ∨ (J=212 ∧ D=55))) := by
  unfold LTerminal at h
  omega

theorem corner_is_not_terminal : ¬LTerminal 212 55 := by
  norm_num [LTerminal]

theorem empty_degrees_are_terminal : LTerminal 0 0 := by
  norm_num [LTerminal]

/-- Common-D-box coupling at arm A.  These are the exact hypotheses the
partition glue must preserve instead of separately aggregating both sides. -/
theorem armA_commonHelper_coupled_numerator_le
    (rest exit : FlagDegree)
    (hpartition : CumulativeSumLE rest exit Ledger.primaryFlag)
    (hrest : CumulativeLE rest Ledger.armAFlag) :
    (Ledger.n-Ledger.v)^2*
          flagMixed rest Ledger.armAAgreement Ledger.armAAgreement+
        (Ledger.n-Ledger.v)*(Ledger.a-Ledger.v)*
          flagMixed exit Ledger.maxHelperFlag Ledger.primaryAgreement≤
      Ledger.commonNumerator Ledger.armAFlag Ledger.armAExitFlag
        Ledger.armAAgreement := by
  unfold Ledger.commonNumerator
  apply coupled_flagMixed_le rest exit Ledger.primaryFlag Ledger.armAFlag
    Ledger.armAExitFlag Ledger.armAAgreement Ledger.armAAgreement
    Ledger.maxHelperFlag Ledger.primaryAgreement
  · exact hpartition
  · exact hrest
  · norm_num [CumulativeLE,cumulativeTotal,cumulativeMiddle,cumulativeAll,
      Ledger.armAFlag,Ledger.primaryFlag]
  · norm_num [CumulativeComplement,cumulativeTotal,cumulativeMiddle,
      cumulativeAll,Ledger.armAExitFlag,Ledger.armAFlag,Ledger.primaryFlag]
  · norm_num [totalMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armAAgreement,
      Ledger.maxHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag]
  · norm_num [middleMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armAAgreement,
      Ledger.maxHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag,
      unitYZFlag]
  · norm_num [allMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armAAgreement,
      Ledger.maxHelperFlag,Ledger.primaryAgreement,flagMixed,unitYZFlag,
      unitAllFlag]

/-- The current one-source helper envelope is also safely coupled. -/
theorem armA_jointHelper_coupled_numerator_le
    (rest exit : FlagDegree)
    (hpartition : CumulativeSumLE rest exit Ledger.primaryFlag)
    (hrest : CumulativeLE rest Ledger.armAFlag) :
    (Ledger.n-Ledger.v)^2*
          flagMixed rest Ledger.armAAgreement Ledger.armAAgreement+
        (Ledger.n-Ledger.v)*(Ledger.a-Ledger.v)*
          flagMixed exit Ledger.jointHelperFlag Ledger.primaryAgreement≤
      Ledger.jointCommonNumerator Ledger.armAFlag Ledger.armAExitFlag
        Ledger.armAAgreement := by
  unfold Ledger.jointCommonNumerator
  apply coupled_flagMixed_le rest exit Ledger.primaryFlag Ledger.armAFlag
    Ledger.armAExitFlag Ledger.armAAgreement Ledger.armAAgreement
    Ledger.jointHelperFlag Ledger.primaryAgreement
  · exact hpartition
  · exact hrest
  · norm_num [CumulativeLE,cumulativeTotal,cumulativeMiddle,cumulativeAll,
      Ledger.armAFlag,Ledger.primaryFlag]
  · norm_num [CumulativeComplement,cumulativeTotal,cumulativeMiddle,
      cumulativeAll,Ledger.armAExitFlag,Ledger.armAFlag,Ledger.primaryFlag]
  · norm_num [totalMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armAAgreement,
      Ledger.jointHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag]
  · norm_num [middleMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armAAgreement,
      Ledger.jointHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag,
      unitYZFlag]
  · norm_num [allMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armAAgreement,
      Ledger.jointHelperFlag,Ledger.primaryAgreement,flagMixed,unitYZFlag,
      unitAllFlag]

theorem armB_commonHelper_coupled_numerator_le
    (rest exit : FlagDegree)
    (hpartition : CumulativeSumLE rest exit Ledger.primaryFlag)
    (hrest : CumulativeLE rest Ledger.armBFlag) :
    (Ledger.n-Ledger.v)^2*
          flagMixed rest Ledger.armBAgreement Ledger.armBAgreement+
        (Ledger.n-Ledger.v)*(Ledger.a-Ledger.v)*
          flagMixed exit Ledger.maxHelperFlag Ledger.primaryAgreement≤
      Ledger.commonNumerator Ledger.armBFlag Ledger.armBExitFlag
        Ledger.armBAgreement := by
  unfold Ledger.commonNumerator
  apply coupled_flagMixed_le rest exit Ledger.primaryFlag Ledger.armBFlag
    Ledger.armBExitFlag Ledger.armBAgreement Ledger.armBAgreement
    Ledger.maxHelperFlag Ledger.primaryAgreement
  · exact hpartition
  · exact hrest
  · norm_num [CumulativeLE,cumulativeTotal,cumulativeMiddle,cumulativeAll,
      Ledger.armBFlag,Ledger.primaryFlag]
  · norm_num [CumulativeComplement,cumulativeTotal,cumulativeMiddle,
      cumulativeAll,Ledger.armBExitFlag,Ledger.armBFlag,Ledger.primaryFlag]
  · norm_num [totalMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armBAgreement,
      Ledger.maxHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag]
  · norm_num [middleMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armBAgreement,
      Ledger.maxHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag,
      unitYZFlag]
  · norm_num [allMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armBAgreement,
      Ledger.maxHelperFlag,Ledger.primaryAgreement,flagMixed,unitYZFlag,
      unitAllFlag]

theorem armB_jointHelper_coupled_numerator_le
    (rest exit : FlagDegree)
    (hpartition : CumulativeSumLE rest exit Ledger.primaryFlag)
    (hrest : CumulativeLE rest Ledger.armBFlag) :
    (Ledger.n-Ledger.v)^2*
          flagMixed rest Ledger.armBAgreement Ledger.armBAgreement+
        (Ledger.n-Ledger.v)*(Ledger.a-Ledger.v)*
          flagMixed exit Ledger.jointHelperFlag Ledger.primaryAgreement≤
      Ledger.jointCommonNumerator Ledger.armBFlag Ledger.armBExitFlag
        Ledger.armBAgreement := by
  unfold Ledger.jointCommonNumerator
  apply coupled_flagMixed_le rest exit Ledger.primaryFlag Ledger.armBFlag
    Ledger.armBExitFlag Ledger.armBAgreement Ledger.armBAgreement
    Ledger.jointHelperFlag Ledger.primaryAgreement
  · exact hpartition
  · exact hrest
  · norm_num [CumulativeLE,cumulativeTotal,cumulativeMiddle,cumulativeAll,
      Ledger.armBFlag,Ledger.primaryFlag]
  · norm_num [CumulativeComplement,cumulativeTotal,cumulativeMiddle,
      cumulativeAll,Ledger.armBExitFlag,Ledger.armBFlag,Ledger.primaryFlag]
  · norm_num [totalMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armBAgreement,
      Ledger.jointHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag]
  · norm_num [middleMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armBAgreement,
      Ledger.jointHelperFlag,Ledger.primaryAgreement,flagMixed,unitZFlag,
      unitYZFlag]
  · norm_num [allMarginal,Ledger.n,Ledger.v,Ledger.a,Ledger.armBAgreement,
      Ledger.jointHelperFlag,Ledger.primaryAgreement,flagMixed,unitYZFlag,
      unitAllFlag]

def ceilQuotient (num den : Nat) : Nat := (num+den-1)/den

theorem exact_endpoint_caps_and_headroom :
    ceilQuotient
        (Ledger.commonNumerator Ledger.armAFlag Ledger.armAExitFlag
          Ledger.armAAgreement) ((Ledger.a-Ledger.v)^2)=247893461599917381 ∧
    ceilQuotient
        (Ledger.commonNumerator Ledger.armBFlag Ledger.armBExitFlag
          Ledger.armBAgreement) ((Ledger.a-Ledger.v)^2)=244001988473045789 ∧
    ceilQuotient
        (Ledger.jointCommonNumerator Ledger.armAFlag Ledger.armAExitFlag
          Ledger.armAAgreement) ((Ledger.a-Ledger.v)^2)=247924633751427236 ∧
    ceilQuotient
        (Ledger.jointCommonNumerator Ledger.armBFlag Ledger.armBExitFlag
          Ledger.armBAgreement) ((Ledger.a-Ledger.v)^2)=244033198200074653 ∧
    247893461599917381+15522723255702274=263416184855619655 ∧
    263611557201785349-263416184855619655=195372346165694 ∧
    247924633751427236+15522723255702274=263447357007129510 ∧
    263611557201785349-263447357007129510=164200194655839 := by
  norm_num [ceilQuotient,Ledger.commonNumerator,Ledger.jointCommonNumerator,
    Ledger.n,Ledger.a,Ledger.v,Ledger.armAFlag,Ledger.armAExitFlag,
    Ledger.armAAgreement,Ledger.armBFlag,Ledger.armBExitFlag,
    Ledger.armBAgreement,Ledger.maxHelperFlag,Ledger.jointHelperFlag,
    Ledger.primaryAgreement,flagMixed]

#print axioms flagMixed_eq_cumulative
#print axioms coupled_one_resource
#print axioms coupled_flagMixed_le
#print axioms not_LTerminal_cases
#print axioms armA_commonHelper_coupled_numerator_le
#print axioms armA_jointHelper_coupled_numerator_le
#print axioms armB_commonHelper_coupled_numerator_le
#print axioms armB_jointHelper_coupled_numerator_le
#print axioms exact_endpoint_caps_and_headroom

end ProximityPrize.SubmissionLower.IdentityLShapeCoupledFlagCriticW1332256900
