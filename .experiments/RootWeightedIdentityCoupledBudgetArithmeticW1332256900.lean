import WeightedIdentityLShapeCornerW1332256900

/-!
# Independent arithmetic receipt for the coupled W=133225 terminal ledger

The terminal remainder and the factors exited by helper descent partition the
same original factor set.  They must therefore share the primary nested flag
budget instead of each being charged against the full budget.  This file
records the endpoint costs and the coefficientwise dominance that makes the
coupled linear optimization attain its maximum at the full terminal arm.

This is an arithmetic/interface receipt, not the semantic partition theorem.
-/
namespace ProximityPrize.SubmissionLower.RootWeightedIdentityCoupledBudgetArithmeticW1332256900

open RCN095

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

def n : Nat := 262143
def a : Nat := 180413
def v : Nat := 68763
def coreFloor : Nat := 263611557201785349

def primaryFlag : FlagDegree := ⟨496,122,122⟩
def maxHelperFlag : FlagDegree := ⟨10228,2480,2480⟩
/-- One source profile `(k,m,M,D,T)=(1312,11810,15993,5248,2624)`
handles both outer arms and the joint corner.  This slightly larger envelope
avoids all heterogeneous-helper bookkeeping. -/
def jointHelperFlag : FlagDegree := ⟨10745,2624,2624⟩
def primaryAgreement : FlagDegree := ⟨132025976,32640125,32240450⟩

def armAFlag : FlagDegree := ⟨156,28,27⟩
def armBFlag : FlagDegree := ⟨158,27,27⟩
def armAAgreement : FlagDegree := ⟨41432976,7593825,6927700⟩
def armBAgreement : FlagDegree := ⟨41965876,7327375,6927700⟩

/-- The complementary component flags when a terminal arm saturates its
three nested primary budgets. -/
def armAExitFlag : FlagDegree := ⟨340,94,95⟩
def armBExitFlag : FlagDegree := ⟨338,95,95⟩

def commonNumerator (rest exit agreement : FlagDegree) : Nat :=
  (n-v)^2 * flagMixed rest agreement agreement +
    (n-v)*(a-v) * flagMixed exit maxHelperFlag primaryAgreement

def ceilQuotient (num den : Nat) : Nat := (num+den-1)/den

def commonCap (rest exit agreement : FlagDegree) : Nat :=
  ceilQuotient (commonNumerator rest exit agreement) ((a-v)^2)

def jointCommonNumerator (rest exit agreement : FlagDegree) : Nat :=
  (n-v)^2 * flagMixed rest agreement agreement +
    (n-v)*(a-v) * flagMixed exit jointHelperFlag primaryAgreement

def jointCommonCap (rest exit agreement : FlagDegree) : Nat :=
  ceilQuotient (jointCommonNumerator rest exit agreement) ((a-v)^2)

def unitZ : FlagDegree := ⟨1,0,0⟩
def unitYZ : FlagDegree := ⟨0,1,0⟩
def unitAll : FlagDegree := ⟨0,0,1⟩

/-- Costs in the cumulative `(total,middle,all)` resource basis. -/
def cumulativeCosts (q r : FlagDegree) : Fin 3 → Nat :=
  ![flagMixed unitZ q r,
    flagMixed unitYZ q r - flagMixed unitZ q r,
    flagMixed unitAll q r - flagMixed unitYZ q r]

theorem complementary_flags_exact :
    armAFlag.zOnly+armAExitFlag.zOnly=primaryFlag.zOnly ∧
    armAFlag.yz+armAExitFlag.yz=primaryFlag.yz ∧
    armAFlag.all+armAExitFlag.all=primaryFlag.all ∧
    armBFlag.zOnly+armBExitFlag.zOnly=primaryFlag.zOnly ∧
    armBFlag.yz+armBExitFlag.yz=primaryFlag.yz ∧
    armBFlag.all+armBExitFlag.all=primaryFlag.all := by
  norm_num [armAFlag,armAExitFlag,armBFlag,armBExitFlag,primaryFlag]

/-- Moving any one nested degree resource from the exited side to the arm-A
remainder can only increase the common-denominator numerator. -/
theorem armA_rest_resource_dominates_exit :
    ∀ i : Fin 3,
      (n-v)*(a-v)*cumulativeCosts maxHelperFlag primaryAgreement i ≤
        (n-v)^2*cumulativeCosts armAAgreement armAAgreement i := by
  intro i
  fin_cases i <;>
    norm_num [n,a,v,cumulativeCosts,unitZ,unitYZ,unitAll,maxHelperFlag,
      primaryAgreement,armAAgreement,flagMixed]

/-- The same dominance holds for the second terminal arm. -/
theorem armB_rest_resource_dominates_exit :
    ∀ i : Fin 3,
      (n-v)*(a-v)*cumulativeCosts maxHelperFlag primaryAgreement i ≤
        (n-v)^2*cumulativeCosts armBAgreement armBAgreement i := by
  intro i
  fin_cases i <;>
    norm_num [n,a,v,cumulativeCosts,unitZ,unitYZ,unitAll,maxHelperFlag,
      primaryAgreement,armBAgreement,flagMixed]

theorem armA_rest_resource_dominates_joint_exit :
    ∀ i : Fin 3,
      (n-v)*(a-v)*cumulativeCosts jointHelperFlag primaryAgreement i ≤
        (n-v)^2*cumulativeCosts armAAgreement armAAgreement i := by
  intro i
  fin_cases i <;>
    norm_num [n,a,v,cumulativeCosts,unitZ,unitYZ,unitAll,jointHelperFlag,
      primaryAgreement,armAAgreement,flagMixed]

theorem armB_rest_resource_dominates_joint_exit :
    ∀ i : Fin 3,
      (n-v)*(a-v)*cumulativeCosts jointHelperFlag primaryAgreement i ≤
        (n-v)^2*cumulativeCosts armBAgreement armBAgreement i := by
  intro i
  fin_cases i <;>
    norm_num [n,a,v,cumulativeCosts,unitZ,unitYZ,unitAll,jointHelperFlag,
      primaryAgreement,armBAgreement,flagMixed]

theorem coupled_caps_exact :
    commonCap armAFlag armAExitFlag armAAgreement=247893461599917381 ∧
    commonCap armBFlag armBExitFlag armBAgreement=244001988473045789 := by
  norm_num [commonCap,commonNumerator,ceilQuotient,n,a,v,armAFlag,
    armAExitFlag,armAAgreement,armBFlag,armBExitFlag,armBAgreement,
    maxHelperFlag,primaryAgreement,flagMixed]

theorem joint_coupled_caps_exact :
    jointCommonCap armAFlag armAExitFlag armAAgreement=247924633751427236 ∧
    jointCommonCap armBFlag armBExitFlag armBAgreement=244033198200074653 := by
  norm_num [jointCommonCap,jointCommonNumerator,ceilQuotient,n,a,v,armAFlag,
    armAExitFlag,armAAgreement,armBFlag,armBExitFlag,armBAgreement,
    jointHelperFlag,primaryAgreement,flagMixed]

theorem joint_armA_complete_headroom_exact :
    jointCommonCap armAFlag armAExitFlag armAAgreement +
        15522723255702274 = 263447357007129510 ∧
    coreFloor - 263447357007129510 = 164200194655839 ∧
    263447357007129510 < coreFloor := by
  rw [joint_coupled_caps_exact.1]
  norm_num [coreFloor]

theorem armA_complete_headroom_exact :
    commonCap armAFlag armAExitFlag armAAgreement +
        15522723255702274 = 263416184855619655 ∧
    coreFloor - 263416184855619655 = 195372346165694 ∧
    263416184855619655 < coreFloor := by
  rw [coupled_caps_exact.1]
  norm_num [coreFloor]

theorem armB_complete_headroom_exact :
    commonCap armBFlag armBExitFlag armBAgreement +
        15522723255702274 = 259524711728748063 ∧
    coreFloor - 259524711728748063 = 4086845473037286 ∧
    259524711728748063 < coreFloor := by
  rw [coupled_caps_exact.2]
  norm_num [coreFloor]

#print axioms armA_rest_resource_dominates_exit
#print axioms armB_rest_resource_dominates_exit
#print axioms coupled_caps_exact
#print axioms joint_coupled_caps_exact
#print axioms joint_armA_complete_headroom_exact
#print axioms armA_complete_headroom_exact
#print axioms armB_complete_headroom_exact

end ProximityPrize.SubmissionLower.RootWeightedIdentityCoupledBudgetArithmeticW1332256900
