import WeightedIdentityCoreLedgerW1332256900

/-!
# Full W=133225 count ledger on 262143 identity nodes

This is the arithmetic receipt for the one-exception branch.  It keeps the
existing primary `(M,D,T)=(744,244,122)`, the existing cheap cut
`(J,D,T)=(211,55,27)`, and all nonactive cleanup terms.  The helper flag is
left as an input to the one-incidence exit charge; the explicit near-joint
profile `(k,m)=(1312,11803)` is also evaluated.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityOneExceptionLedgerW1332256900

open RCN095
open Order2ReducedCutScaffold

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000

def n : Nat := 262143
def w : Nat := 133225
def a : Nat := 180413
def v : Nat := 68763
def small : Nat := 1453806
def coreFloor : Nat := 263611557201785349

def primaryFlag : FlagDegree := ⟨500,122,122⟩
def cheapFlag : FlagDegree := ⟨156,28,27⟩
def primaryAgreement : FlagDegree := honestReducedAgreementFlag w 744 244 122
def cheapAgreement : FlagDegree := honestReducedAgreementFlag w 211 55 27

def ceilQuotient (num den : Nat) : Nat := (num+den-1)/den

def cheapRegularCap : Nat :=
  ceilQuotient ((n-v)^2*flagMixed cheapFlag cheapAgreement cheapAgreement)
    ((a-v)^2)

def helperExitCap (helperFlag : FlagDegree) : Nat :=
  ceilQuotient ((n-v)*flagMixed primaryFlag helperFlag primaryAgreement) (a-v)

def firstOrderMixedCost (yCap rCap : Nat) : Nat :=
  (1+2*w*yCap)*rCap+w*(2*rCap-1)*yCap

def firstOrderRegularCap (yCap rCap : Nat) : Nat :=
  ceilQuotient ((n-w)*firstOrderMixedCost yCap rCap) (a-w)

def firstOrderSingularCap (yCap rCap : Nat) : Nat := (2*rCap-1)*yCap

def positiveTAuxY : Nat := (2*122-1)*744
def positiveTAuxR : Nat := (2*122-1)*244
def positiveTCleanupCap : Nat :=
  firstOrderRegularCap positiveTAuxY positiveTAuxR+
    firstOrderSingularCap positiveTAuxY positiveTAuxR
def tFreeRegularCap : Nat := firstOrderRegularCap 744 244
def tFreeSingularCap : Nat := firstOrderSingularCap 744 244

/-- Every list contribution except the helper-exit incidence term. -/
def fixedLedgerCap : Nat := cheapRegularCap+positiveTCleanupCap+
  tFreeRegularCap+tFreeSingularCap

def fullLedgerCap (helperFlag : FlagDegree) : Nat :=
  fixedLedgerCap+helperExitCap helperFlag

/-- The highest-J-upper profile in the exhaustive joint helper audit. -/
def nearJointHelperFlag : FlagDegree := ⟨15983-5248,2624,2624⟩

theorem agreement_flags_exact :
    primaryAgreement=⟨133091776,32640125,32240450⟩ ∧
      cheapAgreement=⟨41432976,7593825,6927700⟩ := by
  norm_num [primaryAgreement,cheapAgreement,honestReducedAgreementFlag,w]

theorem one_exception_Johnson_gate :
    (n-(v+1))*(n-w)<
      (small+1)*((a-(v+1))^2-(n-(v+1))*(w-(v+1))) := by
  norm_num [n,v,w,a,small]

theorem full_fixed_ledger :
    cheapRegularCap=247335521894435962 ∧
    positiveTCleanupCap=15606365842399170 ∧
    tFreeRegularCap=264025132882 ∧
    tFreeSingularCap=362328 ∧
    fixedLedgerCap=262942151762330342 := by
  norm_num [cheapRegularCap,positiveTCleanupCap,tFreeRegularCap,
    tFreeSingularCap,fixedLedgerCap,firstOrderRegularCap,
    firstOrderSingularCap,firstOrderMixedCost,positiveTAuxY,positiveTAuxR,
    ceilQuotient,n,v,w,a,cheapFlag,cheapAgreement,
    honestReducedAgreementFlag,flagMixed]

/-- After paying every other list term, this is the exact remaining allowance
for the helper-exit ceiling. -/
theorem helper_exit_allowance_exact :
    coreFloor-fixedLedgerCap=669405439455007 := by
  rw [full_fixed_ledger.2.2.2.2]
  norm_num [coreFloor]

/-- Equivalently, a helper flag can fit the full ledger only when its mixed
cost is at most this exact integer threshold. -/
theorem helper_mixed_cost_threshold_exact :
    (n-v)*386488350993647≤
        (coreFloor-fixedLedgerCap)*(a-v) ∧
      (coreFloor-fixedLedgerCap)*(a-v)<
        (n-v)*(386488350993647+1) := by
  rw [helper_exit_allowance_exact]
  norm_num [n,v,a]

theorem near_joint_helper_flag_exact :
    nearJointHelperFlag=⟨10735,2624,2624⟩ := by
  norm_num [nearJointHelperFlag]

theorem near_joint_mixed_cost_exact :
    flagMixed primaryFlag nearJointHelperFlag primaryAgreement=
      455069826732134 := by
  norm_num [primaryFlag,nearJointHelperFlag,primaryAgreement,
    honestReducedAgreementFlag,w,flagMixed]

theorem near_joint_full_ledger_exact :
    helperExitCap nearJointHelperFlag=788189906793194 ∧
    fullLedgerCap nearJointHelperFlag=263730341669123536 ∧
    coreFloor<fullLedgerCap nearJointHelperFlag ∧
    fullLedgerCap nearJointHelperFlag-coreFloor=118784467338187 := by
  unfold fullLedgerCap
  rw [full_fixed_ledger.2.2.2.2]
  norm_num [helperExitCap,nearJointHelperFlag,primaryFlag,
    primaryAgreement,honestReducedAgreementFlag,ceilQuotient,n,v,w,a,
    coreFloor,flagMixed]

#print axioms one_exception_Johnson_gate
#print axioms full_fixed_ledger
#print axioms helper_mixed_cost_threshold_exact
#print axioms near_joint_full_ledger_exact

end ProximityPrize.SubmissionLower.WeightedIdentityOneExceptionLedgerW1332256900
