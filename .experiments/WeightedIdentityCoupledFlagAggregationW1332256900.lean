import RootWeightedIdentityCoupledBudgetArithmeticW1332256900

/-!
# Coupled terminal/exit flag aggregation at W=133225

The helper-exited factors and the terminal remainder partition one fixed
factor set.  Consequently their three *nested* exact-flag sums share the
minimum-primary budget `(jet,middle,all)=(740,244,122)`.  This file proves the
finite-family inequality which spends that budget once.

The theorem is deliberately phrased in terms of the per-factor incidence
inequalities.  It can therefore consume a single helper profile for every
exit and either terminal arm without knowing how the strict descent selected
the factors.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityCoupledFlagAggregationW1332256900

open scoped BigOperators
open RCN095

namespace A
abbrev n := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n
abbrev a := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a
abbrev v := RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v
abbrev armAFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag
abbrev armAExitFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag
abbrev armAAgreement :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement
abbrev jointHelperFlag :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag
abbrev primaryAgreement :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement
abbrev jointCommonNumerator :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator
abbrev jointCommonCap :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonCap
abbrev ceilQuotient :=
  RootWeightedIdentityCoupledBudgetArithmeticW1332256900.ceilQuotient
end A

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

/-- Exact cumulative-basis expansion of the arm-A two-incidence cost. -/
theorem armA_mixed_cumulative (p : FlagDegree) :
    flagMixed p A.armAAgreement A.armAAgreement =
      153208510195000*(p.zOnly+p.yz+p.all)+
      574070455670400*(p.yz+p.all)+686935716077025*p.all := by
  norm_num [A.armAAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement,
    flagMixed]
  ring

/-- Exact cumulative-basis expansion of the unified cutoff-two helper cost. -/
theorem joint_exit_mixed_cumulative (p : FlagDegree) :
    flagMixed p A.jointHelperFlag A.primaryAgreement =
      254845569600*(p.zOnly+p.yz+p.all)+
      692859796274*(p.yz+p.all)+782801992149*p.all := by
  norm_num [A.jointHelperFlag,A.primaryAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement,
    flagMixed]
  ring

theorem sum_armA_mixed_cumulative {R : Type*} [Fintype R]
    (f : R→FlagDegree) :
    (∑ i,flagMixed (f i) A.armAAgreement A.armAAgreement)=
      153208510195000*(∑ i,((f i).zOnly+(f i).yz+(f i).all))+
      574070455670400*(∑ i,((f i).yz+(f i).all))+
      686935716077025*(∑ i,(f i).all) := by
  rw [Finset.sum_congr rfl (fun i _ => armA_mixed_cumulative (f i))]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem sum_joint_exit_mixed_cumulative {E : Type*} [Fintype E]
    (f : E→FlagDegree) :
    (∑ i,flagMixed (f i) A.jointHelperFlag A.primaryAgreement)=
      254845569600*(∑ i,((f i).zOnly+(f i).yz+(f i).all))+
      692859796274*(∑ i,((f i).yz+(f i).all))+
      782801992149*(∑ i,(f i).all) := by
  rw [Finset.sum_congr rfl (fun i _ => joint_exit_mixed_cumulative (f i))]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]

/-- Load-bearing six-variable LP.  The first three constraints are the one
shared primary budget; the last three say that the terminal remainder lies
in arm A.  Because every scaled arm-A marginal cost dominates the matching
helper-exit marginal cost, the maximum occurs at the full arm-A endpoint. -/
theorem coupled_armA_cost_le
    (eJ eM eS rJ rM rS : Nat)
    (hJ : eJ+rJ≤740) (hM : eM+rM≤244) (hS : eS+rS≤122)
    (hrJ : rJ≤211) (hrM : rM≤55) (hrS : rS≤27) :
    (A.n-A.v)*(A.a-A.v)*
        (254845569600*eJ+692859796274*eM+782801992149*eS)+
      (A.n-A.v)^2*
        (153208510195000*rJ+574070455670400*rM+686935716077025*rS)≤
      A.jointCommonNumerator A.armAFlag A.armAExitFlag A.armAAgreement := by
  norm_num [A.n,A.a,A.v,A.jointCommonNumerator,A.armAFlag,A.armAExitFlag,
    A.armAAgreement,A.jointHelperFlag,A.primaryAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement,
    flagMixed]
  omega

/-- The coupled mixed-cost inequality for two arbitrary finite families. -/
theorem coupled_armA_mixed_sums_le
    {E R : Type*} [Fintype E] [Fintype R]
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (hJ : (∑ i,((exitFlag i).zOnly+(exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤740)
    (hM : (∑ i,((exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).yz+(restFlag i).all))≤244)
    (hS : (∑ i,(exitFlag i).all)+(∑ i,(restFlag i).all)≤122)
    (hrJ : (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤211)
    (hrM : (∑ i,((restFlag i).yz+(restFlag i).all))≤55)
    (hrS : (∑ i,(restFlag i).all)≤27) :
    (A.n-A.v)*(A.a-A.v)*
        (∑ i,flagMixed (exitFlag i) A.jointHelperFlag A.primaryAgreement)+
      (A.n-A.v)^2*
        (∑ i,flagMixed (restFlag i) A.armAAgreement A.armAAgreement)≤
      A.jointCommonNumerator A.armAFlag A.armAExitFlag A.armAAgreement := by
  rw [sum_joint_exit_mixed_cumulative,sum_armA_mixed_cumulative]
  exact coupled_armA_cost_le _ _ _ _ _ _ hJ hM hS hrJ hrM hrS

/-- Direct count-facing form.  `exitCount` is charged by one incidence and
`restCount` by two incidences; the common denominator is introduced only
after the two groups have been coupled. -/
theorem coupled_armA_counts_scaled
    {E R : Type*} [Fintype E] [Fintype R]
    (exitCount : E→Nat) (restCount : R→Nat)
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (hexit : ∀ i,exitCount i*(A.a-A.v)≤
      (A.n-A.v)*flagMixed (exitFlag i) A.jointHelperFlag A.primaryAgreement)
    (hrest : ∀ i,restCount i*(A.a-A.v)^2≤
      (A.n-A.v)^2*flagMixed (restFlag i) A.armAAgreement A.armAAgreement)
    (hJ : (∑ i,((exitFlag i).zOnly+(exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤740)
    (hM : (∑ i,((exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).yz+(restFlag i).all))≤244)
    (hS : (∑ i,(exitFlag i).all)+(∑ i,(restFlag i).all)≤122)
    (hrJ : (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤211)
    (hrM : (∑ i,((restFlag i).yz+(restFlag i).all))≤55)
    (hrS : (∑ i,(restFlag i).all)≤27) :
    ((∑ i,exitCount i)+(∑ i,restCount i))*(A.a-A.v)^2≤
      A.jointCommonNumerator A.armAFlag A.armAExitFlag A.armAAgreement := by
  have he : (∑ i,exitCount i)*(A.a-A.v)≤
      (A.n-A.v)*(∑ i,flagMixed (exitFlag i)
        A.jointHelperFlag A.primaryAgreement) := by
    calc
      _ = ∑ i,exitCount i*(A.a-A.v) := Finset.sum_mul ..
      _ ≤ ∑ i,(A.n-A.v)*flagMixed (exitFlag i)
          A.jointHelperFlag A.primaryAgreement :=
        Finset.sum_le_sum (fun i _ => hexit i)
      _ = _ := (Finset.mul_sum ..).symm
  have hr : (∑ i,restCount i)*(A.a-A.v)^2≤
      (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
        A.armAAgreement A.armAAgreement) := by
    calc
      _ = ∑ i,restCount i*(A.a-A.v)^2 := Finset.sum_mul ..
      _ ≤ ∑ i,(A.n-A.v)^2*flagMixed (restFlag i)
          A.armAAgreement A.armAAgreement :=
        Finset.sum_le_sum (fun i _ => hrest i)
      _ = _ := (Finset.mul_sum ..).symm
  calc
    ((∑ i,exitCount i)+(∑ i,restCount i))*(A.a-A.v)^2 =
        ((∑ i,exitCount i)*(A.a-A.v))*(A.a-A.v)+
          (∑ i,restCount i)*(A.a-A.v)^2 := by ring
    _ ≤ ((A.n-A.v)*(∑ i,flagMixed (exitFlag i)
          A.jointHelperFlag A.primaryAgreement))*(A.a-A.v)+
        (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
          A.armAAgreement A.armAAgreement) :=
      Nat.add_le_add (Nat.mul_le_mul_right (A.a-A.v) he) hr
    _ = (A.n-A.v)*(A.a-A.v)*
          (∑ i,flagMixed (exitFlag i) A.jointHelperFlag A.primaryAgreement)+
        (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
          A.armAAgreement A.armAAgreement) := by ring
    _ ≤ _ := coupled_armA_mixed_sums_le exitFlag restFlag hJ hM hS
      hrJ hrM hrS

/-- Exact endpoint consequence, retaining the common-denominator statement
needed by the final count ledger. -/
theorem coupled_armA_counts_le_cap
    (exitCount restCount : Nat)
    (hscaled : (exitCount+restCount)*(A.a-A.v)^2≤
      A.jointCommonNumerator A.armAFlag A.armAExitFlag A.armAAgreement) :
    exitCount+restCount≤247924633751427236 := by
  apply ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332246900.count_le_of_scaled
    _ _ _ _ (by
      norm_num [A.a,A.v,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
        RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v]) hscaled
  norm_num [A.jointCommonNumerator,A.armAFlag,A.armAExitFlag,A.armAAgreement,
    A.jointHelperFlag,A.primaryAgreement,A.a,A.v,A.n,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointCommonNumerator,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAExitFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.armAAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.jointHelperFlag,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.primaryAgreement,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.a,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.v,
    RootWeightedIdentityCoupledBudgetArithmeticW1332256900.n,flagMixed]

end ProximityPrize.SubmissionLower.WeightedIdentityCoupledFlagAggregationW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledFlagAggregationW1332256900.coupled_armA_cost_le
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledFlagAggregationW1332256900.coupled_armA_counts_scaled
#print axioms ProximityPrize.SubmissionLower.WeightedIdentityCoupledFlagAggregationW1332256900.coupled_armA_counts_le_cap
