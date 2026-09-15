import WeightedIdentityExtendedLShapeArithmeticW1332266900

/-!
# Coupled terminal/exit aggregation at W=133226

The exited and remaining factors partition one fixed ambient factor family.
Their exact flags therefore share the primary cumulative budget
`(jet,middle,all)=(744,244,122)`.  This module spends that budget once for the
two old L-terminal arms.  The two new skinny terminals have enough slack to
use the simpler independent aggregation proved by the integration module.
-/
namespace ProximityPrize.SubmissionLower.WeightedIdentityExtendedLShapeAggregationW1332266900

open scoped BigOperators
open RCN095
open Order2ReducedCutScaffold
open WeightedIdentityExtendedLShapeArithmeticW1332266900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace A
abbrev n := WeightedIdentityExtendedLShapeArithmeticW1332266900.n
abbrev a := WeightedIdentityExtendedLShapeArithmeticW1332266900.a
abbrev v := WeightedIdentityExtendedLShapeArithmeticW1332266900.v
abbrev primaryFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryFlag
abbrev helperFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag
abbrev primaryAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement
abbrev armAFlag := WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag
abbrev armBFlag := WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag
abbrev armAExitFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armAExitFlag
abbrev armBExitFlag :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armBExitFlag
abbrev armAAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armAAgreement
abbrev armBAgreement :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.armBAgreement
abbrev commonNumerator :=
  WeightedIdentityExtendedLShapeArithmeticW1332266900.commonNumerator
end A

theorem armA_mixed_cumulative (p : FlagDegree) :
    flagMixed p A.armAAgreement A.armAAgreement =
      153210810200032*(p.zOnly+p.yz+p.all)+
      574079073761648*(p.yz+p.all)+686946028530192*p.all := by
  norm_num [A.armAAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armAAgreement,
    honestReducedAgreementFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.w,flagMixed]
  ring

theorem armB_mixed_cumulative (p : FlagDegree) :
    flagMixed p A.armBAgreement A.armBAgreement =
      149518983448224*(p.zOnly+p.yz+p.all)+
      581462727265264*(p.yz+p.all)+668699884243160*p.all := by
  norm_num [A.armBAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armBAgreement,
    honestReducedAgreementFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.w,flagMixed]
  ring

theorem helper_mixed_cumulative (p : FlagDegree) :
    flagMixed p A.helperFlag A.primaryAgreement =
      254847482496*(p.zOnly+p.yz+p.all)+
      695661677140*(p.yz+p.all)+785604548130*p.all := by
  norm_num [A.helperFlag,A.primaryAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
    honestReducedAgreementFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.w,flagMixed]
  ring

theorem sum_armA_mixed_cumulative {R : Type*} [Fintype R]
    (f : R→FlagDegree) :
    (∑ i,flagMixed (f i) A.armAAgreement A.armAAgreement)=
      153210810200032*(∑ i,((f i).zOnly+(f i).yz+(f i).all))+
      574079073761648*(∑ i,((f i).yz+(f i).all))+
      686946028530192*(∑ i,(f i).all) := by
  rw [Finset.sum_congr rfl (fun i _ => armA_mixed_cumulative (f i))]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem sum_armB_mixed_cumulative {R : Type*} [Fintype R]
    (f : R→FlagDegree) :
    (∑ i,flagMixed (f i) A.armBAgreement A.armBAgreement)=
      149518983448224*(∑ i,((f i).zOnly+(f i).yz+(f i).all))+
      581462727265264*(∑ i,((f i).yz+(f i).all))+
      668699884243160*(∑ i,(f i).all) := by
  rw [Finset.sum_congr rfl (fun i _ => armB_mixed_cumulative (f i))]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem sum_helper_mixed_cumulative {E : Type*} [Fintype E]
    (f : E→FlagDegree) :
    (∑ i,flagMixed (f i) A.helperFlag A.primaryAgreement)=
      254847482496*(∑ i,((f i).zOnly+(f i).yz+(f i).all))+
      695661677140*(∑ i,((f i).yz+(f i).all))+
      785604548130*(∑ i,(f i).all) := by
  rw [Finset.sum_congr rfl (fun i _ => helper_mixed_cumulative (f i))]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem coupled_armA_cost_le
    (eJ eM eS rJ rM rS : Nat)
    (hJ : eJ+rJ≤744) (hM : eM+rM≤244) (hS : eS+rS≤122)
    (hrJ : rJ≤211) (hrM : rM≤55) (hrS : rS≤27) :
    (A.n-A.v)*(A.a-A.v)*
        (254847482496*eJ+695661677140*eM+785604548130*eS)+
      (A.n-A.v)^2*
        (153210810200032*rJ+574079073761648*rM+686946028530192*rS)≤
      A.commonNumerator A.armAFlag A.armAExitFlag A.armAAgreement := by
  norm_num [A.n,A.a,A.v,A.commonNumerator,A.armAFlag,A.armAExitFlag,
    A.armAAgreement,A.helperFlag,A.primaryAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.commonNumerator,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armAFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armAExitFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armAAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
    honestReducedAgreementFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.w,flagMixed]
  omega

theorem coupled_armB_cost_le
    (eJ eM eS rJ rM rS : Nat)
    (hJ : eJ+rJ≤744) (hM : eM+rM≤244) (hS : eS+rS≤122)
    (hrJ : rJ≤212) (hrM : rM≤54) (hrS : rS≤27) :
    (A.n-A.v)*(A.a-A.v)*
        (254847482496*eJ+695661677140*eM+785604548130*eS)+
      (A.n-A.v)^2*
        (149518983448224*rJ+581462727265264*rM+668699884243160*rS)≤
      A.commonNumerator A.armBFlag A.armBExitFlag A.armBAgreement := by
  norm_num [A.n,A.a,A.v,A.commonNumerator,A.armBFlag,A.armBExitFlag,
    A.armBAgreement,A.helperFlag,A.primaryAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.n,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.a,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.v,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.commonNumerator,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armBFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armBExitFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.armBAgreement,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.helperFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.primaryAgreement,
    honestReducedAgreementFlag,
    WeightedIdentityExtendedLShapeArithmeticW1332266900.w,flagMixed]
  omega

theorem coupled_armA_mixed_sums_le
    {E R : Type*} [Fintype E] [Fintype R]
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (hJ : (∑ i,((exitFlag i).zOnly+(exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤744)
    (hM : (∑ i,((exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).yz+(restFlag i).all))≤244)
    (hS : (∑ i,(exitFlag i).all)+(∑ i,(restFlag i).all)≤122)
    (hrJ : (∑ i,((restFlag i).zOnly+(restFlag i).yz+
      (restFlag i).all))≤211)
    (hrM : (∑ i,((restFlag i).yz+(restFlag i).all))≤55)
    (hrS : (∑ i,(restFlag i).all)≤27) :
    (A.n-A.v)*(A.a-A.v)*
        (∑ i,flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)+
      (A.n-A.v)^2*
        (∑ i,flagMixed (restFlag i) A.armAAgreement A.armAAgreement)≤
      A.commonNumerator A.armAFlag A.armAExitFlag A.armAAgreement := by
  rw [sum_helper_mixed_cumulative,sum_armA_mixed_cumulative]
  exact coupled_armA_cost_le _ _ _ _ _ _ hJ hM hS hrJ hrM hrS

theorem coupled_armB_mixed_sums_le
    {E R : Type*} [Fintype E] [Fintype R]
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (hJ : (∑ i,((exitFlag i).zOnly+(exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤744)
    (hM : (∑ i,((exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).yz+(restFlag i).all))≤244)
    (hS : (∑ i,(exitFlag i).all)+(∑ i,(restFlag i).all)≤122)
    (hrJ : (∑ i,((restFlag i).zOnly+(restFlag i).yz+
      (restFlag i).all))≤212)
    (hrM : (∑ i,((restFlag i).yz+(restFlag i).all))≤54)
    (hrS : (∑ i,(restFlag i).all)≤27) :
    (A.n-A.v)*(A.a-A.v)*
        (∑ i,flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)+
      (A.n-A.v)^2*
        (∑ i,flagMixed (restFlag i) A.armBAgreement A.armBAgreement)≤
      A.commonNumerator A.armBFlag A.armBExitFlag A.armBAgreement := by
  rw [sum_helper_mixed_cumulative,sum_armB_mixed_cumulative]
  exact coupled_armB_cost_le _ _ _ _ _ _ hJ hM hS hrJ hrM hrS

/-- Count-facing wrapper shared by both old terminal arms. -/
theorem coupled_counts_scaled
    {E R : Type*} [Fintype E] [Fintype R]
    (exitCount : E→Nat) (restCount : R→Nat)
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (restAgreement : FlagDegree) (bound : Nat)
    (hexit : ∀ i,exitCount i*(A.a-A.v)≤
      (A.n-A.v)*flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)
    (hrest : ∀ i,restCount i*(A.a-A.v)^2≤
      (A.n-A.v)^2*flagMixed (restFlag i) restAgreement restAgreement)
    (hmixed :
      (A.n-A.v)*(A.a-A.v)*
          (∑ i,flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)+
        (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
          restAgreement restAgreement)≤bound) :
    ((∑ i,exitCount i)+(∑ i,restCount i))*(A.a-A.v)^2≤bound := by
  have he : (∑ i,exitCount i)*(A.a-A.v)≤
      (A.n-A.v)*(∑ i,flagMixed (exitFlag i)
        A.helperFlag A.primaryAgreement) := by
    calc
      _ = ∑ i,exitCount i*(A.a-A.v) := Finset.sum_mul ..
      _ ≤ ∑ i,(A.n-A.v)*flagMixed (exitFlag i)
          A.helperFlag A.primaryAgreement :=
        Finset.sum_le_sum (fun i _ => hexit i)
      _ = _ := (Finset.mul_sum ..).symm
  have hr : (∑ i,restCount i)*(A.a-A.v)^2≤
      (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
        restAgreement restAgreement) := by
    calc
      _ = ∑ i,restCount i*(A.a-A.v)^2 := Finset.sum_mul ..
      _ ≤ ∑ i,(A.n-A.v)^2*flagMixed (restFlag i)
          restAgreement restAgreement :=
        Finset.sum_le_sum (fun i _ => hrest i)
      _ = _ := (Finset.mul_sum ..).symm
  calc
    ((∑ i,exitCount i)+(∑ i,restCount i))*(A.a-A.v)^2 =
        ((∑ i,exitCount i)*(A.a-A.v))*(A.a-A.v)+
          (∑ i,restCount i)*(A.a-A.v)^2 := by ring
    _ ≤ ((A.n-A.v)*(∑ i,flagMixed (exitFlag i)
          A.helperFlag A.primaryAgreement))*(A.a-A.v)+
        (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
          restAgreement restAgreement) :=
      Nat.add_le_add (Nat.mul_le_mul_right (A.a-A.v) he) hr
    _ = (A.n-A.v)*(A.a-A.v)*
          (∑ i,flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)+
        (A.n-A.v)^2*(∑ i,flagMixed (restFlag i)
          restAgreement restAgreement) := by ring
    _ ≤ _ := hmixed

theorem coupled_armA_counts_scaled
    {E R : Type*} [Fintype E] [Fintype R]
    (exitCount : E→Nat) (restCount : R→Nat)
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (hexit : ∀ i,exitCount i*(A.a-A.v)≤
      (A.n-A.v)*flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)
    (hrest : ∀ i,restCount i*(A.a-A.v)^2≤
      (A.n-A.v)^2*flagMixed (restFlag i) A.armAAgreement A.armAAgreement)
    (hJ : (∑ i,((exitFlag i).zOnly+(exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤744)
    (hM : (∑ i,((exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).yz+(restFlag i).all))≤244)
    (hS : (∑ i,(exitFlag i).all)+(∑ i,(restFlag i).all)≤122)
    (hrJ : (∑ i,((restFlag i).zOnly+(restFlag i).yz+
      (restFlag i).all))≤211)
    (hrM : (∑ i,((restFlag i).yz+(restFlag i).all))≤55)
    (hrS : (∑ i,(restFlag i).all)≤27) :
    ((∑ i,exitCount i)+(∑ i,restCount i))*(A.a-A.v)^2≤
      A.commonNumerator A.armAFlag A.armAExitFlag A.armAAgreement := by
  exact coupled_counts_scaled exitCount restCount exitFlag restFlag
    A.armAAgreement _ hexit hrest
    (coupled_armA_mixed_sums_le exitFlag restFlag hJ hM hS hrJ hrM hrS)

theorem coupled_armB_counts_scaled
    {E R : Type*} [Fintype E] [Fintype R]
    (exitCount : E→Nat) (restCount : R→Nat)
    (exitFlag : E→FlagDegree) (restFlag : R→FlagDegree)
    (hexit : ∀ i,exitCount i*(A.a-A.v)≤
      (A.n-A.v)*flagMixed (exitFlag i) A.helperFlag A.primaryAgreement)
    (hrest : ∀ i,restCount i*(A.a-A.v)^2≤
      (A.n-A.v)^2*flagMixed (restFlag i) A.armBAgreement A.armBAgreement)
    (hJ : (∑ i,((exitFlag i).zOnly+(exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).zOnly+(restFlag i).yz+(restFlag i).all))≤744)
    (hM : (∑ i,((exitFlag i).yz+(exitFlag i).all))+
        (∑ i,((restFlag i).yz+(restFlag i).all))≤244)
    (hS : (∑ i,(exitFlag i).all)+(∑ i,(restFlag i).all)≤122)
    (hrJ : (∑ i,((restFlag i).zOnly+(restFlag i).yz+
      (restFlag i).all))≤212)
    (hrM : (∑ i,((restFlag i).yz+(restFlag i).all))≤54)
    (hrS : (∑ i,(restFlag i).all)≤27) :
    ((∑ i,exitCount i)+(∑ i,restCount i))*(A.a-A.v)^2≤
      A.commonNumerator A.armBFlag A.armBExitFlag A.armBAgreement := by
  exact coupled_counts_scaled exitCount restCount exitFlag restFlag
    A.armBAgreement _ hexit hrest
    (coupled_armB_mixed_sums_le exitFlag restFlag hJ hM hS hrJ hrM hrS)

#print axioms coupled_armA_cost_le
#print axioms coupled_armB_cost_le
#print axioms coupled_armA_counts_scaled
#print axioms coupled_armB_counts_scaled

end ProximityPrize.SubmissionLower.WeightedIdentityExtendedLShapeAggregationW1332266900
