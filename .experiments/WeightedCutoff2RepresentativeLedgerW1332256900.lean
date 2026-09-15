import Order2HereditaryActiveSurface6900
import Order2ReducedCutScaffold

/-! Exact representative-count ledger for the cutoff-two `W=133225` profile. -/
namespace ProximityPrize.SubmissionLower.WeightedCutoff2RepresentativeLedgerW1332256900

open RCN095 RCN084
open Order2ReducedCutScaffold
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000

def n : Nat := 262142
def w : Nat := 133225
def a : Nat := 180413
def v : Nat := 68759
def small : Nat := 1453806
def prime : Nat := 2130706433
def retained : Nat := 263611557201523206

def primaryFlag : FlagDegree := ⟨739-244,244-122,122⟩
def helperFlag : FlagDegree := ⟨15993-5248,5248-2624,2624⟩
def cheapFlag : FlagDegree := ⟨211-55,55-27,27⟩
def primaryAgreement : FlagDegree := honestReducedAgreementFlag w 739 244 122
def cheapAgreement : FlagDegree := honestReducedAgreementFlag w 211 55 27

def twoIncidenceNumerator (p q : FlagDegree) : Nat := (n-v)^2*flagMixed p q q
def oneIncidenceNumerator (p q r : FlagDegree) : Nat := (n-v)*flagMixed p q r
def ceilQuotient (num den : Nat) : Nat := (num+den-1)/den

def cheapRegularCap : Nat := ceilQuotient (twoIncidenceNumerator cheapFlag cheapAgreement) ((a-v)^2)
def exitedHelperCap : Nat := ceilQuotient
  (oneIncidenceNumerator primaryFlag helperFlag primaryAgreement) (a-v)

def firstOrderAgreementCap (W yCap rCap : Nat) : Fin 3 → Nat :=
  ![1+2*W*yCap,W*(2*rCap-1),1]
def firstOrderMixedCost (W yCap rCap : Nat) : Nat :=
  (1+2*W*yCap)*rCap+W*(2*rCap-1)*yCap
def firstOrderRegularNumerator (yCap rCap : Nat) : Nat := (n-w)*firstOrderMixedCost w yCap rCap
def firstOrderRegularCap (yCap rCap : Nat) : Nat := ceilQuotient (firstOrderRegularNumerator yCap rCap) (a-w)
def firstOrderSingularCap (yCap rCap : Nat) : Nat := (2*rCap-1)*yCap
def positiveTAuxY : Nat := (2*122-1)*739
def positiveTAuxR : Nat := (2*122-1)*244
def positiveTSingularCap : Nat := firstOrderRegularCap positiveTAuxY positiveTAuxR+
  firstOrderSingularCap positiveTAuxY positiveTAuxR
def tFreeRegularCap : Nat := firstOrderRegularCap 739 244
def tFreeSingularCap : Nat := firstOrderSingularCap 739 244
def yOnlyCap : Nat := 739
def completeCap : Nat := cheapRegularCap+exitedHelperCap+positiveTSingularCap+
  tFreeRegularCap+tFreeSingularCap+yOnlyCap

theorem actual_flags :
    primaryFlag=⟨495,122,122⟩ ∧ helperFlag=⟨10745,2624,2624⟩ ∧
    cheapFlag=⟨156,28,27⟩ ∧ primaryAgreement=⟨131759526,32640125,32240450⟩ ∧
    cheapAgreement=⟨41432976,7593825,6927700⟩ := by
  norm_num [primaryFlag,helperFlag,cheapFlag,primaryAgreement,cheapAgreement,
    honestReducedAgreementFlag,w]

theorem mixed_costs_exact :
    flagMixed cheapFlag cheapAgreement cheapAgreement=82448135047096675 ∧
    flagMixed primaryFlag helperFlag primaryAgreement=452634614950634 := by
  norm_num [flagMixed,primaryFlag,helperFlag,cheapFlag,primaryAgreement,cheapAgreement,
    honestReducedAgreementFlag,w]

theorem incidence_numerators_exact :
    twoIncidenceNumerator cheapFlag cheapAgreement=3083311643992878648877809075 ∧
    oneIncidenceNumerator primaryFlag helperFlag primaryAgreement=87531839742998454822 := by
  rw [twoIncidenceNumerator,oneIncidenceNumerator,mixed_costs_exact.1,mixed_costs_exact.2]
  norm_num [n,v]

theorem active_caps_exact : cheapRegularCap=247325474229198472 ∧
    exitedHelperCap=783956147948112 := by
  unfold cheapRegularCap exitedHelperCap
  rw [incidence_numerators_exact.1,incidence_numerators_exact.2]
  norm_num [ceilQuotient,a,v]

theorem active_scaled_caps :
    twoIncidenceNumerator cheapFlag cheapAgreement≤cheapRegularCap*(a-v)^2 ∧
    oneIncidenceNumerator primaryFlag helperFlag primaryAgreement≤exitedHelperCap*(a-v) := by
  rw [incidence_numerators_exact.1,incidence_numerators_exact.2,
    active_caps_exact.1,active_caps_exact.2]
  norm_num [a,v]

theorem source_and_projection_gates :
    cheapFlag.zOnly+cheapFlag.yz+cheapFlag.all<prime ∧
    primaryFlag.zOnly+primaryFlag.yz+primaryFlag.all<prime ∧
    helperFlag.zOnly+helperFlag.yz+helperFlag.all<prime ∧ w<prime ∧ 2<prime ∧
    (cheapAgreement.yz+cheapAgreement.all)*cheapFlag.all+
      (cheapFlag.yz+cheapFlag.all)*cheapAgreement.all=773104675 ∧
    773104675<prime ∧
    (helperFlag.yz+helperFlag.all)*primaryFlag.all+
      (primaryFlag.yz+primaryFlag.all)*helperFlag.all=1280512 ∧ 1280512<prime := by
  norm_num [cheapFlag,primaryFlag,helperFlag,cheapAgreement,honestReducedAgreementFlag,w,prime]

theorem small_absorption_margins :
    (n-v)*cheapAgreement.all-small*(a-v)=1177376153976 ∧
    (n-v)^2*cheapAgreement.all^2-small*(a-v)^2=1794794488618848435194904 ∧
    (n-v)*primaryAgreement.all-small*(a-v)=6072431687226 := by
  norm_num [n,v,small,a,cheapAgreement,primaryAgreement,honestReducedAgreementFlag,w]

theorem small_absorption_gates :
    small*(a-v)≤(n-v)*cheapAgreement.all ∧
    small*(a-v)^2≤(n-v)^2*cheapAgreement.all^2 ∧
    small*(a-v)≤(n-v)*primaryAgreement.all := by
  norm_num [n,v,small,a,cheapAgreement,primaryAgreement,honestReducedAgreementFlag,w]

theorem shortened_Johnson_gate :
    (n-(v+1))*(n-w)<(small+1)*((a-(v+1))^2-(n-(v+1))*(w-(v+1))) ∧
    v+1≤w ∧ w<a ∧ a≤n := by norm_num [n,v,w,small,a]

theorem seedless_coordinate_cost_eq {Omega : Type} [Field Omega]
    (G : MvPolynomial (Fin 3) Omega) (W yCap rCap : Nat) :
    (∑ i : Fin 3, firstOrderAgreementCap W yCap rCap i*
      RCN001.coordinateMixedDegree Omega G
        (RCN283.seedlessCut : MvPolynomial (Fin 3) Omega) i) =
      (1+2*W*yCap)*G.degreeOf 1+W*(2*rCap-1)*G.degreeOf 0 := by
  have hx0 : (RCN283.seedlessCut : MvPolynomial (Fin 3) Omega).degreeOf 0=0 := by
    simp [RCN283.seedlessCut,MvPolynomial.degreeOf_X_of_ne]
  have hx1 : (RCN283.seedlessCut : MvPolynomial (Fin 3) Omega).degreeOf 1=0 := by
    simp [RCN283.seedlessCut,MvPolynomial.degreeOf_X_of_ne]
  have hx2 : (RCN283.seedlessCut : MvPolynomial (Fin 3) Omega).degreeOf 2=1 := by
    simp [RCN283.seedlessCut]
  simp [Fin.sum_univ_succ,firstOrderAgreementCap,
    RCN001.coordinateMixedDegree_zero,RCN001.coordinateMixedDegree_one,
    RCN001.coordinateMixedDegree_two,hx0,hx1,hx2]

theorem firstOrder_cost_le_of_coordinate_caps {Omega : Type} [Field Omega]
    (G : MvPolynomial (Fin 3) Omega) (W yCap rCap : Nat)
    (hY : G.degreeOf 0≤yCap) (hR : G.degreeOf 1≤rCap) :
    (∑ i : Fin 3, firstOrderAgreementCap W yCap rCap i*
      RCN001.coordinateMixedDegree Omega G
        (RCN283.seedlessCut : MvPolynomial (Fin 3) Omega) i)≤firstOrderMixedCost W yCap rCap := by
  rw [seedless_coordinate_cost_eq]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hR) (Nat.mul_le_mul_left _ hY)

theorem cleanup_caps_exact :
    positiveTAuxY=179577 ∧ positiveTAuxR=59292 ∧
    firstOrderRegularCap positiveTAuxY positiveTAuxR=15501342813930828 ∧
    firstOrderSingularCap positiveTAuxY positiveTAuxR=21294779391 ∧
    positiveTSingularCap=15501364108710219 ∧
    tFreeRegularCap=262248736190 ∧ tFreeSingularCap=359893 ∧ yOnlyCap=739 := by
  norm_num [positiveTAuxY,positiveTAuxR,firstOrderRegularCap,firstOrderRegularNumerator,
    firstOrderMixedCost,ceilQuotient,firstOrderSingularCap,positiveTSingularCap,
    tFreeRegularCap,tFreeSingularCap,yOnlyCap,n,w,a]

theorem cleanup_scaled_caps :
    firstOrderRegularNumerator positiveTAuxY positiveTAuxR≤
      firstOrderRegularCap positiveTAuxY positiveTAuxR*(a-w) ∧
    firstOrderRegularNumerator 739 244≤tFreeRegularCap*(a-w) := by
  norm_num [positiveTAuxY,positiveTAuxR,firstOrderRegularNumerator,firstOrderMixedCost,
    firstOrderRegularCap,tFreeRegularCap,ceilQuotient,n,w,a]

theorem cleanup_characteristic_gates :
    122<prime ∧ 244<prime ∧ 739<prime ∧ positiveTAuxY<prime ∧ positiveTAuxR<prime := by
  norm_num [positiveTAuxY,positiveTAuxR,prime]

theorem complete_cap_exact : completeCap=263611056734953625 := by
  unfold completeCap
  rw [active_caps_exact.1,active_caps_exact.2,cleanup_caps_exact.2.2.2.2.1,
    cleanup_caps_exact.2.2.2.2.2.1,cleanup_caps_exact.2.2.2.2.2.2.1,
    cleanup_caps_exact.2.2.2.2.2.2.2]

theorem complete_cap_lt_retained : completeCap<retained := by
  rw [complete_cap_exact]
  norm_num [retained]

theorem complete_headroom : retained-completeCap=500466569581 := by
  rw [complete_cap_exact]
  norm_num [retained]

theorem aggregate_scaled_flags {I : Type*} [Fintype I]
    (counts : I → Nat) (flags : I → FlagDegree) (p q r : FlagDegree)
    (scale numeratorScale : Nat)
    (hper : ∀ i, counts i*scale≤numeratorScale*flagMixed (flags i) q r)
    (hs : (∑ i,(flags i).all)≤p.all)
    (hm : (∑ i,((flags i).yz+(flags i).all))≤p.yz+p.all)
    (ht : (∑ i,((flags i).zOnly+(flags i).yz+(flags i).all))≤p.zOnly+p.yz+p.all) :
    (∑ i,counts i)*scale≤numeratorScale*flagMixed p q r := by
  calc
    _ = ∑ i, counts i*scale := Finset.sum_mul ..
    _ ≤ ∑ i, numeratorScale*flagMixed (flags i) q r :=
      Finset.sum_le_sum fun i hi => hper i
    _ = numeratorScale*(∑ i,flagMixed (flags i) q r) := (Finset.mul_sum ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_flagMixed_le_of_cumulative flags p q r hs hm ht)

theorem count_le_of_scaled (count den num cap : Nat) (hden : 0<den)
    (hcount : count*den≤num) (hcap : num≤cap*den) : count≤cap := by
  have h := hcount.trans hcap
  nlinarith

theorem complete_ledger_of_branch_bounds (total cheap exited positiveT tRegular tSingular yOnly : Nat)
    (hcover : total≤cheap+exited+positiveT+tRegular+tSingular+yOnly)
    (hcheap : cheap*(a-v)^2≤twoIncidenceNumerator cheapFlag cheapAgreement)
    (hexited : exited*(a-v)≤oneIncidenceNumerator primaryFlag helperFlag primaryAgreement)
    (hpositive : positiveT≤positiveTSingularCap)
    (htRegular : tRegular*(a-w)≤firstOrderRegularNumerator 739 244)
    (htSingular : tSingular≤tFreeSingularCap) (hyOnly : yOnly≤yOnlyCap) :
    total<retained := by
  have hc := count_le_of_scaled cheap _ _ cheapRegularCap (by norm_num [a,v])
    hcheap active_scaled_caps.1
  have he := count_le_of_scaled exited _ _ exitedHelperCap (by norm_num [a,v])
    hexited active_scaled_caps.2
  have hr := count_le_of_scaled tRegular _ _ tFreeRegularCap (by norm_num [a,w])
    htRegular cleanup_scaled_caps.2
  have htotal : total≤completeCap := by unfold completeCap; omega
  exact htotal.trans_lt complete_cap_lt_retained

end ProximityPrize.SubmissionLower.WeightedCutoff2RepresentativeLedgerW1332256900

#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2RepresentativeLedgerW1332256900.complete_cap_lt_retained
#print axioms ProximityPrize.SubmissionLower.WeightedCutoff2RepresentativeLedgerW1332256900.complete_ledger_of_branch_bounds
