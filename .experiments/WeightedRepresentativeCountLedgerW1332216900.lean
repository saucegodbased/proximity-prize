import Order2HereditaryActiveSurface6900
import Order2ReducedCutScaffold

/-! W=133221 complete representative count arithmetic using the actual flagMixed and
honest reduced-agreement flag definitions. Factor-family and cleanup semantic
bounds remain explicit inputs to the aggregation adapter. -/

namespace ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900

open RCN095 RCN084
open Order2ReducedCutScaffold
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000

def n : Nat := 262144
def w : Nat := 133221
def a : Nat := 180413
def v : Nat := 68740
def small : Nat := 2458014
def prime : Nat := 2130706433
def retained : Nat := 253511670984674103

def primaryFlag : FlagDegree := ⟨721-236,236-118,118⟩
def helperFlag : FlagDegree := ⟨15259-5008,5008-2504,2504⟩
def cheapFlag : FlagDegree := ⟨207-54,54-27,27⟩
def primaryAgreement : FlagDegree := honestReducedAgreementFlag w 721 236 118
def cheapAgreement : FlagDegree := honestReducedAgreementFlag w 207 54 27

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
def positiveTAuxY : Nat := (2*118-1)*721
def positiveTAuxR : Nat := (2*118-1)*236
def positiveTSingularCap : Nat := firstOrderRegularCap positiveTAuxY positiveTAuxR+
  firstOrderSingularCap positiveTAuxY positiveTAuxR
def tFreeRegularCap : Nat := firstOrderRegularCap 721 236
def tFreeSingularCap : Nat := firstOrderSingularCap 721 236
def yOnlyCap : Nat := 721
def completeCap : Nat := cheapRegularCap+exitedHelperCap+positiveTSingularCap+
  tFreeRegularCap+tFreeSingularCap+yOnlyCap

theorem actual_flags :
    primaryFlag=⟨485,118,118⟩ ∧ helperFlag=⟨10251,2504,2504⟩ ∧
    cheapFlag=⟨153,27,27⟩ ∧ primaryAgreement=⟨129091150,31573377,31173714⟩ ∧
    cheapAgreement=⟨40632406,7327155,6927492⟩ := by
  norm_num [primaryFlag,helperFlag,cheapFlag,primaryAgreement,cheapAgreement,
    honestReducedAgreementFlag,w]

theorem mixed_costs_exact :
    flagMixed cheapFlag cheapAgreement cheapAgreement=78874449552666999 ∧
    flagMixed primaryFlag helperFlag primaryAgreement=406928924583954 := by
  norm_num [flagMixed,primaryFlag,helperFlag,cheapFlag,primaryAgreement,cheapAgreement,
    honestReducedAgreementFlag,w]

theorem incidence_numerators_exact :
    twoIncidenceNumerator cheapFlag cheapAgreement=2950307242120492336339964784 ∧
    oneIncidenceNumerator primaryFlag helperFlag primaryAgreement=78701681730235039416 := by
  rw [twoIncidenceNumerator,oneIncidenceNumerator,mixed_costs_exact.1,mixed_costs_exact.2]
  norm_num [n,v]

theorem active_caps_exact : cheapRegularCap=236576105857455036 ∧
    exitedHelperCap=704751208709671 := by
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
      (cheapFlag.yz+cheapFlag.all)*cheapAgreement.all=758960037 ∧
    758960037<prime ∧
    (helperFlag.yz+helperFlag.all)*primaryFlag.all+
      (primaryFlag.yz+primaryFlag.all)*helperFlag.all=1181888 ∧ 1181888<prime := by
  norm_num [cheapFlag,primaryFlag,helperFlag,cheapAgreement,honestReducedAgreementFlag,w,prime]

/-- The old extra R-coordinate condition really fails; only the certified
adaptive regular-component producer may consume the cheap count. -/
theorem old_cheap_literal_R_gate_fails :
    (cheapAgreement.zOnly+cheapAgreement.yz+cheapAgreement.all)*cheapFlag.all+
      (cheapFlag.zOnly+cheapFlag.yz+cheapFlag.all)*cheapAgreement.all=2915941275 ∧
    prime≤2915941275 := by
  norm_num [cheapFlag,cheapAgreement,honestReducedAgreementFlag,w,prime]

theorem small_absorption_margins :
    (n-v)*cheapAgreement.all-small*(a-v)=1065310865346 ∧
    (n-v)^2*cheapAgreement.all^2-small*(a-v)^2=1795076503721328365914818 ∧
    (n-v)*primaryAgreement.all-small*(a-v)=5754627185034 := by
  norm_num [n,v,small,a,cheapAgreement,primaryAgreement,honestReducedAgreementFlag,w]

theorem small_absorption_gates :
    small*(a-v)≤(n-v)*cheapAgreement.all ∧
    small*(a-v)^2≤(n-v)^2*cheapAgreement.all^2 ∧
    small*(a-v)≤(n-v)*primaryAgreement.all := by
  norm_num [n,v,small,a,cheapAgreement,primaryAgreement,honestReducedAgreementFlag,w]

theorem shortened_Johnson_gate :
    (n-(v+1))*(n-w)<(small+1)*((a-(v+1))^2-(n-(v+1))*(w-(v+1))) ∧
    v+1≤w ∧ w<a ∧ a≤n := by norm_num [n,v,w,small,a]

/-- This is exactly the mixed-coordinate cost used by the existing seedless
first-order consumer, before replacing source coordinate degrees by caps. -/
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
    positiveTAuxY=169435 ∧ positiveTAuxR=55460 ∧
    firstOrderRegularCap positiveTAuxY positiveTAuxR=13679673590906793 ∧
    firstOrderSingularCap positiveTAuxY positiveTAuxR=18793560765 ∧
    positiveTSingularCap=13679692384467558 ∧
    tFreeRegularCap=247446700702 ∧ tFreeSingularCap=339591 ∧ yOnlyCap=721 := by
  norm_num [positiveTAuxY,positiveTAuxR,firstOrderRegularCap,firstOrderRegularNumerator,
    firstOrderMixedCost,ceilQuotient,firstOrderSingularCap,positiveTSingularCap,
    tFreeRegularCap,tFreeSingularCap,yOnlyCap,n,w,a]

theorem cleanup_scaled_caps :
    firstOrderRegularNumerator positiveTAuxY positiveTAuxR≤
      firstOrderRegularCap positiveTAuxY positiveTAuxR*(a-w) ∧
    firstOrderRegularNumerator 721 236≤tFreeRegularCap*(a-w) := by
  norm_num [positiveTAuxY,positiveTAuxR,firstOrderRegularNumerator,firstOrderMixedCost,
    firstOrderRegularCap,tFreeRegularCap,ceilQuotient,n,w,a]

theorem cleanup_characteristic_gates :
    118<prime ∧ 236<prime ∧ 721<prime ∧ positiveTAuxY<prime ∧ positiveTAuxR<prime := by
  norm_num [positiveTAuxY,positiveTAuxR,prime]

theorem complete_cap_exact : completeCap=250960796897673279 := by
  unfold completeCap
  rw [active_caps_exact.1,active_caps_exact.2,cleanup_caps_exact.2.2.2.2.1,
    cleanup_caps_exact.2.2.2.2.2.1,cleanup_caps_exact.2.2.2.2.2.2.1,
    cleanup_caps_exact.2.2.2.2.2.2.2]

theorem complete_cap_lt_retained : completeCap<retained := by
  rw [complete_cap_exact]
  norm_num [retained]

theorem complete_headroom : retained-completeCap=2550874087000824 := by
  rw [complete_cap_exact]
  norm_num [retained]

/-- Shared flag costs are charged once after summing the assigned factors.
The cumulative degree premises and per-factor incidence inequalities remain
explicit; this theorem does not construct a factor partition. -/
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

/-- Final numerical assembly, with all unconnected geometric/factor/cleanup
inputs displayed. No scalar-family theorem is claimed by this adapter. -/
theorem complete_ledger_of_branch_bounds (total cheap exited positiveT tRegular tSingular yOnly : Nat)
    (hcover : total≤cheap+exited+positiveT+tRegular+tSingular+yOnly)
    (hcheap : cheap*(a-v)^2≤twoIncidenceNumerator cheapFlag cheapAgreement)
    (hexited : exited*(a-v)≤oneIncidenceNumerator primaryFlag helperFlag primaryAgreement)
    (hpositive : positiveT≤positiveTSingularCap)
    (htRegular : tRegular*(a-w)≤firstOrderRegularNumerator 721 236)
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

end ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900

#print axioms ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900.mixed_costs_exact
#print axioms ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900.seedless_coordinate_cost_eq
#print axioms ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900.cleanup_caps_exact
#print axioms ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900.aggregate_scaled_flags
#print axioms ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900.complete_cap_lt_retained
#print axioms ProximityPrize.SubmissionLower.WeightedRepresentativeCountLedgerW1332216900.complete_ledger_of_branch_bounds
