import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Exact-G root-count stop for the old-kernel value route

A passive shift of an old contact-kernel relation can create a new gradient
direction only through the old relation's scalar boundary value.  In the
exact m47 setting that value trace has the strict X-degree budget
`< 47 * |G|`, while complete agreement contact gives 47 zero Hasse
coordinates at each of the `|G|` distinct agreement nodes.  The trace is
therefore zero.

This file proves that root-count implication and its map-level form.  It is
kept separate from `K0PassiveValueNormalBridge6900` so each formal check has
a small import and memory footprint.
-/

namespace ProximityPrize.SubmissionLower.K0PassiveValueRootStop6900

open Polynomial

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

variable {K G Source Contact : Type*}
  [Field K] [Fintype G]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Contact] [Module K Contact]

/-- Hasse vanishing at one node gives the corresponding node-power
divisor, without dividing by factorials. -/
theorem node_pow_dvd_of_hasse_zero
    (a : K) (p : K[X]) (n : Nat)
    (h : ∀ j < n, (Polynomial.hasseDeriv j p).eval a = 0) :
    (Polynomial.X - Polynomial.C a) ^ n ∣ p := by
  have ht : Polynomial.X ^ n ∣ Polynomial.taylor a p := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro j hj
    rw [Polynomial.taylor_coeff, h j hj]
  have hh := map_dvd (Polynomial.taylorAlgHom (-a)).toRingHom ht
  change Polynomial.taylor (-a) (Polynomial.X ^ n) ∣
    Polynomial.taylor (-a) (Polynomial.taylor a p) at hh
  simpa only [Polynomial.taylor_pow, Polynomial.taylor_X,
    Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero,
    Polynomial.C_neg, sub_eq_add_neg] using hh

/-- A polynomial of degree strictly below `m * |G|` whose first `m` Hasse
coordinates vanish at every distinct agreement node is zero. -/
theorem polynomial_eq_zero_of_depth_agreement_hasse_zero
    (nodes : G → K) (hnodes : Function.Injective nodes) (m : Nat) (p : K[X])
    (hzero : ∀ i : G, ∀ j < m,
      (Polynomial.hasseDeriv j p).eval (nodes i) = 0)
    (hdegree : p.natDegree < m * Fintype.card G) :
    p = 0 := by
  have hfactor : ∀ i : G,
      ((Polynomial.X : K[X]) - Polynomial.C (nodes i)) ^ m ∣ p := by
    intro i
    apply node_pow_dvd_of_hasse_zero
    intro j hj
    exact hzero i j hj
  have hpairwise : Pairwise (Function.onFun IsCoprime fun i : G ↦
      ((Polynomial.X : K[X]) - Polynomial.C (nodes i)) ^ m) := by
    intro i j hij
    exact (Polynomial.pairwise_coprime_X_sub_C hnodes hij).pow
  have hprod :
      (∏ i : G,
        ((Polynomial.X : K[X]) - Polynomial.C (nodes i)) ^ m) ∣ p := by
    exact Fintype.prod_dvd_of_coprime hpairwise hfactor
  have hprodDegree :
      (∏ i : G,
        ((Polynomial.X : K[X]) - Polynomial.C (nodes i)) ^ m).natDegree =
          m * Fintype.card G := by
    rw [Polynomial.natDegree_prod]
    · simp [Polynomial.natDegree_pow, Nat.mul_comm]
    · intro i hi
      exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (nodes i))
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hprod
  rw [hprodDegree]
  exact hdegree

/-- Exact m47 specialization of the general agreement root bound. -/
theorem polynomial_eq_zero_of_depth47_agreement_hasse_zero
    (nodes : G → K) (hnodes : Function.Injective nodes) (p : K[X])
    (hzero : ∀ i : G, ∀ j < 47,
      (Polynomial.hasseDeriv j p).eval (nodes i) = 0)
    (hdegree : p.natDegree < 47 * Fintype.card G) :
    p = 0 :=
  polynomial_eq_zero_of_depth_agreement_hasse_zero
    nodes hnodes 47 p hzero hdegree

/-- Hence the value of such a trace at any proposed new boundary X-coordinate
is zero as well. -/
theorem boundary_value_eq_zero_of_depth47_agreement_hasse_zero
    (nodes : G → K) (hnodes : Function.Injective nodes) (p : K[X])
    (hzero : ∀ i : G, ∀ j < 47,
      (Polynomial.hasseDeriv j p).eval (nodes i) = 0)
    (hdegree : p.natDegree < 47 * Fintype.card G) (xi : K) :
    p.eval xi = 0 := by
  rw [polynomial_eq_zero_of_depth47_agreement_hasse_zero
    nodes hnodes p hzero hdegree]
  simp

/-- Restriction of an old-source scalar value to its complete contact
kernel. -/
def oldKernelValue
    (contact : Source →ₗ[K] Contact) (old : Submodule K Source)
    (value : old →ₗ[K] K) :
    LinearMap.ker (contact.domRestrict old) →ₗ[K] K :=
  value.domRestrict (LinearMap.ker (contact.domRestrict old))

/-- Map-level form of the STOP.  If an old source vector has a
degree-`<47|G|` value trace and old contact zero supplies its 47 agreement
Hasse zeros, then the value functional on the entire old contact kernel is
the zero map. -/
theorem oldKernelValue_eq_zero_of_depth47_root_bound
    (contact : Source →ₗ[K] Contact) (old : Submodule K Source)
    (trace : old →ₗ[K] K[X]) (value : old →ₗ[K] K)
    (nodes : G → K) (hnodes : Function.Injective nodes) (xi : K)
    (hvalueTrace : ∀ v : old, value v = (trace v).eval xi)
    (hdegree : ∀ v : old,
      (trace v).natDegree < 47 * Fintype.card G)
    (hcontactHasse : ∀ v : old, contact v.1 = 0 →
      ∀ i : G, ∀ j < 47,
        (Polynomial.hasseDeriv j (trace v)).eval (nodes i) = 0) :
    oldKernelValue contact old value = 0 := by
  apply LinearMap.ext
  intro v
  change value v.1 = 0
  rw [hvalueTrace]
  exact boundary_value_eq_zero_of_depth47_agreement_hasse_zero
    nodes hnodes (trace v.1) (hcontactHasse v.1 v.2) (hdegree v.1) xi

/-- In particular the nonzero-value witness required by the simple passive
shift bridge cannot exist under the exact-G root-bound hypotheses. -/
theorem no_nonzero_oldKernelValue_of_depth47_root_bound
    (contact : Source →ₗ[K] Contact) (old : Submodule K Source)
    (trace : old →ₗ[K] K[X]) (value : old →ₗ[K] K)
    (nodes : G → K) (hnodes : Function.Injective nodes) (xi : K)
    (hvalueTrace : ∀ v : old, value v = (trace v).eval xi)
    (hdegree : ∀ v : old,
      (trace v).natDegree < 47 * Fintype.card G)
    (hcontactHasse : ∀ v : old, contact v.1 = 0 →
      ∀ i : G, ∀ j < 47,
        (Polynomial.hasseDeriv j (trace v)).eval (nodes i) = 0) :
    ¬ ∃ v : LinearMap.ker (contact.domRestrict old),
      oldKernelValue contact old value v ≠ 0 := by
  rw [oldKernelValue_eq_zero_of_depth47_root_bound
    contact old trace value nodes hnodes xi hvalueTrace hdegree hcontactHasse]
  simp

#print axioms polynomial_eq_zero_of_depth_agreement_hasse_zero
#print axioms polynomial_eq_zero_of_depth47_agreement_hasse_zero
#print axioms boundary_value_eq_zero_of_depth47_agreement_hasse_zero
#print axioms oldKernelValue_eq_zero_of_depth47_root_bound
#print axioms no_nonzero_oldKernelValue_of_depth47_root_bound

end

end ProximityPrize.SubmissionLower.K0PassiveValueRootStop6900
