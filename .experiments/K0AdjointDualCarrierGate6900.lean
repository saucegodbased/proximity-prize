import GlobalO2WeakCS4FilteredHRSAdapter6900
import HrsGlobalPassiveAdjacentInterface6900

/-!
# Rank-defect dual witness and finite-node decomposition for k=0

This file proves the choice-free linear-algebra bridge which precedes any
HRS recurrence.  A four-boundary rank defect gives one nonzero boundary
functional represented by a single compatible dual row of the complete
contact map.  A dual row on a finite product is then the sum of its literal
node restrictions.

No claim is made that the node restrictions have the complementary degree
or agreement vanishing required by the target recurrence.
-/

namespace ProximityPrize.SubmissionLower.K0AdjointDualCarrierGate6900

open ProximityPrize.SubmissionLower.GlobalO2WeakCS4FilteredHRSAdapter6900

noncomputable section

set_option autoImplicit false
set_option Elab.async false

variable {k V S T I : Type*}
  [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup S] [Module k S]
  [AddCommGroup T] [Module k T]
  [Fintype I] [DecidableEq I]

/-- Rank below four on the complete contact kernel produces one nonzero
four-boundary covector and one *single compatible* complete-contact dual row.
There is no pivot/minor choice in the statement. -/
theorem exists_nonzero_boundary_contact_dual_of_rank_lt_four
    (contact : V →ₗ[k] S) (jet : V →ₗ[k] Boundary4 k)
    (hrank : Module.finrank k
      (LinearMap.range (fullKernelFourJet contact jet)) < 4) :
    exists ell : Module.Dual k (Boundary4 k), ell ≠ 0 ∧
      exists eta : Module.Dual k S,
        jet.dualMap ell = contact.dualMap eta := by
  have hnotRigid : ¬ AdjointBoundaryRigidity contact jet := by
    intro hrigid
    have heq := fullKernelFourJet_rank_eq_four_of_adjointBoundaryRigidity
      contact jet hrigid
    omega
  unfold AdjointBoundaryRigidity at hnotRigid
  push Not at hnotRigid
  obtain ⟨ell, hrow, hell⟩ := hnotRigid
  obtain ⟨eta, heta⟩ := hrow
  exact ⟨ell, hell, eta, heta.symm⟩

/-- Restriction of a functional on a finite node product to one literal
node, by extending the local vector by zero at every other node. -/
def localDual (eta : Module.Dual k (I -> T)) (x : I) : Module.Dual k T :=
  eta.comp (LinearMap.single k (fun _ : I => T) x)

/-- A functional on a finite node product is the sum of its node
restrictions.  This is the exact decomposition needed before applying the
local Hasse/CRT representation to each contact block. -/
theorem sum_localDual_apply
    (eta : Module.Dual k (I -> T)) (v : I -> T) :
    (∑ x, localDual eta x (v x)) = eta v := by
  calc
    (∑ x, localDual eta x (v x)) =
        ∑ x, eta ((LinearMap.single k (fun _ : I => T) x) (v x)) := rfl
    _ = eta (∑ x, (LinearMap.single k (fun _ : I => T) x) (v x)) :=
      by rw [map_sum]
    _ = eta v := by
      congr 1
      funext y
      simp

omit [FiniteDimensional k V] in
/-- Evaluating a compatible adjoint relation on any source vector gives
one aggregate equation involving the node-local restrictions of the same
dual row. -/
theorem boundary_eq_sum_local_contact_of_dual_relation
    (contact : V →ₗ[k] (I -> T))
    (jet : V →ₗ[k] Boundary4 k)
    (ell : Module.Dual k (Boundary4 k))
    (eta : Module.Dual k (I -> T))
    (hrelation : jet.dualMap ell = contact.dualMap eta)
    (v : V) :
    ell (jet v) = ∑ x, localDual eta x ((contact v) x) := by
  have hpoint := LinearMap.congr_fun hrelation v
  change ell (jet v) = eta (contact v) at hpoint
  rw [sum_localDual_apply]
  exact hpoint

omit [FiniteDimensional k V] in
/-- If a source carrier has zero boundary value and zero agreement contact,
the compatible dual row gives a genuinely error-only aggregate equation.
This is the exact logical reduction; source legality and HRS identification
of the carrier remain separate mathematical obligations. -/
theorem error_only_equation_of_zero_boundary_and_agreement
    {G E : Type*} [Fintype G] [Fintype E]
    [DecidableEq G] [DecidableEq E]
    (contactG : V →ₗ[k] (G -> T))
    (contactE : V →ₗ[k] (E -> T))
    (jet : V →ₗ[k] Boundary4 k)
    (ell : Module.Dual k (Boundary4 k))
    (eta : Module.Dual k ((G -> T) × (E -> T)))
    (hrelation : jet.dualMap ell =
      (contactG.prod contactE).dualMap eta)
    (v : V) (hjet : jet v = 0) (hG : contactG v = 0) :
    (∑ x : E,
      localDual (eta.comp (LinearMap.inr k (G -> T) (E -> T))) x
        ((contactE v) x)) = 0 := by
  have hpoint := LinearMap.congr_fun hrelation v
  change ell (jet v) = eta (contactG v, contactE v) at hpoint
  rw [hjet, map_zero, hG] at hpoint
  calc
    (∑ x : E,
        localDual (eta.comp (LinearMap.inr k (G -> T) (E -> T))) x
          ((contactE v) x)) =
        (eta.comp (LinearMap.inr k (G -> T) (E -> T))) (contactE v) :=
      sum_localDual_apply _ _
    _ = eta (0, contactE v) := rfl
    _ = 0 := hpoint.symm

/-- Cofactor-free end-to-end form.  A rank defect supplies one compatible
dual row which gives the error-only equation for *every* member of any
literal source carrier family having zero agreement contact and zero
boundary jet. -/
theorem exists_compatible_dual_with_all_error_only_equations_of_rank_lt_four
    {G E P : Type*} [Fintype G] [Fintype E]
    [DecidableEq G] [DecidableEq E]
    (contactG : V →ₗ[k] (G -> T))
    (contactE : V →ₗ[k] (E -> T))
    (jet : V →ₗ[k] Boundary4 k)
    (carrier : P -> V)
    (hjet : forall p, jet (carrier p) = 0)
    (hG : forall p, contactG (carrier p) = 0)
    (hrank : Module.finrank k
      (LinearMap.range
        (fullKernelFourJet (contactG.prod contactE) jet)) < 4) :
    exists ell : Module.Dual k (Boundary4 k), ell ≠ 0 ∧
      exists eta : Module.Dual k ((G -> T) × (E -> T)),
        jet.dualMap ell = (contactG.prod contactE).dualMap eta ∧
        forall p,
          (∑ x : E,
            localDual
                (eta.comp (LinearMap.inr k (G -> T) (E -> T))) x
              ((contactE (carrier p)) x)) = 0 := by
  obtain ⟨ell, hell, eta, hrelation⟩ :=
    exists_nonzero_boundary_contact_dual_of_rank_lt_four
      (contactG.prod contactE) jet hrank
  refine ⟨ell, hell, eta, hrelation, ?_⟩
  intro p
  exact error_only_equation_of_zero_boundary_and_agreement
    contactG contactE jet ell eta hrelation (carrier p) (hjet p) (hG p)

#print axioms exists_nonzero_boundary_contact_dual_of_rank_lt_four
#print axioms sum_localDual_apply
#print axioms boundary_eq_sum_local_contact_of_dual_relation
#print axioms error_only_equation_of_zero_boundary_and_agreement
#print axioms exists_compatible_dual_with_all_error_only_equations_of_rank_lt_four

end

end ProximityPrize.SubmissionLower.K0AdjointDualCarrierGate6900
