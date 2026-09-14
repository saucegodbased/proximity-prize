import CanonicalHighTailCoefficientRank6900
import PolynomialReciprocalAlignedControl6900

/-!
# API-scope countergate for high tails versus an aligned rational cross

The high-tail rank-two invariant does not by itself force the aligned-cross
coefficients `c,d` to vary.  The existing reciprocal control construction has
literal `c = 1`, `d = 0`.  Here we prove, by a kernel-checked root count, that
at denominator degree `2049` every nonzero constant direction in that control
has canonical degree at least `260095`, far above the endpoint cutoff
`133120`.

This is deliberately an `AlignedCrossData` countergate, not an inhabitant of
the full `DataElevenHighEClosedLeaf`: it satisfies the exact `cross` and all
four source equations, but does not manufacture the enormous same-family
weighted/pole witness carried by that leaf.
-/

namespace ProximityPrize.SubmissionLower.ProjectiveHighReciprocalCrossCountergate6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open ActualAlignedCrossMinimumCount6900
open PolynomialReciprocalAlignedControl6900
open CanonicalHighTailCoefficientRank6900
open UniversalProjectiveHighDirectionEndpointCut6900
open LowReceivedDirectionScalarSplit1331196900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP IRSProfile.Field 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

abbrev reciprocalDomainU (E : ExtensionField[X]) :
    Fin 2 → Index → ExtensionField :=
  reciprocalU E (fun i ↦ IRSProfile.domain i)

theorem receivedReciprocalDirectionInterpolant_eval (E : ExtensionField[X])
    (a b : ExtensionField) (i : Index) :
    (receivedDirectionInterpolant IRSProfile.domain
      (fun x ↦ a * reciprocalDomainU E 0 x +
        b * reciprocalDomainU E 1 x)).eval (IRSProfile.domain i) =
      a * reciprocalDomainU E 0 i + b * reciprocalDomainU E 1 i := by
  exact receivedDirectionInterpolant_eval IRSProfile.domain
    (fun x ↦ a * reciprocalDomainU E 0 x +
      b * reciprocalDomainU E 1 x) i

def ReciprocalProjectiveHigh (E : ExtensionField[X]) : Prop :=
  ∀ a b : ExtensionField, (a ≠ 0 ∨ b ≠ 0) →
    133120 ≤
      (receivedDirectionInterpolant IRSProfile.domain
        (fun i ↦ a * reciprocalDomainU E 0 i +
          b * reciprocalDomainU E 1 i)).natDegree

theorem clear_affine_reciprocal {K : Type*} [Field K]
    (e x a b : K) (he : e ≠ 0) :
    e * (a * (x / e) + b * (1 / e)) - (a * x + b) = 0 := by
  field_simp [he]
  ring

/-- Root-count lower bound for every projective direction of the reciprocal
word.  If a direction had degree below `262144 - 2049`, multiplying it by
`E` would give a polynomial of degree below the domain size which agrees with
the nonzero affine polynomial `a*X+b` at every node.  Root rigidity would make
`E` divide that affine polynomial, contradicting `deg E = 2049`. -/
theorem reciprocalDomain_direction_natDegree_ge_260095
    (E : ExtensionField[X]) (hEdegree : E.natDegree = 2049)
    (hroot : ∀ i, E.eval (IRSProfile.domain i) ≠ 0)
    (a b : ExtensionField) (hab : a ≠ 0 ∨ b ≠ 0) :
    260095 ≤
      (receivedDirectionInterpolant IRSProfile.domain
        (fun i ↦ a * reciprocalDomainU E 0 i +
          b * reciprocalDomainU E 1 i)).natDegree := by
  classical
  let V := receivedDirectionInterpolant IRSProfile.domain
    (fun i ↦ a * reciprocalDomainU E 0 i +
      b * reciprocalDomainU E 1 i)
  have hcleared : ∀ i,
      E.eval (IRSProfile.domain i) * V.eval (IRSProfile.domain i) =
        a * IRSProfile.domain i + b := by
    intro i
    have hVeval := receivedReciprocalDirectionInterpolant_eval E a b i
    rw [hVeval]
    simp only [reciprocalDomainU, reciprocalU, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact sub_eq_zero.mp
      (clear_affine_reciprocal _ _ _ _ (hroot i))
  by_contra hdegree
  exact (affine_reciprocal_interpolant_not_degree_lt
      IRSProfile.domain E V 2049 260095
      (by norm_num [Index, IRSProfile.Index])
      (by norm_num [Index, IRSProfile.Index]) (by norm_num) hEdegree
      a b hab hcleared) (Nat.lt_of_not_ge hdegree)

theorem reciprocalDomain_projectiveHigh
    (E : ExtensionField[X]) (hEdegree : E.natDegree = 2049)
    (hroot : ∀ i, E.eval (IRSProfile.domain i) ≠ 0) :
    ReciprocalProjectiveHigh E := by
  intro a b hab
  exact (show 133120 ≤ 260095 by omega).trans
    (reciprocalDomain_direction_natDegree_ge_260095 E hEdegree hroot a b hab)

/-- The preceding raw predicate is literally the endpoint's canonical
projective-high predicate, not merely an analogous custom notion. -/
theorem reciprocalDomain_canonicalProjectiveHigh
    (E : ExtensionField[X]) (hEdegree : E.natDegree = 2049)
    (hroot : ∀ i, E.eval (IRSProfile.domain i) ≠ 0) :
    CanonicalHighTailDirectionIndependent IRSProfile.domain
      (reciprocalDomainU E) := by
  intro a b hab
  exact (show 133120 ≤ 260095 by norm_num).trans
    (reciprocalDomain_direction_natDegree_ge_260095
      E hEdegree hroot a b hab)

/-- Conditional literal cross package.  Every public field of
`AlignedCrossData`, including all four source equations, is supplied by the
existing `reciprocalCross`; its coefficients are still `c=1,d=0`. -/
theorem reciprocalCross_constant_cd_with_canonicalHigh
    (E : ExtensionField[X]) (hEdegree : E.natDegree = 2049)
    (hEne : E ≠ 0)
    (hroot : ∀ i, E.eval (IRSProfile.domain i) ≠ 0) :
    ∃ R : AlignedCrossData (reciprocalDomainU E) E.natDegree,
      R.E = E ∧ R.c = 1 ∧ R.d = 0 ∧ R.N = -1 ∧
      ¬ R.E ∣ R.N ∧
      CanonicalHighTailDirectionIndependent IRSProfile.domain
        (reciprocalDomainU E) := by
  let R := reciprocalCross E (fun i ↦ IRSProfile.domain i)
    hEne hroot (fun i ↦ sigma_domain i)
  have hnonpolynomial : ¬ R.E ∣ R.N := by
    intro hdiv
    have h := natDegree_le_of_dvd hdiv
      (show R.N ≠ 0 by simp [R, reciprocalCross])
    simp only [R, reciprocalCross, hEdegree, natDegree_neg,
      natDegree_one] at h
    omega
  exact ⟨R, rfl, rfl, rfl, rfl, hnonpolynomial,
    reciprocalDomain_canonicalProjectiveHigh E hEdegree hroot⟩

/-- Fully inhabited API-scope countergate at the exact excess `2049`.
It is compatible with the newer nonpolynomial-wrap lower bound too:
`260095 > 237212 + 2049`. -/
theorem exists_constant_cd_canonicalHigh_alignedCross :
    ∃ E : ExtensionField[X], E.natDegree = 2049 ∧ E ≠ 0 ∧
      IsCoprime E (E.map sigma) ∧
      ∃ R : AlignedCrossData (reciprocalDomainU E) E.natDegree,
        R.E = E ∧ R.c = 1 ∧ R.d = 0 ∧ R.N = -1 ∧
        ¬ R.E ∣ R.N ∧
        CanonicalHighTailDirectionIndependent IRSProfile.domain
          (reciprocalDomainU E) := by
  obtain ⟨alpha, halpha⟩ :=
    ActualWeightedOneSmallGradeCount6900.target_exists_nonfixed
  obtain ⟨E, hEdegree, hEne, hroots, hcoprime⟩ :=
    exists_power_denominator sigma alpha 2049 (by omega) halpha
  have hroot (i : Index) : E.eval (IRSProfile.domain i) ≠ 0 :=
    hroots (IRSProfile.domain i) (sigma_domain i)
  obtain ⟨R, hRE, hRc, hRd, hRN, hproper, hhigh⟩ :=
    reciprocalCross_constant_cd_with_canonicalHigh E hEdegree hEne hroot
  exact ⟨E, hEdegree, hEne, hcoprime, R, hRE, hRc, hRd, hRN,
    hproper, hhigh⟩

theorem reciprocal_countergate_wrap_compatible :
    237212 + 2049 < 260095 := by norm_num

#print axioms reciprocalDomain_direction_natDegree_ge_260095
#print axioms reciprocalDomain_projectiveHigh
#print axioms reciprocalDomain_canonicalProjectiveHigh
#print axioms reciprocalCross_constant_cd_with_canonicalHigh
#print axioms exists_constant_cd_canonicalHigh_alignedCross

end
end ProximityPrize.SubmissionLower.ProjectiveHighReciprocalCrossCountergate6900
