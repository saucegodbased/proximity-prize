import ProjectiveHighReciprocalCrossCountergate6900
import ActualAdjacentFilteredHardCornerElimination6900
import TZeroReciprocalResiduePlaneCountergate6900
import FixedScalarSmallSReciprocalSeed6900

/-!
# The scalar hard-corner predicate alone admits `s = 0`

This is a deliberately scoped countergate.  It constructs the literal
`FixedScalarWeightedNoAdjacentHardCornerCondition` on the reciprocal aligned
cross with `c = 1`, `d = 0`, and displayed homogeneous minimum `Q = 1`.
Its retained scalar family is an injective Frobenius-fixed plane indexed by
`BaseField × BaseField`, so it has more than `253511670984674103` members.

The agreement sets in this control are empty.  Thus this is **not** a
`DataElevenHighEClosedLeaf`, and it does not realize the actual `180413`
agreement hypothesis, selected-word agreement, badness, or conic incidence.
It proves only that the scalar hard-corner record itself cannot imply a
positive lower bound on `max (deg c) (deg d) + deg Q`.
-/

namespace ProximityPrize.SubmissionLower.FixedScalarSmallSCountergate6900

open Polynomial ProximityPrize.Benchmark SupportRecurrence6900.Target
open ActualAlignedRationalCrossData6900
open PolynomialReciprocalAlignedControl6900
open ProjectiveHighReciprocalCrossCountergate6900
open UniversalProjectiveHighDirectionEndpointCut6900
open ActualAdjacentFilteredHardCornerElimination6900
open TZeroReciprocalResiduePlaneCountergate6900
open FixedScalarSmallSReciprocalSeed6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

local instance {T : Type*} : DecidableEq T := Classical.decEq T
local instance : CharP IRSProfile.Field 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-! A finite-image package which keeps all concrete finite-field equality
tests out of the proofs below. -/

def imageExtend {A B C : Type*} (f : A → B) (g : A → C) (junk : B → C) :
    B → C :=
  Function.extend f g junk

theorem finite_image_extend_package {A B C : Type*}
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f)
    (g : A → C) (hg : Function.Injective g) (junk : B → C) :
    ∃ Good : Finset B,
      Good.card = Fintype.card A ∧
      Set.InjOn (imageExtend f g junk) (↑Good : Set B) ∧
      ∀ b ∈ Good, ∃ a : A,
        f a = b ∧ imageExtend f g junk b = g a := by
  let Good : Finset B := Finset.univ.image f
  refine ⟨Good, ?_, ?_, ?_⟩
  · change (Finset.univ.image f).card = Fintype.card A
    rw [Finset.card_image_iff.mpr hf.injOn,
      Finset.card_univ]
  · intro x hx y hy hxy
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : g a = g b := by
      simpa only [imageExtend, hf.extend_apply] using hxy
    exact congrArg f (hg hab)
  · intro b hb
    obtain ⟨a, _ha, hab⟩ := Finset.mem_image.mp hb
    subst b
    exact ⟨a, rfl, by simp only [imageExtend, hf.extend_apply]⟩

def planeSeed (theta : ExtensionField) (uv : BaseField × BaseField) :
    ExtensionField :=
  planeScalar theta uv.1 uv.2

def planeFixedRepresentative (e : Nat) (uv : BaseField × BaseField) :
    ExtensionField[X] :=
  -planeRepresentative e uv.1 uv.2

def planeSelectedRepresentative (uv : BaseField × BaseField) :
    ExtensionField[X] :=
  -Polynomial.C (algebraMap BaseField ExtensionField uv.2)

theorem planeSeed_injective (theta : ExtensionField)
    (htheta : sigma theta ≠ theta) :
    Function.Injective (planeSeed theta) := by
  exact planeScalar_injective theta htheta

theorem planeFixedRepresentative_injective (e : Nat) (he : 0 < e) :
    Function.Injective (planeFixedRepresentative e) := by
  intro uv wz h
  apply planeRepresentative_injective e he
  exact neg_injective h
where
  planeRepresentative_injective (e : Nat) (he : 0 < e) :
      Function.Injective
        (fun uv : BaseField × BaseField ↦
          planeRepresentative e uv.1 uv.2) := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have hu := congrArg (fun P : ExtensionField[X] ↦ P.eval 0) h
    have hu' : algebraMap BaseField ExtensionField u =
        algebraMap BaseField ExtensionField u' := by
      simpa only [planeRepresentative, eval_add, eval_C, eval_mul, eval_pow,
        eval_X, zero_pow (Nat.ne_of_gt he), mul_zero, add_zero] using hu
    have huv : u = u' := (algebraMap BaseField ExtensionField).injective hu'
    subst u'
    have hmul :
        Polynomial.C (algebraMap BaseField ExtensionField v) *
            (Polynomial.X : ExtensionField[X]) ^ e =
          Polynomial.C (algebraMap BaseField ExtensionField v') *
            (Polynomial.X : ExtensionField[X]) ^ e := by
      change
        Polynomial.C (algebraMap BaseField ExtensionField u) +
            Polynomial.C (algebraMap BaseField ExtensionField v) *
              (Polynomial.X : ExtensionField[X]) ^ e =
          Polynomial.C (algebraMap BaseField ExtensionField u) +
            Polynomial.C (algebraMap BaseField ExtensionField v') *
              (Polynomial.X : ExtensionField[X]) ^ e at h
      exact add_left_cancel h
    have hC : Polynomial.C (algebraMap BaseField ExtensionField v) =
        Polynomial.C (algebraMap BaseField ExtensionField v') := by
      exact mul_right_cancel₀
        (pow_ne_zero e (Polynomial.X_ne_zero :
          (Polynomial.X : ExtensionField[X]) ≠ 0)) hmul
    have hv : v = v' := (algebraMap BaseField ExtensionField).injective
      (Polynomial.C_injective hC)
    subst v'
    rfl

theorem planeFixedRepresentative_fixed (e : Nat)
    (uv : BaseField × BaseField) :
    (planeFixedRepresentative e uv).map sigma =
      planeFixedRepresentative e uv := by
  simpa only [planeFixedRepresentative, Polynomial.map_neg] using
    congrArg Neg.neg (planeRepresentative_fixed e uv.1 uv.2)

theorem planeFixedRepresentative_degree_le (e : Nat)
    (uv : BaseField × BaseField) :
    (planeFixedRepresentative e uv).natDegree ≤ e := by
  simpa only [planeFixedRepresentative, Polynomial.natDegree_neg] using
    planeRepresentative_degree_le e uv.1 uv.2

theorem plane_exact_residual (theta : ExtensionField) (e : Nat)
    (uv : BaseField × BaseField) :
    ((Polynomial.X : ExtensionField[X]) ^ e - Polynomial.C theta) *
        planeSelectedRepresentative uv =
      Polynomial.C (planeSeed theta uv) + planeFixedRepresentative e uv := by
  rcases uv with ⟨u, v⟩
  simp only [planeSelectedRepresentative, planeSeed, planeScalar,
    planeFixedRepresentative, planeRepresentative, Polynomial.C_add,
    Polynomial.C_mul]
  ring

theorem power_denominator_second_or_third_coprime
    (theta : ExtensionField) (htheta : sigma theta ≠ theta) (e : Nat) :
    IsCoprime ((Polynomial.X : ExtensionField[X]) ^ e - Polynomial.C theta)
        (((Polynomial.X : ExtensionField[X]) ^ e - Polynomial.C theta).map
          (sigma.comp sigma)) ∨
      IsCoprime ((Polynomial.X : ExtensionField[X]) ^ e - Polynomial.C theta)
        (((Polynomial.X : ExtensionField[X]) ^ e - Polynomial.C theta).map
          (sigma.comp (sigma.comp sigma))) := by
  by_cases hsecond : sigma (sigma theta) = theta
  · right
    have hthird : sigma (sigma (sigma theta)) ≠ theta := by
      rw [hsecond]
      exact htheta
    simpa only [RingHom.comp_apply] using
      power_denominator_conjugate_coprime
        (sigma.comp (sigma.comp sigma)) theta e hthird
  · left
    simpa only [RingHom.comp_apply] using
      power_denominator_conjugate_coprime (sigma.comp sigma) theta e hsecond

theorem denominator_second_or_third_coprime
    (theta : ExtensionField) (htheta : sigma theta ≠ theta) (e : Nat) :
    IsCoprime (denominator theta e)
        ((denominator theta e).map (sigma.comp sigma)) ∨
      IsCoprime (denominator theta e)
        ((denominator theta e).map
          (sigma.comp (sigma.comp sigma))) := by
  simpa only [denominator] using
    power_denominator_second_or_third_coprime theta htheta e

theorem denominator_plane_exact_residual (theta : ExtensionField) (e : Nat)
    (uv : BaseField × BaseField) :
    denominator theta e * planeSelectedRepresentative uv =
      Polynomial.C (planeSeed theta uv) + planeFixedRepresentative e uv := by
  simpa only [denominator] using plane_exact_residual theta e uv

def emptyAgreement (_gamma : ExtensionField) : Finset Index := ∅

/-- Exact constructor for the literal scalar hard-corner predicate.  The
hidden existential tuple is `B=1`, `E0=X^2049-C theta`, `N0=-1`, `Q=1`, so
its scalar degree parameter is exactly `s=0`.  Its agreement sets are empty. -/
theorem exists_reciprocal_plane_fixedScalar_noAdjacent_condition
    (theta : ExtensionField) (htheta : sigma theta ≠ theta) :
    ∃ R : AlignedCrossData
        (reciprocalDomainU (denominator theta 2049))
        (denominator theta 2049).natDegree,
      R.c = 1 ∧ R.d = 0 ∧
      ∃ Gamma : Finset ExtensionField,
      ∃ selected : ExtensionField → ExtensionField[X],
        FixedScalarWeightedNoAdjacentHardCornerCondition
          Gamma emptyAgreement selected R := by
  let E : ExtensionField[X] := denominator theta 2049
  have hE : E ≠ 0 := hostileDenominator_ne_zero theta
  have hroot : ∀ i, E.eval (IRSProfile.domain i) ≠ 0 :=
    hostileDenominator_root_free theta htheta
  obtain ⟨R, hRE, hRL, hRM, hRc, hRd, hRN⟩ :=
    exists_reciprocalCross_full_fields E hE hroot
  have hEdegree : E.natDegree = 2049 :=
    hostileDenominator_natDegree theta
  let f : BaseField × BaseField → ExtensionField := planeSeed theta
  let g : BaseField × BaseField → ExtensionField[X] :=
    planeFixedRepresentative 2049
  let scalar : ExtensionField → ExtensionField[X] :=
    imageExtend f g (fun gamma ↦ -Polynomial.C gamma)
  let selected : ExtensionField → ExtensionField[X] :=
    imageExtend f planeSelectedRepresentative (fun _gamma ↦ 0)
  obtain ⟨Good, hGoodCard, hscalarInj, hrepresent⟩ :=
    finite_image_extend_package f (planeSeed_injective theta htheta) g
      (planeFixedRepresentative_injective 2049 (by omega))
      (fun gamma ↦ -Polynomial.C gamma)
  refine ⟨R, ?_⟩
  constructor
  · exact hRc
  constructor
  · exact hRd
  refine ⟨Good, selected, ?_⟩
  refine ⟨1, E, -1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact one_ne_zero
  · exact hE
  · simpa only [one_mul] using hRE
  · simpa only [one_mul] using hRN
  · exact ⟨0, -1, by ring⟩
  · exact isCoprime_one_right
  · exact one_ne_zero
  · rw [hRL, hRM]
    simp
  · intro P hP _hhom
    simp
  · norm_num [hRc, hRd, hEdegree]
  · exact hroot
  · simpa only [E] using
      hostileDenominator_conjugate_coprime theta htheta
  · simpa only [E] using
      denominator_second_or_third_coprime theta htheta 2049
  · refine ⟨Good, scalar, (fun _i ↦ 0), 0, 1, ?_⟩
    dsimp only
    refine ⟨Finset.Subset.rfl,
      ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp
    · rw [hGoodCard, Fintype.card_prod]
      have hbase : Fintype.card BaseField = 2130706433 := by
        norm_num [BaseField, KoalaBear.Field, KoalaBear.fieldSize]
      rw [hbase]
      norm_num
    · norm_num [hRc, hRd, hEdegree]
    · norm_num [hRc, hRd, hEdegree]
    · intro i
      simp
    · simp [hRc, hRd]
    · exact hscalarInj
    · intro i
      simp
    · intro gamma hgamma
      obtain ⟨uv, hseed, hscalar⟩ := hrepresent gamma hgamma
      have hseed' : planeSeed theta uv = gamma := by
        simpa only [f] using hseed
      have hscalar' : scalar gamma = planeFixedRepresentative 2049 uv := by
        simpa only [scalar, g] using hscalar
      have hselected : selected gamma = planeSelectedRepresentative uv := by
        rw [← hseed']
        simpa only [selected, f, imageExtend] using
          (planeSeed_injective theta htheta).extend_apply
            planeSelectedRepresentative (fun _gamma ↦ 0) uv
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hscalar']
        exact planeFixedRepresentative_fixed 2049 uv
      · rw [hscalar']
        exact (planeFixedRepresentative_degree_le 2049 uv).trans
          (by norm_num [hRc, hRd, hEdegree])
      · rw [hselected, hscalar', ← hseed']
        rw [hRc, hRd]
        simpa only [zero_add, mul_one, mul_zero, add_zero, one_mul, E] using
          denominator_plane_exact_residual theta 2049 uv
      · intro i hi
        simp [emptyAgreement] at hi
    all_goals norm_num [hRc, hRd, hEdegree]

/-- Fully inhabited scalar-record countergate with literal constant `c,d`,
exact projective-high received rows, and explicit `Q=1`.  It is still not a
DataEleven leaf and still has empty agreement sets. -/
theorem exists_projectiveHigh_fixedScalar_condition_with_s_zero :
    ∃ theta : ExtensionField, sigma theta ≠ theta ∧
    let E : ExtensionField[X] := denominator theta 2049
    ∃ R : AlignedCrossData (reciprocalDomainU E) E.natDegree,
      R.c = 1 ∧ R.d = 0 ∧
      max R.c.natDegree R.d.natDegree +
          (1 : ExtensionField[X]).natDegree = 0 ∧
      CanonicalHighTailDirectionIndependent IRSProfile.domain
        (reciprocalDomainU E) ∧
      ∃ Gamma : Finset ExtensionField,
      ∃ selected : ExtensionField → ExtensionField[X],
        FixedScalarWeightedNoAdjacentHardCornerCondition
          Gamma emptyAgreement selected R := by
  obtain ⟨theta, htheta⟩ :=
    ActualWeightedOneSmallGradeCount6900.target_exists_nonfixed
  obtain ⟨R, hc, hd, Gamma, selected, hcondition⟩ :=
    exists_reciprocal_plane_fixedScalar_noAdjacent_condition theta htheta
  refine ⟨theta, htheta, R, hc, hd, ?_, ?_, Gamma, selected, hcondition⟩
  · simp [hc, hd]
  · exact reciprocalDomain_canonicalProjectiveHigh (denominator theta 2049)
      (hostileDenominator_natDegree theta)
      (hostileDenominator_root_free theta htheta)

#print axioms finite_image_extend_package
#print axioms planeFixedRepresentative_injective
#print axioms plane_exact_residual
#print axioms exists_reciprocal_plane_fixedScalar_noAdjacent_condition
#print axioms exists_projectiveHigh_fixedScalar_condition_with_s_zero

end
end ProximityPrize.SubmissionLower.FixedScalarSmallSCountergate6900
