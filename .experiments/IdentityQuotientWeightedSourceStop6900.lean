import HeterogeneousLinearInterpolationSource6900
import WeightedSourcePowerEscape6900

/-!
# Quotienting the near-total affine identity does not enlarge the weighted source

The fixed identity is triangular in the selected-polynomial jet whenever its
`E0` coefficient is nonzero.  Hence, after quotienting by the identity and its
first two prolongations, the scalar value/first derivative/second derivative
remain arbitrary.  The resulting one-word jet source is exactly the existing
four-variable weighted source, not a new lower-rank source.

The final two lemmas record the two independent numerical obstructions:

* in the heterogeneous source, even the smallest certified masked-identity
  subspace is much larger than the raw rank-nullity surplus at 262143 nodes;
* in the weighted source, quotienting by a putative polynomial factor is the
  existing first `powerStage` cut and therefore pays the existing `stageBand`.
-/
namespace ProximityPrize.SubmissionLower.IdentityQuotientWeightedSourceStop6900

open Order2SourceBasisScaffold
open WeightedSourceIndex6900
open WeightedSourceBoxQuotient6900
open WeightedSourceColumnBands6900
open WeightedSourcePowerEscape6900

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

/-- Every scalar second jet has a lift through an affine identity and its first
two formal derivative equations.  The only required pivot is the root-free
coefficient of the selected word. -/
theorem affine_identity_allows_arbitrary_second_jet
    {K : Type*} [Field K]
    (e e1 e2 a0 a1 a2 b0 b1 b2 s0 s1 s2 : K) (he : e ≠ 0) :
    ∃ p0 p1 p2 : K,
      e*p0 = a0+b0*s0 ∧
      e*p1+e1*p0 = a1+b1*s0+b0*s1 ∧
      e*p2+2*e1*p1+e2*p0 = a2+b2*s0+2*b1*s1+b0*s2 := by
  let p0 := (a0+b0*s0)/e
  let p1 := (a1+b1*s0+b0*s1-e1*p0)/e
  let p2 := (a2+b2*s0+2*b1*s1+b0*s2-2*e1*p1-e2*p0)/e
  refine ⟨p0,p1,p2,?_,?_,?_⟩
  · dsimp only [p0]
    field_simp [he]
  · dsimp only [p1]
    field_simp [he]
    ring
  · dsimp only [p2]
    field_simp [he]
    ring

/-- The triangular lift is unique.  Thus the quotient has exactly the scalar
jet coordinates; it has neither an extra selected-jet coordinate nor a hidden
equation on the scalar jet. -/
theorem affine_identity_second_jet_unique
    {K : Type*} [Field K]
    (e e1 e2 a0 a1 a2 b0 b1 b2 s0 s1 s2 : K) (he : e ≠ 0)
    (p0 p1 p2 q0 q1 q2 : K)
    (hp0 : e*p0 = a0+b0*s0)
    (hp1 : e*p1+e1*p0 = a1+b1*s0+b0*s1)
    (hp2 : e*p2+2*e1*p1+e2*p0 = a2+b2*s0+2*b1*s1+b0*s2)
    (hq0 : e*q0 = a0+b0*s0)
    (hq1 : e*q1+e1*q0 = a1+b1*s0+b0*s1)
    (hq2 : e*q2+2*e1*q1+e2*q0 = a2+b2*s0+2*b1*s1+b0*s2) :
    p0=q0 ∧ p1=q1 ∧ p2=q2 := by
  have h0 : e*p0=e*q0 := hp0.trans hq0.symm
  have hp0q0 : p0=q0 := mul_left_cancel₀ he h0
  rw [hp0q0] at hp1 hp2
  have h1 : e*p1=e*q1 := by
    linear_combination hp1-hq1
  have hp1q1 : p1=q1 := mul_left_cancel₀ he h1
  rw [hp1q1] at hp2
  have h2 : e*p2=e*q2 := by
    linear_combination hp2-hq2
  exact ⟨hp0q0,hp1q1,mul_left_cancel₀ he h2⟩

/-- At `W=133225`, width 18 and the most optimistic 262143-node restriction,
the raw heterogeneous rank-nullity surplus is only 4257.  The certified
masked relation already has at least 525759 independent multiplier slots. -/
theorem endpoint_raw_gap_and_mask_capacity :
    18*(180413+(180413-131071)+(180413-133225))=4984974 ∧
    262143*19=4980717 ∧
    4984974-4980717=4257 ∧
    17*(49342-18414-1)=525759 ∧
    4257<525759 := by
  norm_num

/-- Increasing the seed width cannot make the rank-nullity certificate beat
the known masked-identity multiplier space.  Here 30927 is the worst certified
X-multiplier width after paying degree(E0)<=18414 and one exceptional node. -/
theorem every_positive_width_gap_is_swallowed (r : Nat) (hr : 18≤r) :
    r*(180413+(180413-131071)+(180413-133225))-262143*(r+1) <
      (r-1)*(49342-18414-1) := by
  norm_num
  omega

/-- Removing a polynomial-factor identity from the actual weighted source is
literally the already-formal first power-band cut.  Thus such a quotient does
not create a free dimension refund: all recovered dimensions are charged by
the same `stageBand` used by the deflation/helper analysis. -/
theorem first_identity_quotient_pays_stageBand
    {K : Type*} [Field K]
    (V : Submodule K (Poly4 K)) (F : Poly4 K)
    (B W D delta : Nat) (hW : 0<W)
    (hV : V≤weightedCoefficientBox K B W D) (hF : F≠0)
    (hidentity : ∀ G∈V, F∣G) :
    Module.finrank K V ≤
      stageBand B W D (mainDegree W F) (derivativeDegree F) delta 0+
        Module.finrank K (powerStage V F B W D delta 1) := by
  have hdiv : ∀ G∈powerStage V F B W D delta 0, F∣G := by
    intro G hG
    have hstage : powerStage V F B W D delta 0=V :=
      powerStage_zero V F B W D delta hV
    rw [hstage] at hG
    exact hidentity G hG
  have hstep := powerStage_finrank_step V F B W D delta 0 hW hV hF hdiv
  have hstage : powerStage V F B W D delta 0=V :=
    powerStage_zero V F B W D delta hV
  rw [hstage] at hstep
  simpa only [Nat.zero_add] using hstep

#print axioms affine_identity_allows_arbitrary_second_jet
#print axioms affine_identity_second_jet_unique
#print axioms endpoint_raw_gap_and_mask_capacity
#print axioms every_positive_width_gap_is_swallowed
#print axioms first_identity_quotient_pays_stageBand

end
end ProximityPrize.SubmissionLower.IdentityQuotientWeightedSourceStop6900
