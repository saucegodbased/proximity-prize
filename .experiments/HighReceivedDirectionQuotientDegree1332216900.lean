import LowReceivedDirectionScalarSplit1332216900

/-!
# Exact quotient-degree handoff from the degree-133221 scalar split

`LowReceivedDirectionScalarSplit1332216900` leaves the branch in which the
global received-direction interpolant has degree at least `133222`.  After
subtracting a code-degree anchor and dividing by its degree-`131072` locator,
the residual quotient consequently has degree at least `2150`.
-/

namespace ProximityPrize.SubmissionLower.HighReceivedDirectionQuotientDegree1332216900

open Polynomial

set_option autoImplicit false
set_option Elab.async false

noncomputable section

variable {K : Type} [Field K]

theorem quotient_degree_ge_2150
    (U q Lambda T : K[X])
    (hU : 133222 ≤ U.natDegree)
    (hq : q.natDegree ≤ 131071)
    (hLambda : Lambda.natDegree = 131072)
    (hfactor : U - q = Lambda * T) :
    2150 ≤ T.natDegree := by
  have hqU : q.natDegree < U.natDegree := by omega
  have hsub : (U - q).natDegree = U.natDegree :=
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt hqU
  have hLne : Lambda ≠ 0 := by
    intro hz
    simp [hz] at hLambda
  have hsubne : U - q ≠ 0 := by
    intro hz
    have hzdeg : (U - q).natDegree = 0 := by simp [hz]
    rw [hsub] at hzdeg
    omega
  have hTne : T ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfactor
    exact hsubne hfactor
  have hmul : (Lambda * T).natDegree =
      Lambda.natDegree + T.natDegree :=
    Polynomial.natDegree_mul hLne hTne
  rw [hfactor] at hsub
  rw [hmul, hLambda] at hsub
  omega

end

end ProximityPrize.SubmissionLower.HighReceivedDirectionQuotientDegree1332216900

#print axioms ProximityPrize.SubmissionLower.HighReceivedDirectionQuotientDegree1332216900.quotient_degree_ge_2150
