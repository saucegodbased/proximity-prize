import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Full187 fixed-degree cross-packet endpoint STOP

This closes a strictly larger class than the single inverse packet gate.
Fix one error-locator stratum `H^a` and one homogeneous normal degree `n`.
Allow an arbitrary linear combination of all Bernstein/inverse packets in
that degree.  After cancellation, let `j` be the first surviving power at
the agreement endpoint and let `r` be its vanishing order at the error
endpoint.  A nonzero degree-`n` polynomial with these two endpoint orders
has `j+r <= n`.  Error contact 60 requires `a+r >= 60`.

Homogenizing the packet with the natural error unit `L*A`, where
`A=c^-1 H'`, makes the first surviving `V^j` coefficient contain at least
`H^a A^(n-j)`.  Since `deg H=81731`, `deg A=81730`, and the literal
pure-seed residual allowance is only `16951*j`, this coefficient cannot be
source legal, even with the relaxed cap `n <= 66`.

The scope is exact: coefficients from different `H`-adic strata or different
homogeneous degrees can still cancel after reduction modulo powers of `H`.
Those genuinely mixed Hermite/Popov packets are not excluded here.
-/

namespace ProximityPrize.SubmissionLower.Full187FixedDegreeCrossPacketEndpointStop6900

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- Two distinct endpoint factors consume the sum of their multiplicities. -/
theorem two_endpoint_orders_fit_degree
    (P : K[X]) (j r n : Nat) (hP : P ≠ 0)
    (hdiv : X ^ j * (X - 1) ^ r ∣ P)
    (hdeg : P.natDegree ≤ n) :
    j + r ≤ n := by
  have hfactor : X ^ j * (X - 1) ^ r ≠ (0 : K[X]) := by
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero)
      (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : K)))
  have hle := Polynomial.natDegree_le_of_dvd hdiv hP
  have hdegree : (X ^ j * (X - 1) ^ r : K[X]).natDegree = j + r := by
    rw [Polynomial.natDegree_mul
      (pow_ne_zero _ X_ne_zero)
      (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : K))),
      Polynomial.natDegree_pow, Polynomial.natDegree_pow]
    rw [show (X - 1 : K[X]).natDegree = 1 by
      simpa using natDegree_X_sub_C (1 : K)]
    simp
  rw [hdegree] at hle
  omega

/-- Target arithmetic for every surviving endpoint in a common-stratum,
fixed-degree cross-packet sum. -/
theorem no_fixed_degree_cross_packet_endpoint
    (a j r n : Nat)
    (hcontact : 60 ≤ a + r)
    (hendpoints : j + r ≤ n)
    (hcap : n ≤ 66) :
    ¬ a * 81731 + (n - j) * 81730 < 16951 * j := by
  omega

/-- Polynomial form of the same tight-facet obstruction. -/
theorem fixed_degree_cross_packet_multiplier_not_source_legal
    (H A : K[X]) (a j r n : Nat)
    (hH : H ≠ 0) (hA : A ≠ 0)
    (hHdegree : H.natDegree = 81731)
    (hAdegree : A.natDegree = 81730)
    (hcontact : 60 ≤ a + r)
    (hendpoints : j + r ≤ n)
    (hcap : n ≤ 66) :
    ¬ (H ^ a * A ^ (n - j)).natDegree < 16951 * j := by
  intro hlegal
  rw [Polynomial.natDegree_mul (pow_ne_zero _ hH) (pow_ne_zero _ hA),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    hHdegree, hAdegree] at hlegal
  exact no_fixed_degree_cross_packet_endpoint a j r n
    hcontact hendpoints hcap hlegal

/-- The best numerical corner is still very far outside the strip: taking
all six relaxed excess degrees at the agreement endpoint leaves a gap of
millions. -/
theorem best_relaxed_corner_gap :
    60 * 81730 - 6 * 16951 = 4802094 := by
  norm_num

end

end ProximityPrize.SubmissionLower.Full187FixedDegreeCrossPacketEndpointStop6900

#print axioms ProximityPrize.SubmissionLower.Full187FixedDegreeCrossPacketEndpointStop6900.two_endpoint_orders_fit_degree
#print axioms ProximityPrize.SubmissionLower.Full187FixedDegreeCrossPacketEndpointStop6900.no_fixed_degree_cross_packet_endpoint
#print axioms ProximityPrize.SubmissionLower.Full187FixedDegreeCrossPacketEndpointStop6900.fixed_degree_cross_packet_multiplier_not_source_legal
