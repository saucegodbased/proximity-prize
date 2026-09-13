import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full187 high-`V` inverse packet: endpoint STOP

This file audits one tempting way to turn the surviving high-`V` layers into
an error-flat construction.  Write `L` for the agreement locator, `H` for the
error locator, and suppose the full-domain locator has constant derivative:

`(L * H)' = c`.

Then `A = c⁻¹ H'` is an inverse to `L` modulo `H`.  Thus packets of the form

`H^a L^(60-s-r) V^s (V-LA)^r`

look attractive: at an error, `LA=1 mod H`, so both `H` and `V-LA` provide
first-order contact.  Unfortunately the coefficient at the *low* `V`
endpoint contains `H^a A^r`.  With the literal Full187 degrees
`deg H=81731`, `deg A=81730`, its degree cannot fit the source allowance
`16951*s`, even under the relaxed total-`V` cap `s+r <= 66`.

This is deliberately a single-packet gate.  It does **not** exclude a linear
combination whose low-`V` endpoints cancel across several packets, nor a
higher-Hermite inverse represented by different polynomials.
-/

namespace ProximityPrize.SubmissionLower.Full187HighVInversePacketEndpointStop6900

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- The full-domain derivative identity really supplies the advertised
inverse of `L` modulo `H`. -/
theorem derivative_inverse_mod_error
    (L H : K[X]) (c : K) (hc : c ≠ 0)
    (hfull : (L * H).derivative = C c) :
    H ∣ 1 - L * (C c⁻¹ * H.derivative) := by
  refine ⟨C c⁻¹ * L.derivative, ?_⟩
  have hcunit : C c⁻¹ * C c = (1 : K[X]) := by
    rw [← C_mul]
    simp [hc]
  calc
    1 - L * (C c⁻¹ * H.derivative) =
        C c⁻¹ * (C c - L * H.derivative) := by
          rw [← hcunit]
          ring
    _ = C c⁻¹ * ((L * H).derivative - L * H.derivative) := by
          rw [hfull]
    _ = H * (C c⁻¹ * L.derivative) := by
          rw [Polynomial.derivative_mul]
          ring

/-- Exact target arithmetic: no nonnegative triple can simultaneously buy
60 first-order contact units, stay below even the relaxed degree-66 `V` cap,
and fit the low-`V` source endpoint after paying for `H^a A^r`. -/
theorem no_inverse_packet_endpoint_triple
    (a r s : Nat)
    (hcontact : 60 ≤ a + r)
    (hcap : s + r ≤ 66) :
    ¬ a * 81731 + r * 81730 < 16951 * s := by
  omega

/-- The same gate in the polynomial form needed by a literal construction.
The degree hypotheses are exactly those of the natural representative
`A=c⁻¹H'` for a degree-81731 squarefree error locator. -/
theorem inverse_packet_low_V_endpoint_not_source_legal
    (H A : K[X]) (a r s : Nat)
    (hH : H ≠ 0) (hA : A ≠ 0)
    (hHdegree : H.natDegree = 81731)
    (hAdegree : A.natDegree = 81730)
    (hcontact : 60 ≤ a + r)
    (hcap : s + r ≤ 66) :
    ¬ (H ^ a * A ^ r).natDegree < 16951 * s := by
  intro hlegal
  rw [Polynomial.natDegree_mul (pow_ne_zero _ hH) (pow_ne_zero _ hA),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    hHdegree, hAdegree] at hlegal
  exact no_inverse_packet_endpoint_triple a r s hcontact hcap hlegal

/-- The corrected high-`V` bifiltration starts being source-positive at
`b=19`, not `b=20`.  This records the exact two sides of that threshold. -/
theorem pure_V_error_charge_threshold :
    16951 * 18 - (60 - 3 * 18) * 81731 = 0 /\
      490386 - 305118 = 185268 /\
      16951 * 19 - (60 - 3 * 19) * 81731 = 76876 /\
      16951 * 20 - (60 - 3 * 20) * 81731 = 339020 := by
  norm_num

/-- A compact ledger for the two packet endpoints.  The high-`V` endpoint
only pays `H^a`; the low-`V` endpoint pays the fatal `H^a A^r`. -/
theorem inverse_packet_two_endpoint_multiplier_degrees
    (a r : Nat) :
    a * 81731 ≤ a * 81731 + r * 81730 /\
      (a * 81731 + r * 81730) - a * 81731 = r * 81730 := by
  omega

end

end ProximityPrize.SubmissionLower.Full187HighVInversePacketEndpointStop6900

#print axioms ProximityPrize.SubmissionLower.Full187HighVInversePacketEndpointStop6900.derivative_inverse_mod_error
#print axioms ProximityPrize.SubmissionLower.Full187HighVInversePacketEndpointStop6900.no_inverse_packet_endpoint_triple
#print axioms ProximityPrize.SubmissionLower.Full187HighVInversePacketEndpointStop6900.inverse_packet_low_V_endpoint_not_source_legal
#print axioms ProximityPrize.SubmissionLower.Full187HighVInversePacketEndpointStop6900.pure_V_error_charge_threshold
