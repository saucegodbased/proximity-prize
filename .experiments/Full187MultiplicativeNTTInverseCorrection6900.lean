import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Full187 multiplicative-NTT inverse correction

The target evaluation domain is multiplicative, so its full locator is
`X^N - 1`; its derivative is not constant.  If `L*H=X^N-1`, the natural
polynomial inverse of `L` modulo `H` is

`A = N⁻¹ * X * H'`.

This file records the exact identity.  In particular `deg A = deg H` in the
generic target situation, one degree larger than the additive/constant-
derivative surrogate `H'`.  Every earlier endpoint impossibility proved with
the optimistic degree `deg H - 1` remains valid (and is strengthened), but
the surrogate inverse itself must not be used as a target construction.
-/

namespace ProximityPrize.SubmissionLower.Full187MultiplicativeNTTInverseCorrection6900

open Polynomial

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K]

/-- Exact Bezout identity behind the inverse on a multiplicative domain. -/
theorem multiplicative_domain_inverse_identity
    (L H : K[X]) (N : Nat) (hN : (N : K) ≠ 0)
    (hfull : L * H = X ^ N - 1) :
    1 - L * (C (N : K)⁻¹ * X * H.derivative) =
      H * (-L + C (N : K)⁻¹ * X * L.derivative) := by
  have hderiv := congrArg Polynomial.derivative hfull
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, sub_zero, Polynomial.derivative_pow,
    Polynomial.derivative_X, mul_one] at hderiv
  have hNnat : N ≠ 0 := by
    intro hzero
    subst N
    simp at hN
  have hxpow : X * X ^ (N - 1) = (X : K[X]) ^ N := by
    nth_rewrite 2 [show N = (N - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hscaled :
      C (N : K)⁻¹ * X * (L * H).derivative = (X : K[X]) ^ N := by
    rw [Polynomial.derivative_mul, hderiv]
    calc
      C (N : K)⁻¹ * X * (C (N : K) * X ^ (N - 1)) =
          (C (N : K)⁻¹ * C (N : K)) *
            (X * X ^ (N - 1)) := by ring
      _ = (X : K[X]) ^ N := by
        rw [← C_mul, inv_mul_cancel₀ hN, C_1, one_mul, hxpow]
  calc
    1 - L * (C (N : K)⁻¹ * X * H.derivative) =
        1 - C (N : K)⁻¹ * X * (L * H.derivative) := by ring
    _ = 1 - C (N : K)⁻¹ * X *
          ((L * H).derivative - L.derivative * H) := by
            rw [Polynomial.derivative_mul]
            ring
    _ = H * (-L + C (N : K)⁻¹ * X * L.derivative) := by
      rw [mul_sub, hscaled]
      have homega : 1 - (X : K[X]) ^ N = -(L * H) := by
        rw [hfull]
        ring
      rw [show 1 - ((X : K[X]) ^ N -
          C (N : K)⁻¹ * X * (L.derivative * H)) =
          (1 - (X : K[X]) ^ N) +
            C (N : K)⁻¹ * X * (L.derivative * H) by ring,
        homega]
      ring

/-- Therefore `N⁻¹ X H'` is an inverse of `L` modulo the error locator. -/
theorem multiplicative_domain_inverse_mod_error
    (L H : K[X]) (N : Nat) (hN : (N : K) ≠ 0)
    (hfull : L * H = X ^ N - 1) :
    H ∣ 1 - L * (C (N : K)⁻¹ * X * H.derivative) := by
  refine ⟨-L + C (N : K)⁻¹ * X * L.derivative, ?_⟩
  exact multiplicative_domain_inverse_identity L H N hN hfull

/-- With the actual multiplicative-domain inverse degree `e`, the relaxed
endpoint system remains impossible.  The global arithmetic minimum is the
corner `(a+r,s+r)=(60,66)` with `r=0`, whose deficit is `3,785,094`.
This also corrects a larger non-sharp number recorded in one exploratory
fixed-degree note. -/
theorem actual_inverse_endpoint_gap
    (a r s : Nat) (hcontact : 60 ≤ a + r) (hcap : s + r ≤ 66) :
    16951 * s + 3785094 ≤ 81731 * a + 81731 * r := by
  omega

theorem actual_inverse_endpoint_gap_sharp :
    81731 * 60 - 16951 * 66 = 3785094 := by
  norm_num

theorem no_actual_inverse_packet_endpoint
    (a r s : Nat) (hcontact : 60 ≤ a + r) (hcap : s + r ≤ 66) :
    ¬ 81731 * a + 81731 * r < 16951 * s := by
  intro hlegal
  have hgap := actual_inverse_endpoint_gap a r s hcontact hcap
  omega

end

end ProximityPrize.SubmissionLower.Full187MultiplicativeNTTInverseCorrection6900

#print axioms ProximityPrize.SubmissionLower.Full187MultiplicativeNTTInverseCorrection6900.multiplicative_domain_inverse_identity
#print axioms ProximityPrize.SubmissionLower.Full187MultiplicativeNTTInverseCorrection6900.multiplicative_domain_inverse_mod_error
#print axioms ProximityPrize.SubmissionLower.Full187MultiplicativeNTTInverseCorrection6900.no_actual_inverse_packet_endpoint
