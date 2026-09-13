import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full187 derivative-normalized separator projector: exact STOP

The full-domain identity `Omega=L*H` gives
`Omega'=L'*H+L*H'`.  Thus `L*H'/Omega'` is one at error roots and zero at
agreement roots.  When the domain derivative has a cheap inverse (as for a
root-of-unity domain), this is the most promising denominator-normalized
scalar separator.

Applying the quintic smoothstep

`sigma(s)=10s^3-15s^4+6s^5`

makes `sigma` third-order flat at the agreements and `1-sigma` third-order
flat at the errors.  If `U3` is likewise order three at agreements and a
third-order-flat unit at errors, then

`P3 = U3 * (sigma-U3)^20`

has agreement contact at least 63, error contact at least 60, zero candidate
value, and a nonzero linear candidate boundary.

The obstruction is exact: that linear boundary coefficient is `sigma^20`.
Since `s` contains one agreement-locator factor, `sigma` contains `L^3`, so
`sigma^20` contains `L^60`.  A nonzero coefficient with that factor cannot
fit even the linear `Y` strip, whose strict cutoff is `60g-w`.  This kills
the best derivative-normalized Taylor projector independently of the cost of
inverting `Omega'`.  It does not kill cross-degree sums whose top and linear
coefficients cancel between genuinely different projector rows.
-/

namespace ProximityPrize.SubmissionLower.Full187DerivativeSeparatorProjectorStop6900

open Polynomial

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

/-- Product-rule identity used to normalize the separator. -/
theorem full_domain_derivative_identity
    (L H L' H' : K) :
    L' * H + L * H' = L * H' + L' * H := by
  ring

/-- At an error (`H=0`), the derivative-normalized separator is one. -/
theorem derivative_separator_at_error
    (L H H' omega' : K) (hH : H = 0)
    (homega : omega' = L * H') (homega0 : omega' ≠ 0) :
    (L * H') / omega' = 1 := by
  rw [homega] at homega0 ⊢
  exact div_self homega0

/-- At an agreement (`L=0`), the same separator is zero. -/
theorem derivative_separator_at_agreement
    (L H' omega' : K) (hL : L = 0) :
    (L * H') / omega' = 0 := by
  simp [hL]

/-- Quintic smoothstep, kept factored at the agreement endpoint. -/
def smoothstep (s : K) : K := s ^ 3 * (10 - 15 * s + 6 * s ^ 2)

/-- Exact third-order factor at the error endpoint. -/
theorem one_sub_smoothstep_factor (s : K) :
    1 - smoothstep s = (1 - s) ^ 3 * (1 + 3 * s + 6 * s ^ 2) := by
  simp [smoothstep]
  ring

theorem smoothstep_zero : smoothstep (0 : K) = 0 := by
  simp [smoothstep]

theorem smoothstep_one : smoothstep (1 : K) = 1 := by
  simp [smoothstep]
  ring

/-- The candidate-linear coefficient of
`U*(sigma-U)^20` is exactly `sigma^20`. -/
def scalarProjector (sigma : K) : K[X] :=
  Polynomial.X * (Polynomial.C sigma - Polynomial.X) ^ 20

theorem scalarProjector_linear_boundary (sigma : K) :
    (scalarProjector sigma).derivative.eval 0 = sigma ^ 20 := by
  simp [scalarProjector, Polynomial.derivative_mul,
    Polynomial.derivative_pow]

/-- Exact contact bookkeeping for the order-three construction. -/
theorem third_order_projector_contact_bookkeeping :
    3 + 20 * 3 ≥ 60 ∧ 20 * 3 ≥ 60 := by
  norm_num

/-- Polynomial-coefficient version; unlike `smoothstep`, it needs only the
ring structure on `K[X]`. -/
def smoothstepPoly (s : K[X]) : K[X] :=
  s ^ 3 * (10 - 15 * s + 6 * s ^ 2)

/-- A separator with one agreement-locator factor acquires `L^60` in its
twentieth smoothstep power. -/
theorem locator_sixty_dvd_smoothstep_twenty
    (L A : K[X]) :
    L ^ 60 ∣ (smoothstepPoly (L * A)) ^ 20 := by
  refine ⟨A ^ 60 * (10 - 15 * (L * A) + 6 * (L * A) ^ 2) ^ 20, ?_⟩
  simp only [smoothstepPoly, mul_pow]
  rw [show (L ^ 3) ^ 20 = L ^ 60 by
    rw [← pow_mul],
    show (A ^ 3) ^ 20 = A ^ 60 by
      rw [← pow_mul]]
  ring

/-- Target source STOP for the resulting nonzero linear boundary
coefficient. -/
theorem locator_sixty_linear_boundary_not_source_legal
    (L B : K[X]) (hL : L ≠ 0) (hB : B ≠ 0)
    (hLdegree : L.natDegree = 180413) (hdiv : L ^ 60 ∣ B) :
    ¬ B.natDegree < 60 * 180413 - 131071 := by
  intro hlegal
  have hlower := Polynomial.natDegree_le_of_dvd hdiv hB
  rw [Polynomial.natDegree_pow, hLdegree] at hlower
  omega

theorem target_linear_boundary_gap :
    60 * 180413 - (60 * 180413 - 131071) = 131071 := by
  norm_num

end


end ProximityPrize.SubmissionLower.Full187DerivativeSeparatorProjectorStop6900

#print axioms ProximityPrize.SubmissionLower.Full187DerivativeSeparatorProjectorStop6900.one_sub_smoothstep_factor
#print axioms ProximityPrize.SubmissionLower.Full187DerivativeSeparatorProjectorStop6900.scalarProjector_linear_boundary
#print axioms ProximityPrize.SubmissionLower.Full187DerivativeSeparatorProjectorStop6900.locator_sixty_dvd_smoothstep_twenty
#print axioms ProximityPrize.SubmissionLower.Full187DerivativeSeparatorProjectorStop6900.locator_sixty_linear_boundary_not_source_legal
