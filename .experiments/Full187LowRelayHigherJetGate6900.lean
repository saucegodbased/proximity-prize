import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full187 staggered low relays: order-two/order-three V-sector gate

For `57 <= n <= 60`, put

`R_n = q_n * L^(60-n) * (U*V^n - H^3*Z*V^(n-2)*J1)`.

Each bracket cancels at the pure seed.  At an error its `H=0` reduction is
an independently CRT-controllable multiple of `V^n`.  This file records the
exact binomial-moment calculations in the literal local value coordinate

`V = 1 + E + T*R - T^2*S/2`.

The two original degrees 60 and 59 match value and the linear `E,T*R` jets,
but leave the nonzero `T^2*R^2` coefficient -1711.  Adding degree 58 kills
the complete V-sector through horizontal order two.  Adding degree 57 kills
the V-sector through horizontal order three.  The remaining issue is the
Hermite behaviour of the degree-<e CRT representatives and the `H^3*J1`
tail, neither of which is represented as an axiom here.
-/

namespace ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900

set_option autoImplicit false

/-- The original two relay amplitudes are forced by value and linear jet
matching, but their second binomial moment is nonzero. -/
theorem two_relay_order_two_obstruction :
    (-58 : Int) + 59 = 1 ∧
      (-58 : Int) * 60 + 59 * 59 = 1 ∧
      (-58 : Int) * 1770 + 59 * 1711 = -1711 ∧
      (-1711 : Int) ≠ 0 := by
  norm_num

/-- The degree-58 relay is the unique next binomial actuator needed for the
complete horizontal order-two V-sector.  The columns are ordered 60,59,58;
the three displayed moments are coefficients of `(V-1)^k`, `k=0,1,2`. -/
theorem three_relay_order_two_solution :
    (1653 : Int) - 3363 + 1711 = 1 ∧
      (1653 : Int) * 60 - 3363 * 59 + 1711 * 58 = 1 ∧
      (1653 : Int) * 1770 - 3363 * 1711 + 1711 * 1653 = 0 ∧
      (1653 : Int) * 34220 - 3363 * 32509 + 1711 * 30856 = 32509 := by
  norm_num

/-- The degree-57 relay is the last source-legal member of this staggered
binomial ladder.  These Lagrange amplitudes reproduce the value coordinate
through cubic order: their moments against `choose(n,k)` are
`(1,1,0,0)` for `k=0,1,2,3`. -/
theorem four_relay_order_three_solution :
    (-30856 : Int) + 94164 - 95816 + 32509 = 1 ∧
      (-30856 : Int) * 60 + 94164 * 59 - 95816 * 58 + 32509 * 57 = 1 ∧
      (-30856 : Int) * 1770 + 94164 * 1711 - 95816 * 1653 + 32509 * 1596 = 0 ∧
      (-30856 : Int) * 34220 + 94164 * 32509 - 95816 * 30856 +
        32509 * 29260 = 0 ∧
      (-30856 : Int) * 487635 + 94164 * 455126 - 95816 * 424270 +
        32509 * 395010 = -455126 := by
  norm_num

/-- Exact source ledger for the two new blocks.  The first two pairs are
the lead (`U*V^n`) and shifted (`H^3*Z*V^(n-2)*J1`) rows respectively. -/
theorem staggered_relay_literal_strip_ledger :
    704699 < 983158 ∧ 687749 < 966208 ∧
      983158 - 704699 = 278459 ∧ 966208 - 687749 = 278459 ∧
    885112 < 966207 ∧ 868162 < 949257 ∧
      966207 - 885112 = 81095 ∧ 949257 - 868162 = 81095 ∧
    ¬ (1065525 < 949256) ∧ ¬ (1048575 < 932306) ∧
      1065525 - 949256 = 116269 ∧ 1048575 - 932306 = 116269 := by
  norm_num

/-! Both new brackets are literal pure-seed identities.  They are stated
over an arbitrary commutative ring, so no generic-rank hypothesis enters the
endpoint cancellation. -/
section PureSeed

variable {K : Type*} [CommRing K]

theorem relay_58_pure_seed_cancel (L H U Z : K) :
    L ^ 2 * (U * (-(H ^ 2 * Z)) ^ 58 -
      H ^ 3 * Z * (-(H ^ 2 * Z)) ^ 56 * (H * U * Z)) = 0 := by
  ring

theorem relay_57_pure_seed_cancel (L H U Z : K) :
    L ^ 3 * (U * (-(H ^ 2 * Z)) ^ 57 -
      H ^ 3 * Z * (-(H ^ 2 * Z)) ^ 55 * (H * U * Z)) = 0 := by
  ring

/-- At a simple error, `J1=L*W-L'*V` has horizontal-order-zero part
`-L' + L*R`.  This is the complete contribution of the subtracted binomial
row at contact weight three: it has only pure `T^3` and `T^3*R` components,
never `T^2*R^2`, `T^3*R*S`, or `T^3*R^3`. -/
theorem cubic_J1_tail_components (a h L L1 R T : K) :
    -a * (h * T) ^ 3 * (-L1 + L * R) =
      (a * h ^ 3 * L1) * T ^ 3 -
        (a * h ^ 3 * L) * T ^ 3 * R := by
  ring

end PureSeed

end ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900

#print axioms ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900.two_relay_order_two_obstruction
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900.three_relay_order_two_solution
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900.four_relay_order_three_solution
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900.staggered_relay_literal_strip_ledger
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900.relay_58_pure_seed_cancel
#print axioms ProximityPrize.SubmissionLower.Full187LowRelayHigherJetGate6900.cubic_J1_tail_components
