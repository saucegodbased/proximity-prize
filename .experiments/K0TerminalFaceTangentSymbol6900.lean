import K0SRTinyContactCore6900
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Terminal active-face tangent symbol for the k0 source

For a degree-`w` candidate with leading jet `(Y,R) = (p,w*p)` and a
degree-`w+1` agreement tangent with leading jet
`(lambdaY,lambdaR) = (q,(w+1)*q)`, the two adjacent terminal monomials

```
X^A * Y^(U-1) * R,       X^(A-1) * Y^U
```

have cancelling candidate leading symbols, while their tangent leading
symbols differ by exactly `q*p^(U-1)`.  This file proves the literal m8 and
target instances, as well as membership in the corresponding raw source.

These are principal-symbol identities only.  They do not construct a
global contact-kernel relation whose lower terms complete the two-term
symbol.  In fact a much lower source column already has a candidate-free
nonzero tangent symbol; the final section records this explicit
non-sufficiency guard.
-/

namespace ProximityPrize.SubmissionLower.K0TerminalFaceTangentSymbol6900

open K0SRTinyContactCore6900

noncomputable section
set_option autoImplicit false
set_option Elab.async false

variable {K : Type*} [Field K]

/-- General Euler-defect identity behind the terminal pair.  The base leading
jet has `R=w*Y`, whereas a degree-`w+1` tangent has
`lambdaR=(w+1)*lambdaY`; their one-unit discrepancy survives after the two
candidate symbols cancel. -/
theorem terminal_euler_defect
    (p q gamma : K) (w n : Nat) :
    rawBoundaryScalar 0 p ((w : K) * p) gamma
        0 q (((w + 1 : Nat) : K) * q) 0 0 (n + 1) 1 0 -
      (w : K) * rawBoundaryScalar 0 p ((w : K) * p) gamma
        0 q (((w + 1 : Nat) : K) * q) 0 0 (n + 2) 0 0 =
      q * p ^ (n + 1) := by
  simp [rawBoundaryScalar, pow_succ]
  ring

/-! ## Cubic/quartic m8 identity -/

/-- On the candidate leading jet, the two m8 terminal symbols cancel. -/
theorem m8_terminal_candidate_symbol_cancel (p : K) :
    p ^ 11 * (3 * p) - 3 * p ^ 12 = 0 := by
  ring

/-- The same two symbols have unit Euler defect in the quartic tangent
direction.  `rawBoundaryScalar` is the literal four-gradient pairing; the
`S` and `Z` coordinates are irrelevant because both shapes have `s=z=0`. -/
theorem m8_terminal_tangent_symbol_unit (p q gamma : K) :
    rawBoundaryScalar (6 * p) p (3 * p) gamma
        (12 * q) q (4 * q) 1 0 11 1 0 -
      3 * rawBoundaryScalar (6 * p) p (3 * p) gamma
        (12 * q) q (4 * q) 1 0 12 0 0 =
      q * p ^ 11 := by
  simp [rawBoundaryScalar]
  ring

/-- Both terms occupy the active-total-12, passive-`z=0` face and use their
last legal X coefficient when `(D,w,L,B,s,U)=(48,3,12,3,1,12)`. -/
theorem m8_terminal_pair_legal_at_L12 :
    rawShapeLegal 48 3 12 3 1 12 12 0 11 1 0 ∧
      rawShapeLegal 48 3 12 3 1 12 11 0 12 0 0 := by
  norm_num [rawShapeLegal]

/-- The identical two terminal shapes are absent from the truncated L10
source. -/
theorem m8_terminal_pair_absent_at_L10 :
    ¬ rawShapeLegal 48 3 10 3 1 12 12 0 11 1 0 ∧
      ¬ rawShapeLegal 48 3 10 3 1 12 11 0 12 0 0 := by
  norm_num [rawShapeLegal]

/-! ## Exact target-scaled identity -/

/-- Target analogue of the candidate-symbol cancellation, with
`w=131071` and `U=64`. -/
theorem target_terminal_candidate_symbol_cancel (p : K) :
    p ^ 63 * (131071 * p) - 131071 * p ^ 64 = 0 := by
  ring

/-- The target terminal pair sees the leading coefficient `q` of a
degree-`w+1` tangent.  The huge constants are only the literal leading
coefficients of the first derivatives; the identity is characteristic-free.
-/
theorem target_terminal_tangent_symbol_unit (p q gamma : K) :
    rawBoundaryScalar (131071 * 131070 * p) p (131071 * p) gamma
        (131071 * 131072 * q) q (131072 * q) 1 0 63 1 0 -
      131071 * rawBoundaryScalar
        (131071 * 131070 * p) p (131071 * p) gamma
        (131071 * 131072 * q) q (131072 * q) 1 0 64 0 0 =
      q * p ^ 63 := by
  simp [rawBoundaryScalar]
  ring

/-- Exact raw-source legality of
`X^90867*Y^63*R - 131071*X^90866*Y^64` at the 6900 k0 target. -/
theorem target_terminal_pair_legal :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        90867 0 63 1 0 ∧
      rawShapeLegal (47 * 180413) 131071 3757 16 8 64
        90866 0 64 0 0 := by
  norm_num [rawShapeLegal]

/-! ## All six m8 derivative-budget shapes on the terminal face -/

/-- Integer leading-tangent weight after extracting `q*p^(y+r+s-1)` from
an m8 shape.  This avoids division by `3` or `6` and remains meaningful in
every characteristic. -/
def m8TerminalTangentWeight (y r s : Nat) : Nat :=
  y * 3 ^ r * 6 ^ s +
    r * 4 * 3 ^ (r - 1) * 6 ^ s +
    s * 12 * 3 ^ r * 6 ^ (s - 1)

/-- The weights of the six active-total-12, `z=0` shapes
`(y,r,s)=(12,0,0),(11,1,0),(10,2,0),(9,3,0),(11,0,1),(10,1,1)`.
All are nonzero modulo the audit characteristic 101. -/
theorem m8_terminal_face_tangent_weights :
    m8TerminalTangentWeight 12 0 0 = 12 ∧
    m8TerminalTangentWeight 11 1 0 = 37 ∧
    m8TerminalTangentWeight 10 2 0 = 114 ∧
    m8TerminalTangentWeight 9 3 0 = 351 ∧
    m8TerminalTangentWeight 11 0 1 = 78 ∧
    m8TerminalTangentWeight 10 1 1 = 240 := by
  norm_num [m8TerminalTangentWeight]

theorem m8_terminal_face_tangent_weights_nonzero_mod101 :
    12 % 101 ≠ 0 ∧ 37 % 101 ≠ 0 ∧ 114 % 101 ≠ 0 ∧
      351 % 101 ≠ 0 ∧ 78 % 101 ≠ 0 ∧ 240 % 101 ≠ 0 := by
  norm_num

/-! ## Principal-symbol non-sufficiency guard -/

/-- A single `Y` column already has candidate-independent tangent weight
`q`.  Thus a nonzero top-coefficient functional exists even when the m8
terminal face is absent; obtaining a contact-kernel vector on which it is
nonzero is the genuinely load-bearing assertion. -/
theorem single_Y_tangent_symbol
    (S0 Y0 R0 gamma lambdaS q lambdaR lambdaZ : K) :
    rawBoundaryScalar S0 Y0 R0 gamma
      lambdaS q lambdaR lambdaZ 0 1 0 0 = q := by
  simp [rawBoundaryScalar]

theorem m8_single_Y_top_column_legal_at_L10 :
    rawShapeLegal 48 3 10 3 1 12 44 0 1 0 0 := by
  norm_num [rawShapeLegal]

theorem target_single_Y_top_column_legal :
    rawShapeLegal (47 * 180413) 131071 3757 16 8 64
      8348339 0 1 0 0 := by
  norm_num [rawShapeLegal]

#print axioms m8_terminal_candidate_symbol_cancel
#print axioms terminal_euler_defect
#print axioms m8_terminal_tangent_symbol_unit
#print axioms m8_terminal_pair_legal_at_L12
#print axioms m8_terminal_pair_absent_at_L10
#print axioms target_terminal_candidate_symbol_cancel
#print axioms target_terminal_tangent_symbol_unit
#print axioms target_terminal_pair_legal
#print axioms m8_terminal_face_tangent_weights
#print axioms m8_terminal_face_tangent_weights_nonzero_mod101
#print axioms single_Y_tangent_symbol
#print axioms m8_single_Y_top_column_legal_at_L10
#print axioms target_single_Y_top_column_legal

end

end ProximityPrize.SubmissionLower.K0TerminalFaceTangentSymbol6900
