# `L >= U` filtered-strictness falsifier

## Verdict

**RED as a universal theorem.**  Exact literal F101 ranks show that reaching
the active cap `U` does not by itself make the complete passive-face
connecting obstruction vanish.  All 21 cases below have a nonzero associated
top kernel; nine retain a nonzero lower-grade obstruction.

The positive observation remains useful only conditionally: because every
successor-face monomial is divisible by `Z` once `L >= U`, and literal contact
fixes `Z`, strictness at one layer propagates to every later layer.  What this
experiment refutes is the missing base assertion that strictness is automatic
at `L = U`.

## Exact discriminator

For the complete step `L -> L+1`, the script computes

`rank(delta) = rank(full) - rank(old) - rank(top)`

over F101 using the accepted flattened contact

`Y = u0 + u1 Z + eps R - eps^2 S + eps^3 T (mod eps^m)`.

The three datum families include a polynomial off-agreement direction and two
independently generated arbitrary off-agreement directions.  A zero
obstruction is counted as evidence only when `ker(top)` is nonzero.

| profile `(n,w,g,m,B,s,U)` | polynomial direction | arbitrary varying | arbitrary alternating |
|---|---:|---:|---:|
| `(6,2,4,3,2,1,5)` | `1` | `0` | `0` |
| `(9,2,6,3,2,1,5)` | `4` | `0` | `0` |
| `(7,3,5,3,2,1,5)` | `4` | **`3`** | **`3`** |
| `(10,3,7,3,2,1,5)` | `4` | `0` | `0` |
| `(11,4,8,3,2,1,5)` | `5` | `0` | `0` |
| `(6,2,4,4,2,1,6)` | `2` | `0` | `0` |
| `(11,5,8,6,2,1,8)` | `40` | `0` | `0` |

Entries are exact connecting-obstruction ranks at old cap `L=U`.  In the
decisive arbitrary-direction counterexample `(7,3,5,3,2,1,5)`, the varying
case has

`rank(old), rank(top), rank(full) = 548, 126, 677`,

so `rank(delta)=3`, while the top kernel has dimension `146-126=20`.

This also explains why the earlier two-profile sweep looked stronger than it
was: its arbitrary `m=6` datum lies in a GREEN chamber, but a nearby valid
profile does not.  The target might still be strict for additional structural
reasons; `L/U` alone supplies none.

## Receipt

- Script: `.experiments/k0_L_ge_U_strictness_falsifier_6900.py`
- Canonical output SHA-256:
  `485999548f46fc8d49dc73aed6188b10290c5a2e2aa2f12afe3984f8de6cd6de`
- Script SHA-256:
  `c4318db895a2372f8e32e0c17567b3209ac259c576955361fab1bfe46e116cd0`
- Runtime: `176.473s`
- Peak RSS: `1,322,976 KiB`
- Address-space cap: `4,200,000,000` bytes

Boundary evaluation is not used.  This is a finite falsifier of a proposed
universal mechanism, not a target-size rank computation.
