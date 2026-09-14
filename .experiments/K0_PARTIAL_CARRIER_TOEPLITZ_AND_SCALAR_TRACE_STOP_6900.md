# k=0 partial carriers: Toeplitz factor and scalar-trace STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This note changes no
submission or production file.

## Verdict

The partial-locator packet has two exact positive results:

1. its binomial change to the full-`G` center is explicit; and
2. its local reverse-seed block has determinant exactly a positive power of
   the direction mismatch.

These facts explain the `(b-Q_G(e))^22` factor in the small nonmatched raw
minor, conditional on the missing global triangularization. They do not prove
that triangularization.

There is also a decisive target-valid STOP:

```text
arbitrary scalar error-trace / Hermite surjectivity from the
partial-locator a0/a1/a2 packet, even with all seed shifts and all anchors
                                                                    RED
```

The counterfamily has `deg Q_G=w+1`, so every anchor quotient `T_H` is the
same nonzero constant, and has the same nonzero mismatch ratio at every
error. Every `R/S` companion vanishes in the scalar passive quotient, all
seed shifts become scalar multiples, and every anchor chart has the identical
trace space

```text
Lambda_G^m * span{1,X,...,X^(m-1)}.
```

Its dimension is only `47` in the requested profile and `60` in the old
exact-`G` profile, versus `81731` errors.

This does **not** refute a rank-adaptive four-boundary Schur determinant, a
distinguished one-syndrome lift, or a recurrence using higher contact
coordinates or the complete source. Those remain open.

## 1. Exact carrier transform

Let

```text
W       = Z-gamma,
H       = Lambda_H,                 |H|=w+1,
R       = Lambda_(G\H),
Q_G-q_H = H*T,
A_h     = Y-P-W*q_H,
A_G     = Y-P-W*Q_G.
```

Then `A_h=A_G+WHT`. For `0<=k<=m`, put

```text
C_k = H^(m-k) R^m A_h^k,
D_r = (H R)^(m-r) A_G^r = Lambda_G^(m-r) A_G^r.
```

The exact identity is

```text
C_k = sum_(r=0)^k binom(k,r) R^r W^(k-r) T^(k-r) D_r.       (BIN)
```

Proof: expand `(A_G+WHT)^k`; in the `r`th term use

```text
H^(m-k) H^(k-r)=H^(m-r),
R^r R^(m-r)=R^m.
```

The identity is over an arbitrary commutative ring. It is important that
`(BIN)` is an identity of the complete legal carrier: the individual terms
containing `R^r D_r` need not obey the strict source cutoff separately.

## 2. Error contact and the exact Toeplitz determinant

At an error node `e`, define

```text
delta_e   = u0(e)+gamma*u1(e)-P(e),
epsilon_e = u1(e)-Q_G(e).
```

Maximality of the exact agreement set gives `delta_e!=0`. On the
contact-degree-zero slice,

```text
A_G |e = delta_e + epsilon_e W,
A_h |e = delta_e + (epsilon_e+H(e)T(e)) W.             (ERR)
```

Multiplication by `delta+epsilon W`, from the consecutive seed columns

```text
1,W,...,W^(n-1)
```

and projected to the next coefficients `W,...,W^n`, has matrix

```text
[ epsilon  delta       0  ... ]
[       0 epsilon   delta  ... ]
[       0       0 epsilon  ... ]
[             ...             ]
```

and therefore

```text
det M_n(delta,epsilon)=epsilon^n.                       (TOEP)
```

Factoring a common `W^z0` gives the identical matrix on every translated
consecutive seed interval. Thus the local algebra supplies exactly the
positive mismatch power sought by the nonmatched chart. In the small chamber,
`n=22` agrees with the observed factor `(b-4a)^22`.

What is still required globally is a chosen bordered contact minor whose
Schur complement, after eliminating earlier matched errors, is

```text
U * M_n(delta_i,epsilon_i) * V
```

with `U,V` invertible and all later-error terms strictly off the determinant
diagonal. Only then does `(TOEP)` prove that the raw numerator is a unit times
`epsilon_i^n`. Neither `(BIN)` nor the local block proves this Schur form.

## 3. R/S companions and termwise source caps

Use the fully centered slope and curvature variables `R_G,S_G`, and their
anchor-centered versions. Define

```text
a0 = A_h,
a1 = H R_h-H' a0,
a2 = H^2 S_h-2HH'R_h+(2(H')^2-HH'')a0.
```

Differentiating `Q_G-q_H=HT` gives the exact changes

```text
a0 = A_G+WHT,
a1 = H R_G-H'A_G + W H^2 T',
a2 = H^2 S_G-2HH'R_G+(2(H')^2-HH'')A_G + W H^3 T''.   (OSC)
```

In particular `a0,a1,a2` have anchor contact depths `1,2,3` and weighted
degrees at most `w,2w,3w`.

For

```text
d=i+2r+3s,
P_(i,r,s,j,z)=X^j W^z H^(m-d) R^m a0^i a1^r a2^s,
```

every expanded term lies in the requested source when

```text
d<=47,  r+2s<=16,  s<=8,
i+r+s<=64,  z+i+r+s<=3757,  0<=j<d.                  (CAP47)
```

Indeed its weighted X degree is exactly bounded by

```text
(m-d)(w+1)+m(g-w-1)+dw+j = mg-d+j < mg=D.
```

Each `a1` consumes at most one slope unit; each `a2` consumes at most two
slope units and one curvature unit. Every companion is linear in active
variables, so active degree is at most `i+r+s`, and expansion contributes at
most that many additional centered seeds. This proves all caps term by term.
The original `C_k` is the case `(i,r,s,j,z)=(k,0,0,0,0)`.

## 4. What the 75,888 count does and does not say

At external seed `z=0`, all legal shapes and all free X shifts give

```text
sum_(s=0)^8 sum_(r=0)^(16-2s) sum_(i=0)^(47-2r-3s)
  (i+2r+3s)
= 75888 < 81731.                                      (COUNT47)
```

Thus direct `W^0` coefficient surjectivity, or any ordered scalar-localizer
chain restricted to `z=0`, is impossible. A single shape is even more rigid:
its free multiplier has degree `<d<=47`, so it cannot vanish at the other
`81730` distinct errors and remain nonzero at the selected one.

This is **not** a dimension STOP for the full seed packet. The legal range is
`0<=z<=3757-(i+r+s)`. The number with `z>=2`, hence zero first boundary jet,
is

```text
283136910 > 81731.
```

Even the subpacket with total seed degree strictly below `3757`, which has
zero leading-coefficient trace at a matched error, has

```text
283061022 > 81731.
```

At a mismatch the one-dimensional passive quotient is evaluation at

```text
rho_e=-delta_e/epsilon_e,
```

so `W^z` contributes `rho_e^z`; it cannot be discarded by seed grading. At a
matched error `epsilon_e=0`, the quotient is instead leading-coefficient
extraction at infinity. This is why the higher seed shifts are a genuine
candidate for the mismatch recurrence even though they cannot change the
literal `W^0` coefficient.

## 5. Constant-ratio and all-anchor collapse

Higher seeds still do not yield a target-uniform Hermite theorem. If all
finite mismatch ratios equal one constant `rho`, the external seed copies of
any fixed trace vector are merely the scalar multiples `rho^z v`.

An adjacent anchor swap does not force variation. If

```text
q_1-q_0=c Lambda_S
```

for the shared `w`-node locator, choose on each error

```text
delta=Lambda_S,
u1-q_0=a Lambda_S,
u1-q_1=(a-c)Lambda_S,
```

with `a!=0,c`. Both chart ratios are constant:

```text
rho_0=-1/a,             rho_1=-1/(a-c).
```

There is a stronger all-anchor target family. Choose `Q_G` of exact degree
`w+1`, with leading coefficient `c!=0`. For every anchor `H`, the polynomial

```text
Q_G-c Lambda_H
```

has degree at most `w` and agrees with `Q_G` on `H`; uniqueness gives

```text
q_H=Q_G-c Lambda_H,       T_H=(Q_G-q_H)/Lambda_H=c.    (CONST-T)
```

This direction is genuinely retained bad on `G`, because a degree-`<=w`
polynomial cannot agree with degree-`w+1` `Q_G` at more than `w+1` nodes.
On every error set

```text
epsilon_e=1,       delta_e=-rho,       rho!=0;
```

choose `u0` accordingly. Then every outside node is a genuine error and
every local mismatch block is nonsingular.

On the full-centered scalar quotient put `A_G=R_G=S_G=0` and `W=rho`.
Equation `(OSC)` becomes

```text
a0=WHT,        a1=W H^2 T',        a2=W H^3 T''.
```

Therefore the exact scalar trace of `P_(i,r,s,j,z)` at an error `x` is

```text
Lambda_G(x)^m X(x)^j rho^(z+i+r+s)
  * T_H(x)^i * T_H'(x)^r * T_H''(x)^s.                (TRACE)
```

Under `(CONST-T)`, every trace with `r+s>0` is zero. The remaining traces
have `r=s=0` and `j<i<=m`, so every seed and every anchor lies in

```text
Lambda_G^m * span{1,X,...,X^(m-1)}.                   (COLLAPSE)
```

The diagonal `Lambda_G(x)^m` is nonzero on errors. Hence `(COLLAPSE)` has
dimension exactly `m` when there are at least `m` distinct errors. This
proves the announced scalar-Hermite STOP for the entire packet, not merely
for `z=0`.

## 6. Comparison with the old exact-G m60 profile

The same algebra and source proof apply to

```text
(m,B,s,U,L,D)=(60,21,10,82,2703,60g).
```

Even the conservative legal subpacket `r+2s<=21` has unshifted count

```text
197824 > 81731.
```

So m60 has no nominal constant-seed capacity deficit. Nevertheless the
degree-`w+1` family above collapses every anchor chart to dimension at most
`60`; it does not repair uniform scalar Hermite localization.

The old m60 STOPs remain accurately scoped. Generic prescribed-syndrome and
four-graph-row correction statements have small literal countercontrols, and
the naive X-shifted `Z` repair produces a nonzero translated-Hasse tail and a
same-grade `u1` collision. Those results block stripwise deletion. They do
not refute a complete Toeplitz/osculating Schur recurrence which retains the
higher contact tail. Thus m60 is not ruled out as a target-specific route,
but its larger packet count is irrelevant to the scalar counterfamily.

## 7. Exact stop boundary

The following claims are now stopped:

```text
packet-only arbitrary scalar error-trace surjectivity          RED
error-by-error Hermite localization by bounded X multipliers   RED
repairing the former by higher seed powers alone               RED
repairing it uniformly by changing or using all anchors        RED
```

The following claims are not decided:

```text
first-mismatch raw bordered Schur recurrence                   OPEN
all-errors-matched adjacent-carrier recurrence                 OPEN
rank-adaptive four-boundary lift from the complete source      OPEN
```

Any viable proof of an open item must use a distinguished syndrome, higher
contact rows from the non-scalar terms in `(OSC)`, or additional full-source
columns. It cannot cite arbitrary scalar Hermite surjectivity of this packet.

## 8. Formal receipt

`.experiments/K0PartialCarrierToeplitz6900.lean` proves, among others:

```text
partialCarrier_eq_sum_fullCarrier
slopeCompanion_fullCentering
curvatureCompanion_fullCentering
osculatingCompanions_at_fullScalarRoot
reverseSeedToeplitz_det
targetPacketTraceCoefficients_eq
targetPacketZeroBoundaryHigherSeedCoefficients_eq
targetPacketMatchedClearingHigherSeedCoefficients_eq
oldM60PacketTraceCoefficients_eq
anchorSwap_allows_two_constant_ratios
scalarPacketTrace_constantT_mem_mFrame
target_no_single_error_multiplier
```

It replays under the task-local 8 GiB wrapper. Printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`; the core osculating and
constant-`T` span lemmas do not use `Classical.choice`.

