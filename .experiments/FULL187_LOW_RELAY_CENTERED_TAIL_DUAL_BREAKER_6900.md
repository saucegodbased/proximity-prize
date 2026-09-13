# Full187 centered pure-tail factors break the weight-four relay dual

Scope: `lower6900` research only.  This is neither a production change nor a
submission claim.  It targets the exact two weight-four cokernel functionals
from `7777e3d`, rather than running another broad normal-family rank search.
The executable exact receipt is
`full187_low_relay_centered_tail_dual_breaker_6900.py`.

## Literal centered factors and agreement contact

Put `V=Y-H^2 Z`, `W=R-2HH'Z`, and use the fixed pure-tail coefficients

```text
U = -2LH' + L'H,
B = -2L^2(H')^2 - 2L^2HH'' + 4LL'HH' - 2(L')^2H^2 + LL''H^2.
```

The two centered factors simplify *exactly* in the literal source ring:

```text
K1 := J1-HUZ = L R-L'Y,
K2 := J2-BZ  = (2(L')^2-LL'')Y - 2LL'R + L^2S.
```

Consequently `K1` and `K2` vanish at the fixed pure seed, but no positive
agreement contact is attributed to them.  For `0 <= b <= 60`, the rows

```text
q L^(60-b) V^b K1,          q L^(60-b) V^b K2
```

have agreement contact at least 60 solely because
`L^(60-b)V^b` has contact `(60-b)+b=60`.  This is the required `C_G`
ledger and does not rely on an incorrect claim that a centered factor itself
has positive contact.

## Exact source scan for the first centered columns

The script expands every binomial `V^b=(Y-H^2Z)^b`, every literal component
of the displayed `K1`/`K2` identities, and checks all four source caps and
strict X strips with a multiplier of degree `<e=81731`.

| family | last illegal b | first legal b | strict margin at first legal b | worst literal shape |
|---|---:|---:|---:|---|
| `L^(60-b)V^b K1` | 23 (`-3340`) | **24** | `13611` | `(Y,R,S,Z)=(0,1,0,24)` |
| `L^(60-b)V^b K2` | 33 (`-14242`) | **34** | `2709` | `(1,0,0,34)` |

Thus the least-normal-degree source-legal centered breaker is
`L^36 V^24 K1`.  The first `K2` breaker is `L^26 V^34 K2`.  The exact strip
formulae are

```text
margin(K1,b) = 16951*b - 393213,
margin(K2,b) = 16951*b - 573625.
```

They already include the coefficient degrees of `L'`, `L''`, and the
`H^(2(b-i))` binomial tails; no uncollected `BZ` or `HUZ` tail is charged
twice.

## Weight-four dual test

Use the prior row order

```text
(1,x,x^2,x^3,z,x^4,xz),   x=V-1,   wt(x)=1, wt(z)=3,
```

and its two exact left-null vectors

```text
D4 = (487635,-32509,1653,-57,0,1,0),
Dz = (-60,1,0,0,-58,0,1).
```

At an error write `Y=1+x`.  The centered factors have the exact affine
forms

```text
K1 = k1 + l1*x,  k1=LR-L',               l1=-L',
K2 = k2 + l2*x,  k2=(2(L')^2-LL'')-2LL'R+L^2S,
                  l2=2(L')^2-LL''.
```

For the first legal rows their dual pairs are

```text
L^36 V^24 K1 : (D4,Dz)
  = (58905*k1 - 6545*l1, -36*k1 + l1),

L^26 V^34 K2 : (D4,Dz)
  = (14950*k2 - 2300*l2, -26*k2 + l2).
```

The determinant taking `(k1,l1)` to the first pair is `-176715`; for
`(k2,l2)` it is `-44850`.  Both are nonzero modulo the Full187 prime
`2130706433`.  Hence either nonzero centered linear factor genuinely
escapes the common kernel of the two old duals; the prior six-row STOP does
not extend to this source family.

## Augmented reachability

One added breaker removes only one of the two cokernel directions.  In the
flat valid local specialization

```text
L=1, L'=L''=0, R=S=1,
(k1,l1)=(k2,l2)=(1,0),
```

the six old rows plus only `K1_24` (or only `K2_34`) have rank/augmented-rank
`6/7`, so neither one-row extension reaches F0 through weight 4.  Adding
both has rank/augmented-rank **`7/7`**.  An exact flat associated-graded
solution, ordered as `R57,R58,R59,R60,Phi2,Phi3,K1_24,K2_34`, is

```text
(-31630313/2547, 61544021/1698, -9971236/283, 2267502127/198666,
 -590249/198666, 0, 421201/38205, -1434349/110370).
```

For general local centered coefficients, the relevant two-by-two determinant
is

```text
Delta = -993330*k1*k2 - 23895*k1*l2 + 155220*l1*k2 - 4245*l1*l2.
```

Thus the two-row weight-four lift is available exactly on the open condition
`Delta != 0`; the flat specialization proves this condition is not a formal
zero.  It is **not** yet a uniform all-error theorem.

## Status and first remaining condition

This is only a **dual-breaker/projection GO**: the old W4 dual is genuinely
broken by the cheapest legal centered `K1` source, and the first legal
`K1/K2` pair has an explicit weight-four F0 lift after fixing the passive
normal values in a nonempty local chart.  It preserves agreement order 60
and pure-seed cancellation.

It is not a literal `C_E` correction.  The unreduced factors retain the
passive normal forms `LR-L'Y` and
`(2(L')^2-LL'')Y-2LL'R+L^2S`; a full contact calculation must match those
`R,S` rows, not specialize them away.  Also, replacing `Y` by
`V+H^2Z` adds centered `H^2` rows outside the old `(x,z)` projection.  The
flat witness has their coefficients zero, but generic augmented reachability
needs those extra rows as well.

The first unproved condition is therefore stronger than merely `Delta != 0`:
construct a full passive-normal and Hasse/CRT lift that matches every
error-contact component at every node.  The displayed source margins only
pay for degree-`<e` value interpolation; they do not pay for that higher
Hermite lift.  The three RHS components and global boundary coupling remain
unproved.
