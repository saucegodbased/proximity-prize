# K0 order-seven bivariate approximant: cap window GREEN, four-boundary STOP

Date: 2026-09-15 UTC. Scope: lower target 6900 only. This is a new source
architecture and an exact uncertainty reduction. It is not yet a completed
`ProtocolClaim`, candidate, build, or submission.

## Executive verdict

The order-seven cliff in `K0_ALL_NODE_WEIGHTED_OSCULANT_RUNG_SIX_6900.md`
is **not** a universal source-cap STOP. It only stops individual covariant
monomials and constant-size packets.

Using the passive variable `Z` as a second approximant coordinate produces a
uniformly nontrivial, fully cap-legal cancellation space:

```text
8 order-seven covariants
coefficient X degree  <= 9450
coefficient Z degree  <= 7
top-X cancellation    = 40322 coefficients

unknowns              = 8 * 9451 * 8 = 604864
possible constraints  = 40322 * 15   = 604830
guaranteed kernel dim >= 34
```

The needed saving is only 30872 coefficients. The extra 9450 canceled
coefficients pay for the coefficient-polynomial X degree itself. After the
cancellation, the data face lands at global X degree `D-1`, while every term
containing `Y`, `R`, or `S` has 90751 degrees of additional slack.

The top-cancellation kernel has dimension at least 34 for **every** actual
received pair `U0,U1`; no generic rank assumption enters that count. This is
a genuine degree/cap result, but it does not produce the required four-signal
rung. The actual compatible fresh boundary has

```text
J = Y-U0-U1*Z = 0.
```

On that locus the whole order-seven packet has boundary rank at most three,
before top cancellation is imposed. The earlier finite-field probe sampled
`J != 0`; its rank-four outputs were therefore on the wrong stratum and are
retracted as target evidence.

There is also a separate global warning: this packet is **not** a complete
old-low-head kernel element. `H^37` supplies 37 extra orders only at agreement
roots. At error roots `H` is a unit, so the packet has error contact seven,
not 44. It is an order-seven contact space, not a complete old-low-head
kernel. An earlier version of this note incorrectly said that the packet had
contact 44 at both kinds of old node; a second correction retracts the
rank-four boundary claim.

## 1. The eight covariants

Use the all-node generators from commit `66c06c8`:

```text
J  = Y - U0(X) - U1(X) Z                       contact weight 1
C1 = N' J - N V                                contact weight 2
C2 = N^2 A - 2NN'V + 4N^2S +(2N'^2-NN'')J    contact weight 3
```

The eight partitions of weighted order seven are

```text
J^7
J^5 C1
J^3 C1^2
J C1^3
J^4 C2
J^2 C1 C2
C1^2 C2
J C2^2.
```

Give each one an independent coefficient `p_i(X,Z)` with
`deg_X p_i <= 9450` and `deg_Z p_i <= 7`. Multiplication by such a coefficient
does not lower contact order: locally `X=x+epsilon` and `Z` is constant, so a
multiple of `epsilon^7` remains a multiple of `epsilon^7`. Therefore

```text
H^37 * sum_i p_i(X,Z) G_i
```

has contact at least 44 at agreement nodes and at least seven at error nodes.
It is a legal order-seven error-contact source space, not a one-shot
low-head annihilator and not the required four-signal actuator.

## 2. Why the cancellation map has a 34-dimensional kernel

Set the genuine active variables `S,Y,R` to zero. Every data face is then a
polynomial in `X,Z`. Each `G_i` has X degree at most

```text
7*(n-1) = 1835001
```

and Z degree at most seven. After multiplication by `p_i`, the sum has

```text
X degree <= 9450 + 1835001 = 1844451
Z degree <= 7 + 7 = 14.
```

Demand that its first 40322 reversed X coefficients vanish, separately in
all 15 Z channels. This is a linear map from a 604864-dimensional coefficient
box to a space of dimension at most 604830. Rank-nullity gives a kernel of
dimension at least 34, uniformly in all coefficients of `U0,U1`.

No independence of the 604830 equations is assumed. Dependencies only make
the kernel larger.

The exact arithmetic and abstract rank-nullity statement are machine checked
in `K0OrderSevenBivariateApproximantDimension6900.lean`.

## 3. Exact cap check

The residual source budget after `H^37` is

```text
D - 37g = 47g - 37g = 1804130,
```

with a strict inequality. Canceling 40322 leading coefficients leaves

```text
1844451 - 40322 = 1804129,
```

so every data-face Z channel is legal by exactly one degree.

For a term containing a genuine active variable, replacing one data branch
by a `Y`, `R`, or `S` branch improves weighted degree by at least

```text
(n-1)-w = 262143-131071 = 131072.
```

Thus even without any cancellation among active terms its global weighted
degree is at most

```text
37g + 9450 + 7(n-1) - 131072 = 8388660
```

against `D=8479411`, leaving 90751 degrees. The ordinary caps are also loose:
coefficient Z degree plus covariant Z degree is at most 14, active total
degree is at most seven, and the worst `2s+r` is at most four.

### Stage-sized boxes (dimension receipts only)

If the next recurrence needs one scalar at each of the 81731 error nodes,
the smallest useful order-seven box found so far is `M=11119`, `K=7`:

```text
unknowns                         = 8 * 11120 * 8 = 711680
top-face equations              = (11119+30872) * 15 = 629865
guaranteed kernel dimension     >= 81815
one error scalar + four boundary rows = 81735
dimension margin                = 80
active weighted-degree slack    = 89082
```

This is an exact budget but **not** a surjectivity theorem. In fact it cannot
control an arbitrary full local jet: the highest ordinary-active channel
`Y^7` is contributed only by `J^7`. At each fixed passive-Z coefficient its
81731-node value vector factors through just 11120 X coefficients. Therefore
that channel alone has codimension at least 70611. Any successful recurrence
must prove that the residual being corrected lives in a much smaller quotient
and that the joint top-cancellation/error/boundary map is onto that quotient.

For comparison, order eight has ten weighted partitions. The cap-legal box
`M=13712`, `K=100` has:

```text
unknowns                     = 13850130
top-face equations           = 13768226
guaranteed kernel dimension >= 81904
error+boundary margin        = 169
active weighted-degree slack = 4759
```

Again this is only a dimension budget; it does not defeat the same
high-active-channel obstruction by itself.

## 4. Translation to the actual NTT locator

The domain is the full size-`2^18` multiplicative NTT subgroup, so its monic
locator is

```text
N = X^262144 - 1.
```

The top window used above has length 40322, strictly below 262144. Replacing
one leading `X^262144` factor of `N` by its `-1` term drops X degree by
262144, outside the entire inspected window. Hence, in this window, the
standard monomial-locator model is **exact** for the actual `N`, not a
generic leading-symbol heuristic.

Writing `q=X^-1` and

```text
g(q,Z) = sum_{r>=1} (u0[n-r]+u1[n-r] Z) q^(r-1),
theta  = q d/dq,
```

the normalized data faces are exactly

```text
j  = -g
c1 = -(theta+1)g
c2 = -(theta+1)(theta+2)g
```

through the whole 40322-term window. This is the symbolic model used by the
rank probe. It retains arbitrary top coefficients of both actual received
interpolants.

## 5. Exact compatible-boundary STOP

The order-seven packet is weighted homogeneous. In formal covariant
coordinates `(J,C1,C2)`, every packet polynomial `P` satisfies

```text
J*d_J P + 2*C1*d_C1 P + 3*C2*d_C2 P = 7 P.
```

The abstract Euler identity still proves that the *polynomial* gradient map
is faithful. That fact does not survive evaluation at one compatible point.
At `J=0`, the only relevant basis behavior is:

```text
J*C1^3 : dJ axis proportional to C1^3
J*C2^2 : dJ axis proportional to C2^2
C1^2*C2: (dC1,dC2) = (2*C1*C2, C1^2)
```

Differentiating the coefficient polynomials can add a `dZ` axis. Therefore
every evaluated packet gradient is annihilated in covariant coordinates by

```text
(0, C1, -2*C2, 0).
```

If `(C1,C2) != (0,0)`, this is a nonzero covector (the target characteristic
is not two), so rank is at most three. If `C1=C2=0`, every first gradient is
zero. The triangular raw change of variables cannot restore rank: it merely
applies an invertible coordinate change when `N != 0`.

`K0OrderSevenBivariateApproximantDimension6900.lean` now proves this
annihilation basiswise, gives the closed form of the full evaluated symbol,
and proves that any linear map satisfying it is not surjective onto four
boundary coordinates. This is uniform and does not depend on the error
residual quotient or the top-cancellation matrix.

The old modular rank-four outputs are retained only as a regression lesson:
they arose because the script chose `j0` randomly nonzero. The repaired probe
sets `j0=0` and checks the structural rank loss.

## 6. Decision and remaining pivot

The transpose Toeplitz/Popov gate for this exact order-seven packet is no
longer the next question: no cancellation kernel can have larger boundary
image than the ambient packet. The packet is **RED for four-boundary K0**.

A structural jump is possible only at another contact order. At order six,
the formerly advertised packet `J^6,J^4*C1,J^3*C2,Z*J^6` actually has zero
first gradient at `J=0`; its `J != 0` determinant does not apply to the
compatible probe. Other order-six profiles (`J*C1*C2`, `C1^3`, `C2^2` and a
passive multiple) can have four axes when both `C1` and `C2` are nonzero, but
their global error-contact correction and source caps are not proved.

At order eight there are two J-free profiles, `C1^4` and `C1*C2^2`, so the
intrinsic `J=0` rank obstruction is not automatically the same. The numeric
`M=13712,K=100` receipt above remains only a cap/dimension budget. A valid
pivot must prove the actual compatible-boundary rank and show how order seven
of the preceding residual vanishes before an order-eight source can act.

## Replay

```bash
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/\
K0OrderSevenBivariateApproximantDimension6900.lean

python3 .experiments/k0_order7_bivariate_approximant_probe_6900.py \
  --gap 8 --m 12 --k 5 --seeds 3
```

The Lean file is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`
only), uses no `decide`/`native_decide`, and checks below the 4 GiB cap.
