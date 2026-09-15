# K0 order-seven bivariate approximant: cap window GREEN, pointwise readout OPEN

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

This is a real breakthrough: the top-cancellation kernel has dimension at
least 34 for **every** actual received pair `U0,U1`; no generic rank assumption
enters that count. This is enough to certify nonzero next-rung carriers once
the substituted packet is shown faithful. It is not enough to prescribe a
full error layer. Small exact finite-field models give fresh-boundary rank
four in every tested specialization, but neither that pointwise statement nor
the error-layer readout may be silently inferred from dimension.

There is also a separate global warning: this packet is **not** a complete
old-low-head kernel element. `H^37` supplies 37 extra orders only at agreement
roots. At error roots `H` is a unit, so the packet has error contact seven,
not 44. The result crosses rung seven of a layerwise error recurrence; later
error rungs remain. An earlier version of this note incorrectly said that the
packet had contact 44 at both kinds of old node. That statement was removed
after the explicit contact audit.

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
It is a legal seventh error-rung actuator, not a one-shot low-head
annihilator.

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

## 5. Boundary-gradient evidence

The order-seven packet is weighted homogeneous. In formal covariant
coordinates `(J,C1,C2)`, every packet polynomial `P` satisfies

```text
J*d_J P + 2*C1*d_C1 P + 3*C2*d_C2 P = 7 P.
```

Since the target characteristic does not divide seven, the formal
three-gradient map is injective on the abstract weighted-order-seven space.
The raw change of variables from `(Y,R,S)` to `(J,C1,C2)` is triangular with
diagonal `(1,-N,2*N^2)` and determinant `-2*N^3`. Over the fraction field of
`K[X,Z]`, this proves faithfulness when `N` is the nonzero locator and the
characteristic is not two. It does **not** say that evaluation of four
gradients at one fresh point is independent: on the stratum
`J=C1=C2=0`, all order-seven first gradients vanish, and other `J=0` strata
require separate rank analysis.

The Lean receipt proves the weighted Euler identity for all eight
covariants and the resulting zero-gradient implication.

For a pointwise discriminator,
`k0_order7_bivariate_approximant_probe_6900.py` builds the exact convolution
matrix over `GF(1000003)` and appends four literal fresh-boundary gradient
rows. Representative results:

```text
gap=3,  m=8,  k=3: rank 111, nullity 177, boundary increment 4
gap=5,  m=4,  k=1: rank  69, nullity  11, boundary increment 4
gap=8,  m=12, k=5: rank 245, nullity 379, boundary increment 4
gap=30, m=35, k=1: rank 548, nullity  28, boundary increment 4
gap=30, m=10, k=10: rank 665, nullity 303, boundary increment 4
```

Every tested random specialization and scale had boundary increment four.
These are exact modular ranks, not floating-point ranks. They prove that the
desired augmented minor is not formally identically zero, but they do not
prove it nonzero for every received word/fresh point.

## 6. The remaining exact OPEN for rung seven

The next theorem is now sharply isolated:

```text
Identify the exact scalar residual quotient produced by the completed first
six recurrence rungs. Then prove that, for every actual U0,U1 and every
admissible fresh point on the required nonvanishing stratum, the joint
top-cancellation/error-quotient/four-boundary map has full target rank.
```

The boundary-only subproblem says no nonzero boundary dual lies in the row
span of the top-coefficient equations. The right attack is the transpose
Toeplitz recurrence: a hypothetical row-span relation forces eight
simultaneous finite recurrences against

```text
g^7, g^5 Dg, g^3(Dg)^2, g(Dg)^3,
g^4 D2g, g^2(Dg)(D2g), (Dg)^2(D2g), g(D2g)^2.
```

One should use the actual fresh-point evaluation sequence and stratify the
triangular `(J,C1,C2,Z)` boundary symbol rather than assuming `J != 0`.
Separately, the recurrence residual must be shown to avoid the enormous
unreachable part of the `Y^7` channel. Even after those theorems, the
layerwise recurrence still needs legal actuators for error orders eight
through 43 (or a separate jump that closes those layers).

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
