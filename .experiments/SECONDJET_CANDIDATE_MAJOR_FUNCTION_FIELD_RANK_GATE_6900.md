# Second-jet candidate-major function-field rank gate at 6900

Date: 2026-09-14 UTC. This is an exact arithmetic and finite-field
discriminator, not a proof, candidate, or submission.

## Result

The proposed fourth-curvature osculating repair has a degree-ledger error:
its first agreement-tangent coefficient is already outside the root-count
range. The previously stated order `15` is not available.

A simpler zero-reserve P5 source is genuinely positive at the target and has
the expected rank dichotomy in faithful small contact kernels:

```text
(m,B,s,U,L,k,n0) = (148,64,10,200,5465,0,1)
columns            = 6,379,078,467,962,794
one-node rank      =        24,333,499,291
N * rank           = 6,378,880,838,139,904
source margin      =           197,629,822,890
```

However, this does **not** solve a new geometric theorem. It lands exactly on
the archived Global-O2 blocker:

```text
rank of the full (Y,R,S,Z) conormal < 4
  ==> u1 on the agreement set has an interpolant of degree <= w.
```

The small exact tests support this implication but do not prove it. The
low-degree branch is necessarily rank at most three because it is a legal
selected polynomial pencil. Therefore universal pointwise rank four is
false, while rank four on the retained/non-pencil branch remains the right
conditional theorem.

## 1. Why the k=4 order-15 calculation fails

Let

```text
A = 180413,  w = 131071,
gS = A-(w-2) = 49344,
gT = A-w-1   = 49341.
```

For every source monomial which can survive four curvature derivatives, the
profile `(148,64,30,200,5465,4,5)` uses reserve four. Hence its original
weighted degree is strictly below

```text
m*A - 4*gS.
```

Applying `(partial_S)^4` lowers weighted degree by another `4*(w-2)` and
lowers contact from `m` to `m-4`. Since

```text
4*gS + 4*(w-2) = 4*A,
```

the resulting polynomial `W` has exactly the bound

```text
deg_X W(f'',f,f',z) < (m-4)*A.
```

There is only the strict one-degree root-count slack. Replacing one graph
coordinate by the degree-`<A` agreement interpolant costs as much as
`gT=49341`, while preserving the `(m-4)A` roots. Thus order one is already
unforced. The literal target-legal endpoint

```text
X^((m-4)A-1) * S^4
```

shows that the degree envelope is sharp. The expression
`4*A-14*49341` subtracts the four-contact loss once when constructing `W`
and then incorrectly reuses that same `4*A` as fresh tangent slack.

In the faithful small profile

```text
(n,w,A,m,B,s,U,L,k,n0)=(5,2,4,5,10,5,5,7,4,5),
```

the complete contact matrix has `2910` columns, rank `2571`, and kernel
dimension `339`, but the projection of the kernel to all `S`-degree-at-least
four coordinates has rank zero. Consequently `D4(V)=0`, its gradient rank is
zero, and adding its first unforced directional coefficient still has rank
zero. This does not prove target collapse, because the small chamber is not a
scaled target instance. It does prove that total kernel dimension cannot be
used as a derivative-image lower bound.

## 2. Zero-reserve P5 rank discriminator

The executable constructs the complete all-node order-two contact matrix
using the exact relaxed support inequalities

```text
2*Sdeg+Rdeg <= B,  Sdeg <= s,
Ydeg+Rdeg+Sdeg <= U,
Ydeg+Rdeg+Sdeg+Zdeg <= L,
weighted degree < m*A.
```

For each receipt, a genuine degree-`w` candidate is made to agree at exactly
`A` nodes. Every contact-kernel row is independently checked to specialize
to the zero polynomial on that selected graph.

Three low-degree agreement tangents were checked across two source chambers.
Every full conormal has exact rank three over `F_101(X)`, and the polynomial
identity

```text
(h,h',h'',1) dot grad Q = 0
```

holds for every kernel row. This is forced: `f+t*h` is a legal degree-`w`
candidate for every `t` and agrees on the same nodes with seed `z+t`.

Twelve degree-`>w` agreement tangents were tested across three chambers,
including top monomials, dense top-degree polynomials, randomized received
directions, different agreement sets, and `(n,w,A)=(5,2,4)` and `(7,3,5)`.
All twelve have exact rank four over `F_101(X)`. Rank four is certified by a
nonzero specialized four-minor; the conormal entries are polynomials in `X`,
so this is a valid lower bound over the function field. It is not a proof of
the target implication.

The current semantic hash is

```text
28377c81c07fcd1f1f22ef8c2cdd7b0c124469814218eeb2e7a577ad581bfad9
```

## 3. Prior-work comparison

The qualitative low/high tangent behavior is not new. It reproduces the
mechanism in

```text
f7_badrow_full_conormal_semantics_audit.py
GLOBAL_O2_REVERSE_INCLUSION_AND_HIGH_AGREEMENT_SPLIT_AUDIT_6900.md
GLOBAL_O2_FIXED_MINOR_COVER_AND_DUAL3_AUDIT_6900.md
```

Those audits already identify the missing low-band theorem as
rank-defect recovery, or equivalently the first extra Newton divided
difference identity for `u1`. They also explain why more syndrome grids do
not reduce the central uncertainty. The genuinely new outputs here are:

1. the target-positive zero-reserve profile above;
2. confirmation that its exact relaxed support has the same rank semantics;
3. the correction of the k=4 tangent order from `15` to `1`; and
4. recalibration of the fixed-cutoff high-agreement obstruction at `m=148`.

## 4. High-agreement obstruction for the new profile

With fixed cutoff `D=m*A`, the standard determinant-preserving contact
columns give exact residual degree bounds at `|G|=A+r`:

```text
full four-minor:      148025 - 589*r
vertical three-minor: 148026 - 441*r.
```

Therefore the full four-coordinate route is not degree-killed only through

```text
r=251, |G|=180664; residual 186.
```

At `r=252`, `|G|=180665`, the residual is `-403`, forcing every full minor
to vanish. The vertical route survives through `r=335`, `|G|=180748`, with
residual `291`; at `r=336`, `|G|=180749`, its residual is `-150`.

Thus even a proof of rank-defect recovery for the first agreement bucket
would leave a real high-agreement split. Retuning the source cutoff per
agreement bucket remains arithmetically possible, but each bucket's source
and aggregate count must be paid honestly; this note does not supply that
count.

## 5. Reproduction and stop rule

```sh
time python3 \
  .experiments/secondjet_candidate_major_function_field_rank_gate_6900.py
```

The script uses dense exact modular matrices only in the displayed small
chambers and stays far below 3 GiB.

Do not run another random syndrome grid. The next useful unit is one of:

1. prove the target low-band implication `rank<4 => degree(u1|G)<=w` using a
   fixed symbolic contact chart / first extra Newton coefficient;
2. construct the literal three-dimensional dual continuation map from the
   archived Global-O2 plan; or
3. find a different source whose fixed-cutoff minor window and count close
   the high-agreement band.

Until one of these is supplied, the zero-reserve source is a numerically
viable producer with an old, genuinely geometric blocker—not a nearly
mechanical submission path.
