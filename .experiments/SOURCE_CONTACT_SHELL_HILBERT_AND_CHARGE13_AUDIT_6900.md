# Source/contact shell Hilbert and charge-13 cycle audit

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, radius, and accepted-6806 artifacts are unchanged.

## Verdict

The one-shell q=1 green and q=2 red are explained by an exact Hilbert sign
change:

```text
m6 q=t=1 saturated shell: source/contact = 642/540, margin +102
m6 q:t=2:1 saturated shell: source/contact = 751/800, margin  -49
```

The q=1 first post-prefix shell crosses the cumulative margin from `-58` to
`+44`, forcing complete contact cycles.  The q=2 shell changes `-890` to
`-939`; injection is dimensionally possible and the literal matrix indeed was
injective.  This is why adding `{pure,R,S}` could work in the first control
but could not work in the second.

Full187 is in a sharply different regime.  Its saturated shell margin is

```text
Delta = 127,554,977 > 0,
```

so top-diagonal shell cycles are unavoidable.  Nevertheless the accumulated
prefix deficit is so large that a complete kernel is first forced at exactly
the final cap:

```text
cap 2702, passive depth 2620: margin -117,797,284
cap 2703, passive depth 2621: margin   +9,757,693
```

After the strong safe-103 deletion, the final margin remains `+3,291,277`, or
`+3,291,273` after reserving four packet conditions.

The eleven physical charge-13 coefficient streams do **not** have an internal
raw cycle in the fixed target `Q=Xi_E^2` instance.  Projection to their unique
type-A output rows is injective, with rank `846,824`, exactly the source
dimension.  Any useful charge-13 packet class must therefore be a
cross-origin, quotient, or multi-grade mapping-cone cancellation.  Treating
the 11 streams alone as a kernel producer is structurally impossible.

These are exact dimension and evaluation-injectivity statements.  A negative
Hilbert margin does not prove an arbitrary map injective, and a positive
margin does not identify which packet boundary its kernel reaches.

## 1. Symbolic shell formulas

At active grade `d`, put

```text
q_d = min(d,q).
```

The legal derivative shapes are

```text
0 <= s <= min(t,q_d),  0 <= r <= q_d-s,
y = d-r-s.
```

Their strict coefficient widths are

```text
D - w*y - (w-1)*r - (w-2)*s
  = D - w*d + r + 2s.
```

When these widths are positive, define

```text
c_d  = sum_s (q_d-s+1),
mu_d = sum_s [ (q_d-s)(q_d-s+1)/2 + 2s(q_d-s+1) ],
A_d  = c_d (D-w*d) + mu_d.
```

Thus `A_d` is the exact source dimension at active grade `d`, before choosing
the passive exponent `z`.

Let `v` range over the exact shifted-Popov invariant valuations of the
asymmetric `(q_d,t)` contact layer.  The reachable one-node contact dimension
is

```text
B_d = sum_v max(m - (d-q_d) - v, 0).
```

Write

```text
e_d = A_d - n*B_d.
```

At fixed combined grade `h=d+z`, source and contact shell dimensions are

```text
S_h = sum_{d=0}^{min(h,J)} A_d,
T_h = n * sum_{d=0}^{min(h,J)} B_d,
shellMargin(h) = S_h-T_h = sum_{d<=min(h,J)} e_d.
```

For a complete combined-grade prefix through `H`, each active layer `d`
occurs at passive exponents `0,...,H-d`, so

```text
prefixMargin(H)
  = sum_{d=0}^{min(H,J)} (H-d+1)e_d.
```

Once `H>=J`, put

```text
Delta = sum_{d=0}^J e_d,
Omega = sum_{d=0}^J d*e_d.
```

Then the exact affine law is

```text
prefixMargin(H) = (H+1)*Delta - Omega.
```

This identity is the relevant passive-depth calculation.  A positive shell
margin forces a top-diagonal kernel.  A positive prefix margin forces a
complete kernel after all connecting maps.  The first does not imply the
second: a mapping-cone connecting map may inject top relations into the large
prefix cokernel.

## 2. Exact explanation of the two m6 controls

For the q=t=1 green control

```text
(n,w,g,m,D,q,t,J,L)=(10,4,7,6,42,1,1,8,12),
```

the active differences are

```text
(-18,-33,-15,3,21,29,37,45,33).
```

Therefore

```text
Delta = 102, Omega = 976,
prefixMargin(8) = 9*102-976  = -58,
prefixMargin(9) = 10*102-976 = +44.
```

The first post-prefix shell has source/contact dimensions `642/540`, so it
has at least 102 top-diagonal relations.  At most 58 can be consumed by the
prefix deficit; at least 44 complete contact cycles remain by dimension.  The
coefficientwise matrix then showed that its full raw `{pure,R,S}` group can
reach all four packet boundaries.

For the q:t=2:1 red control

```text
(n,w,g,m,D,q,t,J,L)=(10,4,6,6,36,2,1,8,9),
```

the active differences are

```text
(-24,-51,-52,-22,-2,18,28,28,28).
```

Hence

```text
Delta = -49, Omega = 449,
prefixMargin(8) = 9*(-49)-449  = -890,
prefixMargin(9) = 10*(-49)-449 = -939.
```

The saturated shell is `751/800`; it is not forced to have even one
top-diagonal relation.  The exact matrix found rank 751 for those 751 columns,
including the restored unsafe slice.  That observed injectivity is stronger
than the negative dimension count, but the sign explains why a q=1-style
kernel argument had no chance in this chamber.

## 3. Full187 passive-depth threshold

For

```text
(n,w,g,m,D,q,t,J,L)
  =(262144,131071,180413,60,10824780,21,10,82,2703),
```

the exact sums are

```text
Delta = sum e_d     =       127,554,977
Omega = sum d*e_d   =   344,898,900,115.
```

The shell margin first becomes positive at combined grade 79:

```text
shellMargin(78) = -68,433,321
shellMargin(79) = +13,724,689.
```

Thus top-diagonal relations exist even before the active cap is saturated.
At active cap `J=82`, the saturated shell is

```text
source       61,060,568,481
contact      60,933,013,504
margin          127,554,977.
```

However, the cumulative prefix at that point still has margin
`-334,311,837,024`.  For every later passive cap, the affine formula adds
exactly `Delta`.  Near the crossing:

| cap `H` | passive depth `H-J` | prefix margin |
|---:|---:|---:|
| 2700 | 2618 | -372,907,238 |
| 2701 | 2619 | -245,352,261 |
| 2702 | 2620 | -117,797,284 |
| 2703 | 2621 | +9,757,693 |

Therefore:

* shell-level cycles are dimension-forced from grade 79;
* charge-13 active origins first exist at grade 82 with passive exponent zero;
* a surviving complete kernel is first dimension-forced at grade 2703;
* the exact benchmark uses that first crossing, not a comfortable reserve.

Deleting unsafe terminal coordinates only from the final shell subtracts
`6,466,416`, leaving

```text
9,757,693 - 6,466,416 = 3,291,277.
```

This remains positive, but it gives no information about the rank of the four
packet boundaries on that kernel.

## 4. The isolated charge-13 block is raw-injective

The eleven physical charge-13 origins are

```text
c_s(X) Y^61 R^(21-s) S^s Z^2621,  0<=s<=10,
deg c_s < 76979+s.
```

Their widths are `76,979,...,76,989`, totaling `846,824`.  Each stream has a
correlated type-A output

```text
(T,E,R,S,Z)=(2,6,21-s,s+1,2675),
scalar=603758703,
u1 power=54.
```

The row channel is distinct for every `s`.  In the frozen target instance,
`Q=Xi_E^2`; it is nonzero at all agreement nodes because the error and
agreement sets are disjoint.  Thus multiplication by `Q^54` and by the scalar
is invertible pointwise on `G`.

Finally,

```text
max_s (76979+s) = 76989 < g=180413.
```

Evaluation of a polynomial of degree below `76979+s` on the `g` distinct
agreements is injective.  Projecting only to the unique type-A rows therefore
has rank

```text
sum_s (76979+s) = 846824,
```

equal to the whole physical source dimension.  The raw internal kernel is
zero.  A passive `Z` shift merely relabels the output exponent and does not
change this argument.

This does not say the charge-13 residue is useless.  It says exactly what a
valid construction must do: cancel its injective type-A heads using other
source origins or already licensed eliminators, while retaining the correlated
type-B/type-C tails and source provenance.  A transpose that treats the 11
streams as self-contained cycles is wrong by dimension before any packet is
considered.

## 5. Process decision

Stop all further small finite grids.  They cannot answer the remaining
question.  The next useful artifact must be a mixed-origin mapping-cone or
transposed operator at the final passive grade, with the following acceptance
checks:

1. every cancellation of a type-A head names the legal source origin or
   proved eliminator that supplies it;
2. the same operation carries the correlated type-B/type-C tails;
3. strict coefficient windows and safe/deleted provenance remain attached;
4. the output is either four exact packet lifts or a checked dual separator.

Hilbert arithmetic guarantees enough total kernel at the final grade.  It
does not guarantee that charge 13 participates in it or that the four packet
map has rank four.

## 6. Reproduction

```text
python3 -B \
  .experiments/source_contact_shell_hilbert_audit_6900.py
```

Recorded hashes:

```text
canonical e2ee8f5d73bf44c6ca4a8f8f917ee6508ae9c9521cd1c1209ab95c2ffb5135c6
script    f21bec0ae914dec08e629676f82ed5a09d44a2f29e5b37d74a569c0dada146db
```

The run performs exact integer/finite-field arithmetic only and builds no
large matrix.  It uses no `decide`, `native_decide`, production module, or
submission artifact.
