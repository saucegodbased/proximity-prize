# Full187 whole first later-Z frontier: exact six-row GREEN

Date: 2026-09-14 UTC. Scope: lower 6900 research only, extending commit
`91265f0`. No production or submission file is changed.

## Verdict

The first complete later-passive layer exported by the two P59 controls in
`91265f0` is **GREEN**, not another shifted-Pade defect. There are exactly
three live `u0`-free rows per P59 pivot—ordinary `q=0`, induced coefficient
Hasse `q=1`, and first curvature—and the resulting six physical aggregates
have an explicit legal two-band section.

The all-node diagonal operator in each band is

```text
       controls:       x       y       z
ordinary row           I       I       0
curvature row        -29 I   -57/2 I   0
jet row                0    K_actual    I
```

Here

```text
x = H0(P58^(r,10)),
y = H1(P57^(r+1,10)) with H0 held zero,
z = H1(P58^(r,10)).
```

`K_actual` is the higher coefficient jet induced by a fixed legal section;
it is retained, not set to zero. The curvature determinant is

```text
det [[1,1],[-29,-57/2]] = 1/2 != 0 in F_2130706433.
```

Consequently each band has rank `3N`, the two-band lower-triangular system
has rank `6N=1,572,864`, and its cokernel is zero for every internal and
cross-band induced operator.

This is a real extension of `91265f0`, but it is not a Full187 construction.
The four new physical section polynomials still emit `423,134` later
`u0`-free occurrences and `15,272,656` positive-`u0` occurrences. The result
proves that all of those exports advance one common filtration; it does not
solve them.

## 1. Exhaustive frontier, not sampled rows

For a P59 source, the first strictly later passive layer has `f=58`, `h=1`
and no `u0`. The live-weight condition

```text
58 + 2*aE + cS + q < 60
```

has exactly three solutions:

```text
(aE,cS,q) = (0,0,0), (0,1,0), (0,0,1).
```

Thus the two old pivots export precisely these rows:

|band|old pivot|kind|target `(T,E,R,S,Z)`|same-key origins|contact blocks|post-complete-depth residual groups|
|---|---|---|---|---:|---:|---|
|1|`P59^(10,10)`, outer `Z=2624`|ordinary|`(58,0,68,10,2625)`|11|3|none|
|1|same|curvature|`(59,0,67,11,2625)`|11|3|none|
|1|same|jet|`(59,0,68,10,2625)`|20|6|`(11,10,f57,q2,cS0)`|
|2|`P59^(9,10)`, outer `Z=2625`|ordinary|`(58,0,67,10,2626)`|26|6|`(11,10,f56,q2,cS0)`|
|2|same|curvature|`(59,0,66,11,2626)`|26|6|`(11,10,f56,q2,cS1)`|
|2|same|jet|`(59,0,67,10,2626)`|40|10|`(10,10,f57,q2,cS0)`, `(11,10,f56,q3,cS0)`, `(12,9,f56,q2,cS1)`|

The executable inverts the literal contact formula over all 187 physical
shapes, every terminal `C`, and every `P0,...,P59`. It finds 134 origins in
total, all with `u0` exponent zero. Their frozen per-row SHA-256 values are

```text
band1 ordinary   2665200b2b88e5f5a375f6534c50c046fce9b9eabaa4ff030771f8a0d817dfd0
band1 curvature  d495306da0b71f5e7a955310a2939f6159ae97e222cf634701e6b82bebdd1988
band1 jet        ddb189defec404a74c5f9a415a7a2d1644164d88523ce2a74e8752807807e18b
band2 ordinary   168ad632413a3b9fa55082fa564f3ea6eb3a4f832725da42480d9f3c46f30c29
band2 curvature  b20ecf5587d9800ce2335e8f3c73db77047f562b41d6111ac431f972a570fe35
band2 jet        8fedcd54ddaed1ada9f83d96518942d26b0fcae19997de9e789f3f30337c896c
all 134 origins  52522a3a514015d175deea51de3972de31a1541337e2092a86f38124a89f1347
```

This explicitly includes the curvature collisions omitted by a fixed-stream
calculation and the residual groups left by the complete-depth projection.

## 2. The physical sections are legal

The controls and exact strict windows are

|band|physical polynomial|prescribed variation|width|slack over `2N`|
|---|---|---|---:|---:|
|1|`P58^(10,10)`|joint `H0,H1`|601,272|76,984|
|1|`P57^(11,10)`|`H0=0`, arbitrary `H1`|601,273|76,985|
|2|`P58^(9,10)`|joint `H0,H1`|732,342|208,054|
|2|`P57^(10,10)`|`H0=0`, arbitrary `H1`|732,343|208,055|

Because `Omega=X^N-1` is squarefree and all its roots are nonzero, ordinary
confluent Hermite interpolation prescribes the two P58 jets in degree `<2N`.
For P57, use `delta=Omega*V`, `deg V<N`. It preserves `H0=0` and

```text
H1(delta)(alpha) = H1(Omega)(alpha) V(alpha)
                 = N alpha^(-1) V(alpha),
```

so its `H1` values are arbitrary. All four widths are strictly above `2N`.

The P57 section generally induces `H2` and higher jets. In its own band,
`H2(P57)` is the `K_actual` entry in the jet row. The first-band P58/P57
sections also induce every literal occurrence in the second band. The graph
retains these as arbitrary linear maps. No canonical higher jet is assumed
zero.

For desired row values `(a,c,b)` in the order ordinary, curvature, jet, an
explicit inverse is

```text
y =  58*a + 2*c,
x = -57*a - 2*c,
z = b - K_actual*y.
```

This proves surjectivity for arbitrary aggregate right sides, which is
stronger than using special correlations among the 134 physical origins.

## 3. Exact dependency graph and SCCs

Match the ordinary, curvature, and jet rows to `x,y,z`. Conservatively attach
every induced P58 jet `q>=2` to both of its prescribed coordinates and every
induced P57 jet `q>=2` to `y`. Scanning the literal provenance gives the SCCs

```text
{band1_x, band1_y}, {band1_z},
{band2_x, band2_y}, {band2_z}.
```

The two size-two diagonal matrices both have rank two and determinant `1/2`;
the singleton matrices have determinant one. Every inter-band edge points
from band 1 to band 2. There is no dependency from outer `Z=2626` back to
outer `Z=2625`. The frozen 19-edge contribution ledger has SHA-256

```text
03346d0e58ab9399578e47ac8a5d84e16490b4a5c04a61916222f546dfbb7d70.
```

## 4. One common well-founded order

Use lexicographic order

```text
(outer passive Z, J - active degree),
active degree = E+R+S, J=82.
```

For a control `P_k^(r,s)` and a lower contact choice `f<k`, an output has

```text
Z_out = Z_source + h,
active_out = f+r+s.
```

If `h>0`, passive `Z` strictly increases. If `h=0`, the passive grade ties
but active degree strictly decreases, so `J-active` increases. Therefore
every non-full-contact output strictly advances the same order, including the
positive-`u0` terms that do not advance `Z`.

The executable exhausts all live structural outputs of the four section
polynomials:

```text
same-filtration full-contact occurrences       12
strictly-later u0-free occurrences          423,134
strictly-later positive-u0 occurrences    15,272,656
```

The 12 same-filtration occurrences have exactly the six audited target keys;
there are no hidden diagonal rows. Hence the displayed SCC calculation is the
complete diagonal block, while everything omitted from it is provably later.

## 5. Relation to the F101 three-shape connector

The section here uses a base physical shape and its first slope neighbour:
relative shape types `{(0,0),(1,0)}`. The curvature row is separated without
an explicit `+S` coefficient group because adjacent contact degrees give the
two slopes `-29` and `-57/2`, whose difference is the unit `1/2`.

That mirrors only the **matched-error** small-chamber connector, where
`{(0,0),(1,0)}` suffices. The robust nonmatched-error F101 chambers require
`{(0,0),(1,0),(0,1)}`. There is no contradiction: this receipt handles the
agreement-visible `u0`-free diagonal, whereas the still-open 15,272,656
positive-`u0` occurrences are error-facing. They are the precise next place
to test an explicit `+S`/curvature physical group. This note does not assume
the F101 connecting map transfers to Full187.

## 6. Scope and next gate

This result removes the entire first later-Z frontier as a local obstruction
and supplies a global causal orientation. It does **not**:

- instantiate sections on the later `423,134 + 15,272,656` occurrences;
- close one complete passive band or its positive-`u0` connecting map;
- prove Full187 F3 containment, four-packet containment, or a score bound;
- create a 6900 candidate, build, comparator run, or submission.

The next exact gate is the earliest positive-`u0`/same-`Z` frontier in the
displayed filtration, with all same-key origins and an explicit first
curvature (`+S`) physical group. A full-rank diagonal block would justify
continuing; a closed deficient SCC would freeze this cross-slope cascade.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=3221225472 --cpu=600 -- \
  python3 -B \
  .experiments/full187_whole_first_later_z_frontier_gate_6900.py
```

Recorded receipt:

```text
decision           GREEN_WHOLE_SIX_ROW_FIRST_LATER_Z_FRONTIER
rank / cokernel    1,572,864 / 0
curvature det      1/2 = 1,065,353,217 mod p
canonical sha256   66a43314f383122d8547d48eca6322e45fd3b5cba396943954d8489c476d57b5
script sha256      35c822794c1fc0186bb464f5834eb971c393d892829cd45f8e45138478a71df9
peak RSS           17,156 KiB
wall time          about 0.03 s
```
