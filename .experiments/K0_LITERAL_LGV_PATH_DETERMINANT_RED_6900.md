# K0 literal LGV/path determinant — RED

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production,
candidate, claim, score, comparator, or submission file is changed.

## Verdict

**RED for an LGV proof built from the literal raw contact support.** A
coefficient-aware network can be reconsidered only after an independently
proved exact tapered quotient/normal form; constructing that quotient is the
missing global confluence theorem, rather than a path shortcut.

The K0-specific first falsifier is already decisive. On the deterministic
exact-ratio control

```text
F_101, (n,w,g,m,B,s,U,L)=(11,5,8,5,2,1,8,8),
```

the actual relaxed source has 3604 columns and the literal contact target has
4191 occurring rows. Maximum matching in the exact nonzero support has rank
3604 and nullity zero. The frozen exact coefficient matrix has rank 3418 and
nullity 186, and adjoining the four boundary coordinates raises exact rank by
four. Since the support matching already saturates every source column, its
bordered gain is zero. Thus the desired kernel and all four boundary directions
live in coefficient cancellations invisible to raw support paths.

Reproduction:

```text
python3 .experiments/k0_lgv_literal_path_falsifier_6900.py
```

The run takes about 6.3 seconds and 135 MiB RSS. Canonical JSON SHA-256:

```text
a94eab304e9472e509e9e72c443bc797d6df8605141479a619fca1275400480f
```

## Literal operational graph

For a legal raw source monomial `X^a S^s Y^y R^r Z^z`, the actual contact
formula at a node `x` is

```text
(x+epsilon)^a S^s
  (u0+u1 Z+epsilon R-epsilon^2 S+epsilon^3 T)^y R^r Z^z,
```

truncated at outer order 47. A literal factor-stage graph has one layer for
each processed `X` or `Y` factor. An `X` layer chooses `x` or `epsilon`; a `Y`
layer chooses one of `u0,u1 Z,epsilon R,-epsilon^2 S,epsilon^3 T`. Every edge
increments the processed-factor counter, so this expanded graph is genuinely
acyclic. Its path product is the corresponding literal coefficient and paths
ending at the same local monomial are summed.

To obtain the wanted theorem by LGV one would then need a common network for
all legal source columns and node-local rows, plus four boundary sinks, and a
square minor with a provably surviving vertex-disjoint path family. The
support-rank discrepancy above shows that the literal bipartite incidence
network is not that common network: it forgets 186 exact relations already in
the small faithful K0 control.

## Equal-weight paths and cancellation

Path uniqueness fails before any target scaling question.

* At node 1, columns `X^4,X^5` and rows scalar/`epsilon` give
  `[[1,1],[4,5]]`. Both determinant matchings have the same contact weight,
  with products 5 and 4. The determinant is nonzero, but not because of a
  unique minimum path family.
* In `Y^2`, choosing `(u1 Z,epsilon R)` in the two possible factor orders
  reaches the same `epsilon R Z` sink with the same product. At the control's
  node 6, `u1=1`, so the two paths sum to coefficient 2.
* There is a zero minor in the actual benchmark field, not merely in the
  F_101 control. Here

  ```text
  p=2130706433, p-1=127*2^24,
  ord_p(183)=2^23=8388608 < D=47*180413=8479411.
  ```

  Therefore the legal pure-X columns `1,X^8388608` against scalar rows at
  nodes 1 and 183 give `[[1,1],[1,1]]`, with determinant zero. The two
  equal-weight matching products cancel exactly. An artificial edge-ID
  tie-break cannot change this coefficient identity.

These examples also show why a blanket cancellation claim is unavailable:
equal-weight families sometimes subtract to a unit and sometimes to zero.
The coefficients, rather than support or path order, decide.

## Target cap-seam audit

The target raw source is exactly

```text
m=47, B=16, sCap=6, U=64, L=5107,
D=47*180413=8479411, w=131071,
2s+r <= 16,
s <= 6,
s+y+r <= 64,
s+y+r+z <= 5107,
a+w*y+(w-1)*r+(w-2)*s < D.
```

The local expansion graph does not alter the source origin, so its local
acyclicity says nothing about whether a proposed backsolve column is legal.
The natural equal-weight reverse exchanges expose the seams:

```text
Y  <-> X R       sends r to r+1 and can cross 2s+r=16;
Y  <-> X^2 S     sends s to s+1 and can cross s=6 or 2s+r=16.
```

Both preserve weighted degree and active degree, which is precisely why a
filtration-only argument does not notice the failure. The formal forward
connection identities in `K0RawRSConnectionTranspose6900.lean` prove legality
only when rooted in their stated legal parent; they do not give unrestricted
reverse edges or stability of a selected pivot family.

The strict X taper is independently load-bearing. For the naive critical
`S*(Y-W)^47` lift, the first three `S*Y^y` coefficient bands (`y=0,1,2`)
overflow their legal strict X widths, and only `y>=3` fits. This is already
formal in `K0CriticalTailTaperObstruction6900.lean`; two connection derivatives
still do not repair those three bands. Any proposed 47-stage path family must
therefore display legal origins at these taper seams, rather than infer them
from its local sinks.

## Characteristic/factorial audit

There is no helpful factorial torsion. In characteristic 2130706433:

* all factorials through `64!` from the `Y` multinomial expansion are units;
* all outer Hasse denominators through `46!` are units;
* `2` and `6`, which relate ordinary and Hasse-normalized `S,T` coordinates,
  are units;
* every legal X exponent is below the characteristic.

Thus Hasse normalization is an invertible row/column rescaling and does not
change support, rank, or the displayed pure-X cancellation. Loss of rank comes
from specialization and sums of equal-weight paths, not a hidden zero
factorial.

## Only legitimate reopen condition

A repaired route must first construct a coefficient-aware quotient whose
matrix rank is proved equal to the exact contact rank, with all four cap seams
and the strict X taper built into its states. LGV may then be useful on a small
residual band if that quotient is planar/acyclic and has a unique surviving
minor. Assuming such a quotient, or selecting `rank(C)` structural pivots
without proving their determinant, is circular. Therefore this isolated idea
is **RED**, not a current route to the target.
