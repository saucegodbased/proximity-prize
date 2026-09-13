# Full187 centered Wronskian shell: target raw-strip receipt

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, or claim file was changed.

## Scope and shell

This checks source-degree feasibility only for the target-shaped one-shell
ansatz. It does **not** construct its coefficient polynomials, prove their
interpolation conditions, or establish `THREE-RHS`.

Take

```text
(m,g,e,w,J) = (60,180413,81731,131071,82),
b = 23,
Q = Xi^2,
V1 = R - 2 Xi Xi' Z,
J1 = Lambda V1 - Lambda' V.
```

The centered shell is

```text
V^(m-2) Z^b (c V^2 + C Lambda V Z + A Xi J1 Z).
```

Put

```text
B = C Lambda - A Xi Lambda',
B0 = B - c Q + 2 A Lambda Xi'
   = C Lambda - c Q + A(2 Lambda Xi' - Xi Lambda').
```

Then the exact boundary-zero coefficient is

```text
[Y^0 R^0 S^0 Z^(b+m)] = B0 (-Q)^(m-1).                (H0)
```

This collection is essential: separately charging its three pre-collected
pieces loses the available leading cancellation.

## Collected raw X-strip inequalities

For `1 <= y <= m-2`, the pure coefficient of `Y^y Z^(b+m-y)` is

```text
(-Q)^(m-2-y) [ C(m-1,y-1)cQ^2
              -C(m-1,y)B0 Q
              +2C(m-2,y-1)A Lambda Xi' Q ].            (P_y)
```

The `R` coefficient of `Y^y R Z^(b+m-1-y)`, `0 <= y <= m-2`, is

```text
A Xi Lambda (-Q)^(m-2-y).                               (R_y)
```

The terminal `y=59,60` pure rows are also audited; they are not binding.
All 238 collected rows obey the active/passive/curvature/seed caps. Every
shape has total `Y+R+S+Z=83`, far below 2703.

Writing strict bounds as `deg coefficient < cap`, the sharp raw degree caps
are

| coefficient | strict cap | maximum legal degree |
|---|---:|---:|
| `A` | 950770 | 950769 |
| `c` | 1049451 | 1049450 |
| `C` | 1000109 | 1000108 |
| collected `B0` | 1180522 | 1180521 |

The binding rows are:

```text
B0:       (Y,R,S,Z)=(0,0,0,83),
c:        (1,0,0,82),
A pure:   (1,0,0,82),
A R:      (0,1,0,82).
```

For example, the first three sharp equalities are

```text
1180521 + 2e*59       = 60g-1,
1049450 + 2e*59       = (60g-w)-1,
950769 + g + 117e     = (60g-(w-1))-1.
```

## What the `B0` cancellation buys

The degree of the Wronskian cofactor is

```text
deg(2 Lambda Xi' - Xi Lambda') = g+e-1 = 262143,
```

because its monic leading coefficient is `2e-g=-16951`, nonzero in the
target field. At the sharp individual `A,c` caps, both

```text
deg(cQ), deg(A(2 Lambda Xi'-Xi Lambda')) <= 1212912,
```

whereas (H0) permits only `deg B0 <= 1180521`. Thus achieving the wider
sharp `A,c` range requires an actual cancellation of the highest 32391
degrees inside `B0`. This receipt does not assert such a cancellation exists.

If no cancellation is used, the sufficient componentwise caps are instead

```text
deg A < 918379,
deg c < 1017060,
deg C < 1000109.
```

They guarantee `deg B0 < 1180522` term by term.

## Three-RHS interpolation: degree budget only

A conservative depth-three Hermite CRT representative has degree

```text
3e-1 = 245192.
```

It is below even the no-cancellation caps above. In particular, its possible
`B0` component degrees are

```text
deg(C Lambda)                 <= 425605,
deg(c Q)                      <= 408654,
deg(A(2 Lambda Xi'-XiLambda')) <= 507335,
```

giving strict `Y=0` margin

```text
60g - [507335 + 2e*59] = 673187.
```

Therefore the source **degree budget** can accommodate independent
coefficient triples for all three RHS (indeed, it can accommodate a
depth-three Hermite representative per coefficient). This is only a
conditional source GO. The actual nodewise values/Hasse data that would
produce the three error syndromes, together with the exact divisibility
`B+A Xi Lambda'=C Lambda`, have not been constructed.

## Checked artifact

`full187_centered_wronskian_target_strip_6900.py` enumerates all collected
rows, verifies every exact integer inequality, checks the sharp endpoints,
and records the conditional interpolation statement under a 4 GiB cap.

`Full187CenteredWronskianTargetStrip6900.lean` independently formalizes the
depth-three component caps, the four complete row families, the 673187
boundary-zero margin, and the shape-cap preservation for every `Z^k` shift
through `k=2620`. Its capped build is green without `decide` or
`native_decide` (SHA-256
`12a7bba992fc7aef8bb17a781d18402469aeec7d1f48b4317de050870603104f`).

```text
canonical payload SHA-256
7f982845329562e8bef6447ac87d137ed868763bc096a7a830d8bb103deea401

script SHA-256
a5974e681d6c1824ae212dc4c6745b2080af32b2db4647d1aafd2a38c598b449
```
