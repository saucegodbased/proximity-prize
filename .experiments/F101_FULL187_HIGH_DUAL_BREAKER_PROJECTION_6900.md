# F101 Full187 high block: exact dual breaker projection

Date: 2026-09-13 UTC. Scope: lower 6900 research only. This is a small
exact quotient receipt for the faithful `F101`, `Q=Xi_E^2` control. It is
not a production edit, a target theorem, or a replacement for the separate
low-group deletion minimizer.

## Verdict

For the primary source, let `H` contain exactly the literal columns with
boundary degree `d=Y+R+S >= 2`. The high block has an **exact joint locator
defect of three** for `F0,F1,F2`. A particularly small relevant subspace of
its left nullspace is supported only on three `J` rows:

```text
J[Y,X^1], J[Y,X^2], J[Y,X^3].
```

Its three duals pair as the identity with `F0,F1,F2`. Projecting all 1,192
omitted `d=0,1` columns through those duals leaves exactly three nonzero
columns:

```text
X Y,  X^2 Y,  X^3 Y                 (all with seed z=0).
```

They have rank three, and every proper subset has rank at most two. This is
the minimal direct breaker of the **displayed three-coordinate probe**, not
of the full high quotient. In fact, the three columns do not lower the exact
bordered joint defect at all: it remains three. They only break the first
chosen scalar-obstruction coordinates and leave the rest of the exact `J`
head and all contact residuals untouched.

The useful design constraint is therefore sharp: boundary-zero columns are
not direct locator-normal breakers at all. If they occur in a genuine relay,
their role has to be indirect—cancelling contact created by the forced
boundary-one `J` head.

## Exact calculation

The fixed chamber and the literal maps are those of the whole-source locator
lift receipt:

```text
F_101,
(n,w,A,m,D,s,t,J,L) = (11,5,8,4,32,1,1,6,10),
G={0,...,7}, E={8,9,10}, Q=Xi_E^2.
```

The source splits into 1,515 high columns and 1,192 omitted low columns:

| omitted boundary degree | columns | seed range |
|---:|---:|---|
| 0 | 352 | `0..10` |
| 1 | 840 | `0..9` |

No high column has a `J` coordinate. Write

```text
Lambda = X (10 + 39 X + 99 X^2 + ...).
```

The `Y` coefficients of the three locator normals have successive orders at
the anchor `X=0`:

```text
ord_X J_Y(F2) = 1,
ord_X J_Y(F1) = 2,
ord_X J_Y(F0) = 3.
```

This is the derivative staircase: the leading terms come from

```text
F0_Y = Lambda^3,
F1_Y = -Lambda^2 Lambda',
F2_Y = Lambda * (2(Lambda')^2 - Lambda Lambda'').
```

At `X^1,X^2,X^3`, with columns ordered `F0,F1,F2`, the exact Hasse block is

```text
             F0  F1  F2
[X^1 Y]      0   0  81
[X^2 Y]      0  10  92
[X^3 Y]     91  55  29.
```

Its inverse supplies left-null functionals:

```text
lambda_0 = 14[J,Y,X^1] + 46[J,Y,X^2] + 10[J,Y,X^3],
lambda_1 = 55[J,Y,X^1] + 91[J,Y,X^2],
lambda_2 =  5[J,Y,X^1].
```

Over `F_101`, `lambda_i(F_j)=delta_ij`, while every `lambda_i` annihilates
every high column. This proves defect at least three; the three RHS give the
matching upper bound.

The low projection is just as sparse:

```text
                         (lambda_0, lambda_1, lambda_2)
X Y                         (14,55,5)
X^2 Y                       (46,91,0)
X^3 Y                       (10,0,0)
all other d=0,1 columns      (0,0,0).
```

Thus this quotient has no evidence for a broad `R/S` family, a passive seed
recurrence, or a boundary-zero direct injector. It is only the first, local
normal-coordinate gate.

There is an exact guard against mistaking that gate for a solve. After adding
the three displayed columns, the untouched rows

```text
J[Y,X^4], J[R,X^3], J[S,X^3]
```

give the new triangular block

```text
             F0  F1  F2
[Y X^4]     85  94  55
[R X^3]      0  91   9
[S X^3]      0   0  91.
```

Its inverse gives `(82,84,62)`, `(0,10,9)`, and `(0,0,10)` on those rows.
Those functionals annihilate both the high block and `XY,X^2Y,X^3Y`, while
again pairing identically with `F0,F1,F2`. Therefore the actual joint defect
after those three columns is exactly still three. Boundary-zero terms cannot
repair this missing `J` information; all 69 forced head coordinates must be
present first, after which a boundary-zero tail may serve its indirect
contact-relay role.

## What is actually forced, and where seed one enters

Breaking the three displayed functionals is far weaker than matching all
polynomial normal coordinates. Since high columns, `d=0` columns, and
seed-positive `d=1` columns have no `J` component, an exact lift of `Fi`
has a unique `d=1,z=0` coefficient head. Its supports are:

| normal | forced `J` head | centered `d=0,z=1` completion | total low normal |
|---|---:|---:|---:|
| `F0` | 22 | 28 | 50 |
| `F1` | 44 | 28 | 72 |
| `F2` | 66 | 28 | 94 |

The union of the three forced heads has 69 literal monomials. The canonical
agreement-zero centered completions have the clean seed/derivative staircase

```text
F0: Y X^(3..24),                    Z X^(3..30)
F1: Y X^(2..23), R X^(3..24),       Z X^(2..29)
F2: Y X^(1..22), R X^(2..23), S X^(3..24), Z X^(1..28).
```

Each completion is zero on the eight agreement nodes but has an error-contact
residual. The residual is exactly where a genuine low/high relay must act.
This receipt does not minimize that residual relay; it explains why the
separate group minimizer should treat low boundary-zero terms as relay-only,
not as candidate direct normal breakers.

## Reproduction

The calculation avoids dense elimination and was run under the requested
four-GiB address-space ceiling:

```text
prlimit --as=4294967296 --cpu=1200 -- \
  python3 .experiments/f101_full187_high_dual_breaker_projection_6900.py
```

The executable asserts the literal source support, the derivative block, all
left-null pairings, the complete low projection census, and the forced exact
`J` heads before emitting a canonical SHA-256 receipt. The observed receipt
hash is

```text
db769380a60863ec8aa8c7d0d48837269725324f1a2eb2c5ecc9825b028856fe
```

## Route consequence

Use the three-column quotient only as a necessary-interface check. A proposed
relay that omits the forced `d=1,z=0` head cannot possibly lift any `Fi`; a
proposal that advertises a `d=0` direct breaker is contradicted by this
projection. The remaining question is specifically whether a translation-
stable low tail cancels the error contact of the forced centered heads while
the high block closes the rest. That is the right scope for the primal
delta-minimization receipt, not for more autonomous high-`V` packets.
