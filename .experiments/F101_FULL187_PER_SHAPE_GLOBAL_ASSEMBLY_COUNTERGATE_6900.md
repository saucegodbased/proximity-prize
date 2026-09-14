# Full187 per-shape global-assembly countergate

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production,
claim, score, or accepted-6806 file was edited.

## Question

Do the exact target first-fringe successes justify proving a universal
statement separately for every `(r,s)` shape and every terminal coefficient
polynomial `C`?

The tested finite analogue uses

```text
(p,N,W,G,E,M,J,D) = (101,20,9,14,6,4,6,56),
U = Xi_E^2,
F(X,Y) = C(X)Y^6 + sum_(f=0)^3 P_f(X)Y^f,
deg P_f < D-Wf,  deg C < D-WJ = 2.
```

At each of the 20 subgroup nodes it imposes every graph-contact jet of total
order below four. This is exactly membership in `(Omega,Y-U)^4`.

## Exact result

All three residual-bearing adjacent pairs pass the first-fringe dimension
gate, with surpluses 3, 5, and 7. Nevertheless the complete lower matrix has
200 rows, 170 columns, and exact rank 170 over `F_101`. Adjoining the two
terminal `C` columns raises rank to 172; either terminal column alone raises
rank by one.

```text
lower rank / augmented rank = 170 / 172
individual terminal rank gains = 1, 1
```

Thus locally adequate first fringes do not assemble into a universal
per-shape arbitrary-`C` theorem. The implication being tested is false even
in a small ratio-faithful exact model.

## Scope and pivot

This does **not** invalidate the target first-fringe or q26 certificates. It
also does not test the actual four packet right-hand sides. It rules out an
overstrong intermediate theorem and forces the next experiments to preserve
one of the structures that theorem discarded:

1. cross-shape coupling among the 187 terminal shapes; or
2. the special four packet right-hand sides, rather than arbitrary `C`.

The executable receipt is
`f101_full187_per_shape_global_assembly_countergate_6900.py`. It uses exact
FLINT rank only, no probabilistic linear algebra.
