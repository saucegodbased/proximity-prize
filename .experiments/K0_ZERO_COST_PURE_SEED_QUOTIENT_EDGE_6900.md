# K0 zero-cost pure-seed quotient edge (m47 / target profile)

## Decision

The family

```text
X^a Z^z,  0 <= a < 47g,  0 <= z <= 3757,
```

does expose one actual component of a boundary-compatible contact dual.  At
a general boundary seed value `gamma`, it determines the entire reduced
quotient numerator in each outer-seed band:

```text
q_z mod A = z * gamma^(z-1) * lambda_Z * E_xi.
```

where `A` is the monic degree-`47g` pole polynomial and `E_xi` is the unique
degree-`<47g` numerator satisfying

```text
topCoeff(((E_xi * p) mod A), 47g-1) = p(xi)
```

for every `p` of degree `<47g`.

At the centered constant-`T` control (`gamma=0`) this specializes to
`q_z=0` for `z!=1` and `q_1=lambda_Z*E_xi`.  The general displayed identity
is the literal derivative of `Z^z` at `gamma`, so the theorem is not limited
to that centered chamber.

This is a genuine quotient-numerator statement, proved from the explicit
perfectness/injectivity of the quotient-top pairing.  It is not a maximal-rank
claim inferred from dimensions.

It is also an exact **STOP for the pure-seed family alone**.  `E_xi` is
nonzero (pair it with `p=1`), so every one of the pure-seed equations is
compatible with `lambda_Z != 0`.  The next useful edge must connect this
one-dimensional derivative sequence to numerators constrained by a different
PC shape.  More adjacent pure-seed bands do not do that.

## Why the bands separate

For `y=r=s=0`, the literal PC expansion has only `(f,h)=(0,0)`.  Node
localization changes `X^a` to its translated order-47 contact jet and does
not involve `u0` or `u1`.  The outer seed remains a literal monomial:

```text
Z^z * contactColumn(X^a).
```

Consequently its coefficient at outer degree `n` is zero unless `n=z`.
There is no hidden recurrence between `q_z` and `q_(z+1)`; a contact dual is
only field-linear, not automatically linear over the outer polynomial ring.
The Lean file records this disjoint-support identity as
`pureSeedColumn_coeff` and `pureSeedColumn_coeff_other`.

The general raw boundary formula is literal first-jet evaluation.  For the
pure monomial `p(X) Z^z`, its `Z` coordinate is
`z*gamma^(z-1)*p(xi)`.  This is exactly the right side encoded by
`pureSeedBoundaryScalar` and `pureSeedBoundaryRHS`.  The deterministic K0
model's `raw_boundary_column` is the centered `gamma=0` specialization, where
only total active degree one remains visible.

## Formal receipt

File:

```text
.experiments/K0ZeroCostPureSeedDualEdge6900.lean
```

Main declarations:

* `quotientEvalNumerator`: the unique reduced numerator representing
  evaluation at `xi`;
* `quotientTopPairing_evalNumerator`: its exact pairing identity;
* `quotientEvalNumerator_ne_zero`: the evaluation carrier is nonzero;
* `full_window_eval_forces_reduced_numerator`: any full-window inhomogeneous
  evaluation equation forces the reduced numerator to be the evaluation
  carrier;
* `m47_all_pure_seed_bands_force_exact_numerators`: simultaneous target m47
  statement for all `Fin 3758` legal seed bands and arbitrary boundary seed
  `gamma`;
* `exists_all_pure_seed_packet_with_nonzero_Z_numerator`: exact nonclosure
  witness with `lambda_Z=1` satisfying all pure-seed equations.

Checked with a 7.5-GiB virtual-memory ceiling and one Lean worker:

```bash
ulimit -v 7864320
LEAN_PATH=.experiments LEAN_NUM_THREADS=1 \
  lake env lean -j1 -o .experiments/K0ZeroCostPureSeedDualEdge6900.olean \
  .experiments/K0ZeroCostPureSeedDualEdge6900.lean
```

Elapsed time was about 3.2 seconds.  The printed axiom sets contain only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`,
`native_decide`, or unsafe evaluator axiom.

## Structural interpretation

The evaluation numerator has the familiar divided-difference representative

```text
E_xi = (A(X) - A(xi)) / (X - xi)
```

inside `K[X]/(A)`.  The formal interface intentionally characterizes it by
the perfect pairing, avoiding a second polynomial-division proof.  This gives
the correct seed recurrence boundary condition: any future coupled PC edge
must constrain the scalar derivative sequence
`z*gamma^(z-1)*lambda_Z*E_xi`.  Merely adding `Z^2`, `Z^3`, or all remaining
pure seed degrees only determines more members of that sequence and cannot
eliminate `lambda_Z`.
