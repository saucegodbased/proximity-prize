# K0 zero-cost pure-seed quotient edge (m47 / target profile)

## Decision

The family

```text
X^a Z^z,  0 <= a < 47g,  0 <= z <= 3757,
```

does expose one actual component of a boundary-compatible contact dual.  It
determines the entire reduced quotient numerator in each outer-seed band:

```text
q_z mod A = 0                                      (z != 1),
q_1 mod A = lambda_Z * E_xi                       (z = 1),
```

where `A` is the monic degree-`47g` pole polynomial and `E_xi` is the unique
degree-`<47g` numerator satisfying

```text
topCoeff(((E_xi * p) mod A), 47g-1) = p(xi)
```

for every `p` of degree `<47g`.

This is a genuine quotient-numerator statement, proved from the explicit
perfectness/injectivity of the quotient-top pairing.  It is not a maximal-rank
claim inferred from dimensions.

It is also an exact **STOP for the pure-seed family alone**.  `E_xi` is
nonzero (pair it with `p=1`), so every one of the pure-seed equations is
compatible with `lambda_Z != 0`.  The next useful edge must connect this
distinguished `z=1` numerator to a numerator already forced to zero by a
different PC shape.  More adjacent pure-seed bands do not do that.

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

The boundary formula used in the deterministic K0 model is literal first-jet
evaluation (`k0_constantT_packet_conormal_ablation_6900.py`,
`raw_boundary_column`): a raw monomial has boundary support only when
`y+r+s+z=1`.  Therefore the pure family has boundary zero for `z=0` and
`z>=2`; at `z=1` its `Z` coordinate is `p(xi)`.  This is exactly the right
side encoded by `pureSeedBoundaryRHS`.

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
  statement for all `Fin 3758` legal seed bands;
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
must transport a known-zero numerator into this `E_xi` component.  Merely
adding `Z^2`, `Z^3`, or all remaining pure seed degrees only proves more
independent zero statements and cannot eliminate `lambda_Z`.

