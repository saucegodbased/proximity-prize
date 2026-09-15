# Heterogeneous linear interpolation source: exact conditional GO / uniform STOP

## Question

On the exact sharp projective leaf, try one relation

```
A(X,g) + B(X,g) P_g(X) + C(X,g) S_g(X) = 0
```

where `deg P_g <= 131071`, `deg S_g <= W`, every candidate agrees with
`U0+g*U1` at at least `T=180413` nodes, and every scalar agrees with the
fixed `centre` on the same nodes.  Give `A`, `B`, and `C` seed degree at most
17 (width 18), and X-degree windows `<T`, `<T-w`, and `<T-W` respectively.

This route was deduplicated against the existing first-order/O2, determinant,
and top-fibre experiments.  No existing artifact implements this literal
three-block all-node coefficient map.

## What is now formal

`HeterogeneousLinearInterpolationSource6900.lean` defines the finite linear
map without constructing a matrix.  At node `i`, seed coefficient `k` is

```
A_k(i) + B_k(i) u0(i) + C_k(i) centre(i) + B_{k-1}(i) u1(i).
```

It proves:

* the exact source and target finranks;
* a nonzero kernel whenever the source finrank exceeds the target finrank;
* coefficient-kernel membership is the intended all-node identity for every
  seed specialization;
* if a candidate `P` and scalar `S` agree at at least `T` distinct nodes and
  satisfy the declared degree caps, the node identity interpolates to the
  genuine global polynomial syzygy `A_g+B_g P+C_g S=0`;
* all target arithmetic below.

The file replayed under `run_lean_4g_capped.sh` (`-M3500`, no matrix), and all
printed axioms are only `propext`, `Classical.choice`, and `Quot.sound` (some
pure arithmetic receipts use only `propext`).

## Exact arithmetic

For the proposed nominal cap `W=133225`,

```
source      = 18*(180413 + 49342 + 47188) = 4,984,974
constraints = 262144*19                    = 4,980,736
surplus                                      =     4,238.
```

The earlier rough surplus `19,037` was wrong; `4,238` is exact.

However, the sharp package's `133225` is a **lower bound on its allowance**,
not a uniform upper bound on the actual scalar degrees.  It supplies

```
deg S_g <= W_actual,
133225 <= W_actual <= 149485.
```

The C-window must therefore be `<T-W_actual` for the global interpolation
step.  Across the sharp range, the dimension gap is positive exactly when

```
W_actual <= 133460.
```

The last positive point and first negative point are sharp:

```
W=133460: source=4,980,744, surplus 8
W=133461: source=4,980,726, deficit 10.
```

At the proved uniform upper cap,

```
W=149485: source=4,692,294, deficit 288,442.
```

Thus this is a binary **GO conditional on `W_actual <= 133460`**, and a
binary **STOP as a uniform consumer of the present exact sharp package**.
Using the lower endpoint as though it bounded every scalar would make the
global-syzygy degree proof false.

## Identity-node split

The existing sharp split gives a branch with at least `261852` fixed identity
nodes, hence at most `292` nonidentity nodes.  That fact does not repair the
missing scalar-degree bound in the all-node construction: the polynomial
`C_g*S_g` still has to have degree `<T` before agreement interpolation can be
used.

It suggests a different, not-yet-proved source: impose the known fixed scalar
identity freely on the identity nodes and build corrections only on the at
most 292 exceptional nodes.  But a useful correction must also be shown not
to be a masked multiple of the already-known fixed identity.  The existing
`arbitrary_subset_is_fixed_identity_locus` countergate confirms that the
near-global affine locus alone has no hidden algebraic structure.  Therefore
`|nonidentity|<=292` is an input for a new quotient/rank theorem, not a reason
the present 4,238-dimensional kernel is automatically independent.

## Next falsification

The cheapest possible rescue is a degree-histogram theorem on the same
retained `Good`:

```
many g in Good have deg(S_g) <= 133460.
```

No such field is currently present in `SharpProjectiveResidualPackage`.
Without a new argument from scalar injectivity, Frobenius-fixity, agreement,
or the fixed identity, plain pigeonhole gives no lower bound on that low-degree
subfamily: all retained scalars are consistent with lying in degrees
`133461..W_actual`.  This is the next precise gate.

