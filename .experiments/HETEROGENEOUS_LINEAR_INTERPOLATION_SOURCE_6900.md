# Heterogeneous interpolation: exact source GO, independence STOP

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

`HeterogeneousLinearInterpolationSharpAdapter6900.lean` then applies the
same map to the exact `TwoSourceSharpProjectiveHighEIncidenceLeaf`.  It keeps
the literal `U/Gamma/agreement/selected/Good/scalar/centre` and proves all
retained candidates satisfy the global syzygy whenever the package allowance
fits a supplied positive dimension gap.

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

Thus width 18 is a binary **GO conditional on `W_actual <= 133460`**, and a
binary **STOP uniformly**.  Using the lower endpoint as though it bounded
every scalar would make the global-syzygy degree proof false.

## Adaptive seed width

Width 18 is not intrinsic.  For seed width `r`, the signed gap is

```
r * (148024 - W_actual) - 262144.
```

Consequently every `W_actual <= 148023` has some positive raw gap.  The worst
reachable endpoint has an especially clean receipt:

```
W=148023, r=262145:
source      = 262145 * 262145 = 68,720,001,025
constraints = 262144 * 262146 = 68,720,001,024
surplus                                 = 1.
```

At `W=148024`, every new seed layer adds exactly 262144 source coefficients
and 262144 equations, while the target retains its initial 262144 equations.
No width can make the raw gap positive.  Larger W is worse.  The formal
adaptive source therefore narrows the pure degree obstruction to
`W_actual >= 148024` (the top 1462 possible allowance values).

This is a dimension/source GO, not yet an endpoint GO: the guaranteed kernel
vector still has to be independent of the known fixed scalar relation.

## Identity-node split

The existing sharp split gives a branch with at least `261852` fixed identity
nodes, hence at most `292` nonidentity nodes.  The fixed scalar relation is
not itself an all-node nodal-kernel vector: candidate and scalar agreement is
known only on each selected agreement set.  But on every fixed identity node
its two seed coefficients vanish.  Multiplying it by the support locator of
the nonidentity nodes therefore produces an all-node identity.

This masking statement is now formal on the exact leaf:

```
exceptional.card <= 292
deg locator(exceptional) <= 292
locator(exceptional)(x_i) * (row0(i)+g*row1(i)) = 0
```

for every domain node and every seed.

The producer relation has seed degree one.  After restoring the degree bounds
on its anchored numerators `a,b` (not currently fields of the sharp package),
the common X-multiplier width is

```
h = 49342 - deg(E0),       h >= 30928.
```

The 292-node locator leaves at least 30636 X degrees of masked multiples.
Thus the tautological family is already on the order of `(r-1)*30636`:

* at r=18 this dwarfs the guaranteed raw surplus 4238;
* at r=262145 it dwarfs the guaranteed adaptive surplus 1 by billions.

Therefore raw nullity does **not** certify a second independent syzygy.  The
large-identity branch makes the dependence obstruction worse, not better.
The existing `arbitrary_subset_is_fixed_identity_locus` countergate also
confirms that the affine locus alone has no extra algebraic structure.

There is a conditional quotient window worth preserving.  Put `t=|Z^c|` and
`delta=148024-W`.  From `W <= 131071+deg(E0)`, one gets
`h-delta <= 32389`.  If `t >= 32390` and `r>262144`, the raw-kernel lower
bound can numerically exceed the masked-multiple bound.  Turning that number
into an independent source still requires the load-bearing classification:
every syzygy aligned with the fixed relation must be one of those locator
multiples.  No such exact quotient/divisibility theorem currently exists.

Binary endpoint result: **STOP** until that independence theorem (and the
dropped `a,b` degree bounds it needs) is supplied.

## Resource audit

The generic source, including the symbolic `r=262145` existence theorem,
replays under Lean's `-M3500` allocator cap because no matrix is built.
The exact-leaf adapter passes under `-M5500` but the already-large imported
sharp environment does not load under `-M3500`.  More importantly, downstream
proofs must keep the width symbolic: expanding `specializeFamily` as a
262145-term finite sum or running `decide`/`native_decide` on it would be
verifier-unsafe.  The current proofs manipulate the linear map and sums
abstractly and do not perform that expansion.

## Next falsification

One possible rescue is a degree-histogram theorem on the same retained
`Good`:

```
many g in Good have deg(S_g) <= 148023.
```

No such field is currently present in `SharpProjectiveResidualPackage`.
Without a new argument from scalar injectivity, Frobenius-fixity, agreement,
or the fixed identity, plain pigeonhole gives no lower bound on that low-degree
subfamily: the current API is consistent with every retained scalar lying in
the top `148024..W_actual` range.  A histogram does not solve independence in
the lower range, either; the masked-multiple quotient remains the first gate.
