# m69 literal Pascal transpose: fixed-lambda recurrence RED

Date: 2026-09-14 UTC. Scope: lower-6900 m69 source audit only. Production,
score, radius, candidate, and submission roots are unchanged.

## Decision

The fixed-lambda power recurrence used by the conditional m69 dual/Padé
route is **not the transpose of the simultaneous physical source map**.

For one fixed physical tail `(r,s,q)`, let `Y` be the consecutive deficient
contact indices. The shared source at contact `k` contributes to every output
equation `y in Y` with `y<=k`. After retaining the common source-side Hasse
diagonal, the literal map has the form

```text
out_y = sum_(k>=y) binom(k,y) W^(k-y) D_k(U_k).
```

Therefore an arbitrary output dual family `(lambda_y)_(y in Y)` acts on the
source `U_k` through

```text
mu_k = sum_(y in Y, y<=k)
         binom(k,y) W^(k-y) lambda_y,
```

followed by `D_k^T`. The `lambda_y` are independent. In general `mu_k` is
not `lambda*W^k` for one fixed `lambda`, and it does not satisfy
`mu_(k+1)=W*mu_k`.

This is not a normalization issue. The exact counterexample below uses an
adjacent high/low pair whose two Hasse maps have the same depth and order,
and hence the same invertible normalized scalar.

## Literal two-row counterexample

The exact deficient census contains the fixed chain

```text
(r,s,q) = (0,0,26)
Y       = {41,42}
T       = J-r-s = 94.
```

Its first two source widths are

```text
width(41,0,0) = 26*262144 + 258842,
width(42,0,0) = 26*262144 + 127771.
```

Both have Hasse depth/order `(depth,q)=(26,26)`. The coefficient-basis Hasse
weight on both prefixes is the same nonzero scalar

```text
262144^26 mod 2130706433 = 243251425.
```

Thus no varying diagonal can repair the following failure. The first two
transpose covectors are exactly

```text
mu_41 = lambda_41,
mu_42 = 42 W lambda_41 + lambda_42.
```

Now choose, for any nonzero `W`,

```text
lambda_41 = 53,
lambda_42 = -42 W.
```

This pair annihilates the terminal contact **pointwise**, not merely after a
prefix pairing:

```text
mu_94
 = binom(94,41) W^53 lambda_41
   + binom(94,42) W^52 lambda_42
 = 0,
```

because

```text
binom(94,41) = 760365888182828026538367852,
binom(94,42) = 959509335087854414441273718,
53*binom(94,41) = 42*binom(94,42).
```

Nevertheless,

```text
mu_41                 = 53,
mu_42                 = 2184 W,
mu_42 - W*mu_41       = 2131 W != 0
```

in every field of characteristic `2130706433` when `W!=0`. Hence even the
stronger condition `mu_T=0` does not restore the fixed-power recurrence. The
actual terminal condition only asks that `mu_T` annihilate a prefix, so it
cannot imply more.

`M69PascalTransposeFixedLambdaCountergate6900.lean` proves all displayed
identities and the benchmark-characteristic nonvanishing theorem. It compiles
under

```text
LEAN_NUM_THREADS=1 lake env lean -j1 -M3500
```

and reports only

```text
[propext, Classical.choice, Quot.sound].
```

It uses no `sorry`, `admit`, `decide`, `native_decide`, unsafe declaration,
or generated table.

## Exhaustive literal-census extension

The executable

```text
m69_pascal_transpose_fixed_lambda_countergate_6900.py
```

reconstructs all `9,900` fixed `(r,s,q)` chains in the exact m69 deficient
coefficient census. Their lengths range from `1` to `29`; `9,405` chains
have at least two rows.

For every multirow chain, put

```text
a = min(Y),  T=J-r-s,
lambda_a     = T-a,
lambda_(a+1) = -(a+1) W,
lambda_y     = 0 otherwise.
```

Pascal's adjacent-binomial identity gives `mu_T=0`, while

```text
mu_(a+1) - W*mu_a = (a*(T-a-1)-1) W.
```

The script checks this coefficient is nonzero modulo the benchmark prime for
all `9,405` multirow chains. Its integer range is `-1..2131`. The record
stream receipt is

```text
a7a1f667e713807579a7e869636756f13683a2d04870a467ae5b9f92d65b64bf
```

and the canonical JSON receipt is

```text
fa6946ca76c3374f05cd091568b28d4b0160fe84146add6469bb16c9f47cbbec
```

Peak RSS was about `44 MiB`.

## What terminal constraints actually do in the monomial control

The reciprocal-monomial control remains GREEN, but for a different reason.
For `W=X^-2151`, the invariant coordinate

```text
a = outputIndex-y*2151 = sourceIndex-k*2151 mod 262144
```

splits the shared-tail map into scalar Pascal blocks. On the literal two-row
chain above, the executable independently streams all `127797` terminal
coordinates. Every one sees at least `13` available ordinary source contacts;
any two distinct contact columns

```text
(binom(k,41), binom(k,42))
```

have nonzero determinant in the benchmark field. Thus the terminal column is
contained by ordinary Pascal/Vandermonde rank. The minimum-coverage witness is
invariant coordinate `114751`, and `1125` terminal coordinates attain the
minimum `13`.

This is terminal containment by simultaneous Pascal rank, not restoration of
a geometric recurrence. It is a valid clue for a new proof, but only in the
reciprocal-monomial specialization so far.

## Consequences for the active route

The theorem in `M69CorrectedDualRecurrence6900.lean` remains a correct
conditional statement about a direct sum of channels sharing one output
covector. What fails is its use as the physical simultaneous source adapter.
An isolated output equation does have one covector and may use that adapter;
many isolated containments do not allocate the shared `U_k` tails.

Accordingly:

1. The high/low backward recurrence and the small-zero geometric Padé gate
   from `c77f655` are **RED as adapters to simultaneous m69 confluence**.
   Their internal conditional algebra is not retracted, but it currently has
   no edge to the literal shared-tail map.
2. Adding the terminal prefix does not repair that edge. The counterexample
   annihilates its full pointwise transpose and still breaks the first
   recurrence.
3. The correct normalized sequence, at a node where `W!=0`, is

   ```text
   W^-k mu_k = sum_y binom(k,y) W^-y lambda_y,
   ```

   a Pascal/falling-factorial sequence in `k`, not a constant sequence.
   Finite differences produce a hierarchy of the independent `lambda_y`.
4. The next honest route is therefore either a primal simultaneous
   confluence theorem or a dual Pascal-block/finite-difference theorem. Any
   future rational Padé reduction must first be derived from that literal
   transpose; reusing the fixed-lambda recurrence would repeat the adapter
   error.

This countergate closes the source-adapter uncertainty: the old recurrence
does not model the simultaneous source. It does **not** prove or disprove the
arbitrary-rational Pascal confluence theorem, which remains the mathematical
gap to the m69 no-leaf endpoint.
