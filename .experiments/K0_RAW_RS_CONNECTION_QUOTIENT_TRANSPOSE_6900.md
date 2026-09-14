# K0 raw R/S connection and quotient-transpose checkpoint

Date: 2026-09-14 UTC. Scope: full `m=47`, exact-`G`, lower-6900 source.
This is a compiled structural checkpoint, not a rank-four proof or candidate.

## Result

Write the flattened complete-contact coordinates as

```text
(epsilon,S,T,R,Z)
V = u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

The Hasse-normalized jet connection

```text
delta = partial_epsilon + 2 S partial_R + 3 T partial_S
```

satisfies, as literal multivariate-polynomial identities,

```text
delta(V) = R,       delta(R) = 2 S,

delta C[a+1,0,y+1,0,z]
  = (a+1) C[a,0,y+1,0,z] + (y+1) C[a+1,0,y,1,z],

delta C[a+1,0,0,1,z]
  = (a+1) C[a,0,0,1,z] + 2 C[a+1,1,0,0,z],

delta C[a+1,0,y+1,1,z]
  = (a+1) C[a,0,y+1,1,z]
    + (y+1) C[a+1,0,y,2,z]
    + 2 C[a+1,1,y+1,0,z].
```

Here `C[a,s,y,r,z]` is exactly

```text
(x+epsilon)^a S^s V^y R^r Z^z,
```

the literal raw contact formula, not a centered surrogate and not a
`weightedTerm` kernel vector. Applying any complete-contact dual gives the
three corresponding transpose equations. The clean `R -> 2S` equation at
`y=0` explains the stable finite ablation from commit `59915e8`: `R^2` is
absent on that edge, while positive Y-degree necessarily creates the `R^2`
companion.

## The recurrence is legal for both source profiles

The file packages the actual relaxed-source inequalities

```text
2s+r <= B,
s <= sCap,
s+y+r <= U,
s+y+r+z <= L,
a + w*y + (w-1)*r + (w-2)*s < D.
```

All three displayed connection recurrences preserve these inequalities:

- the active degree `s+y+r` and passive degree `s+y+r+z` are unchanged;
- every output weighted cost is one below the input cost;
- the first edge needs only `B>=1`;
- the R/S edges need only `B>=2` and `sCap>=1`;
- `z` is unchanged.

Thus the low `{1,R,S}` connection is uniform in `(sCap,L)`. In particular it
is legal for both `(sCap,L)=(8,3757)` and the shallower green profile
`(6,5107)` from `da056e7`. Nothing in this local recurrence needs curvature
layers 7 or 8, and a larger Z cap is harmless. This closes the raw
**source-legality** portion of the connection gate.

## Literal boundary coupling

For a boundary tangent
`(lambdaS,lambdaY,lambdaR,lambdaZ)` at `(S0,Y0,R0,gamma)`, the raw-shape
right side is the directional derivative of `S^s Y^y R^r Z^z`. The first
coordinates are therefore

```text
b_pure(1) = lambdaZ,
b_R(0)    = lambdaR,
b_S(0)    = lambdaS,

b_R(z) = lambdaR gamma^z + R0 b_pure(z),
b_S(z) = lambdaS gamma^z + S0 b_pure(z).
```

These identities are formalized for arbitrary boundary seed `gamma`. They
are the exact affine coupling of the R and S quotient numerators to the
pure-seed `z=1` evaluation numerator.

## Exact quotient defect and STOP boundary

Let `A` be the monic degree-`M` CRT modulus, and let `E_xi` be the unique
reduced quotient numerator representing evaluation at `xi` under the
perfect quotient-top pairing. For a strip of source width `M-c`, the compiled
equivalence is

```text
pair(q,p) = scalar * p(xi) for every deg p < M-c

iff

(q - scalar E_xi) mod A = 0
or deg((q - scalar E_xi) mod A) < c.
```

At the target constants this leaves

```text
raw R: degree < 131070 = w-1,
raw S: degree < 131069 = w-2.
```

This is not just a loose upper bound. The file constructs, for every scalar,
an explicit compatible numerator `q = scalar E_xi + 1` whose complementary
defect is nonzero. Therefore pure seed plus independently treated R/S strips
does **not** force `(lambdaY,lambdaR,lambdaZ)` into a one-dimensional jet and
does not make the S interpolant small enough. Any such conclusion must use
the coupled connection, not stripwise dimension counting.

## Remaining global gate

The raw contact identities and source legality are now exact. What is not yet
proved is the required agreement/boundary confluence for the transposed
connection: after composing the compatible all-node dual with `delta`, one
must identify the induced boundary functional (or a commutator corrected by
the evaluation row) and prove the agreement contribution cancels. Equivalently,
the existing full-source realization/splice needs the coupled `eta o delta`
row, not merely independent quotient numerators.

That is the precise next theorem. Treating the low-degree defects as zero, or
asserting maximal rank from dimensions, would be invalid.

## Formal artifact

`K0RawRSConnectionTranspose6900.lean` compiles in about eight seconds with
one Lean thread under an 8 GiB virtual-memory cap. Its printed axioms are only
the accepted `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx`, `native_decide`, or unsafe oracle.

