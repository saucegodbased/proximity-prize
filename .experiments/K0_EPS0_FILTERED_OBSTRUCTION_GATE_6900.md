# K0 epsilon-zero filtered obstruction gate

## Verdict

**RED as a generic confluence/factorization lemma.**  The corrected m6,
L8-to-L9 control is GREEN only vacuously: its complete filtered lower-grade
obstruction has rank zero, before imposing any epsilon-row condition.  The
smaller m4, L4-to-L5 control has a rank-15 obstruction with only two error
nodes.  Its full rank 15 survives after setting to zero each of:

- the one literal epsilon-zero scalar row per error;
- every literal epsilon-zero row at the error nodes;
- the first three scalar epsilon rows per error; and
- the last three scalar epsilon rows per error.

In particular, `15 > 3 * 2`, so this valid chamber rules out factorization of
the obstruction through **any** at-most-`3e`-dimensional packet as a uniform
formal-contact theorem.  A target result would need extra target-specific
structure; it cannot follow from generic triangularity or confluence alone.

## Exact map being tested

For an old passive cap `L` and its exact successor face, split the literal
contact map by passive degree.  The local row coordinates are

```text
(node, eps, S, T, R, Z)
```

and passive degree is `S + T + R + Z`.  Contact uses exactly

```text
X -> x + eps
Y -> u0 + u1*Z + eps*R - eps^2*S + eps^3*T  (mod eps^m).
```

Let

```text
C : old cap-L source -> rows of passive degree <= L
A : exact cap-(L+1) face -> rows of passive degree L+1
B : exact cap-(L+1) face -> rows of passive degree <= L.
```

Old columns have no degree-`L+1` component.  The associated top-face kernel is
`ker A`, and the actual filtered connecting obstruction is

```text
delta : ker(A) -> coker(C),     v |-> [B v].
```

This definition is important: projecting raw rows and measuring their rank is
not a test of liftability.  The old contact image must be quotiented first.

For a selected face-only row packet `E`, the script forms the exact block map

```text
(o,v) |-> (C o + B v, A v, E v).
```

Rank-nullity then gives the basis-free identity

```text
rank(delta restricted to ker(A) intersect ker(E))
  = rank([full contact; face-only E]) - rank(C) - rank([A;E]).
```

Thus a reported zero is exactly the requested kernel inclusion

```text
ker(A) intersect ker(E) <= {v | Bv is in image(C)}.
```

## Row packets

Only nodes outside the retained agreement set are called error nodes.

- `error_eps0_scalar_1e`: the row `(eps,S,T,R,Z)=(0,0,0,0,0)` at each error;
- `error_eps0_all_rows`: every lower-passive row with `eps=0` at each error;
- `error_first3_scalar_le_3e`: scalar rows with `eps=0,1,2` at each error;
- `error_last3_scalar_le_3e`: the final three scalar epsilon rows at each error.

The last two are literally bounded by `3e`.  The script also reports whole
first-three and last-three epsilon layers, but those are much larger than
`3e` and in m4 kill the associated kernel completely, so their GREEN result is
vacuous.

## Exact ranks over F_101

### Corrected m6, L8 -> L9

Parameters are
`(n,w,g,m,B,s,U,L,k,n0)=(11,5,8,6,2,1,8,8,0,1)`, with three error nodes.
There are 4,764 old columns and 859 exact-face columns.

```text
rank C       = 4719
rank A       =  726
rank full    = 5445
dim ker A    =  133
rank delta   = 5445 - 4719 - 726 = 0
```

All 133 top-face kernel directions already lift through the complete old
contact image.  Therefore every packet restriction passes, but none detects or
explains anything.  Notably, the one-row-per-error packet and both three-scalar
packets have rank zero on `ker A` here.

### Corrected m4, L4 -> L5

Parameters are
`(n,w,g,m,B,s,U,L,k,n0)=(6,2,4,4,2,1,6,4,0,1)`, with error nodes 1 and 4.
There are 546 old columns and 225 exact-face columns.

```text
rank C       = 539
rank A       = 180
rank full    = 734
dim ker A    =  45
rank delta   = 734 - 539 - 180 = 15
```

The packet results are:

| packet | rows | rank on `ker A` | dim packet-zero top kernel | obstruction rank after packet-zero | result |
|---|---:|---:|---:|---:|---|
| epsilon-zero scalar (`1e`) | 2 | 2 | 43 | 15 | RED |
| all epsilon-zero error rows | 32 | 16 | 29 | 15 | RED |
| first three scalar rows (`<=3e`) | 6 | 6 | 39 | 15 | RED |
| last three scalar rows (`<=3e`) | 6 | 5 | 40 | 15 | RED |
| all rows in first three epsilon layers | 128 | 45 | 0 | 0 | vacuous |
| all rows in last three epsilon layers | 180 | 45 | 0 | 0 | vacuous |

The strongest useful falsification is not just that a chosen packet failed:
the obstruction image itself has dimension 15, while any `3e` packet here has
codomain dimension at most 6.  No alternative choice of six scalar aggregates
can factor this obstruction.

## Boundary convention and scope

This gate is contact-only, so no boundary row enters any matrix.  The formal
boundary convention remains

```text
(Y,R,S,Z) = (P, P', Hasse_2(P), gamma),  Hasse_2(P)=P''/2.
```

Ordinary `P''` is never substituted for `S`.  The experiment is a finite exact
counterexample to a *generic* factorization theorem.  It does not prove the
target obstruction is large; it says the target route must exploit a special
identity absent from the formal contact filtration itself.  Likewise, the m6
rank-zero event must not be promoted as evidence for epsilon-zero detection.

## Reproduction

```bash
python3 .experiments/k0_eps0_filtered_obstruction_gate_6900.py
```

The script pins its exact ranks with assertions, uses a 4.2 GB address-space
ceiling, and prints canonical/script hashes plus runtime and peak RSS.  Final
receipt hashes are recorded in the commit message and script output.
