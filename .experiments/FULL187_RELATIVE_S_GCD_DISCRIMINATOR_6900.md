# Full187 relative-curvature gcd discriminator

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production file,
candidate, score, claim, build, comparator run, or submission was changed.

## Decision

**STOP** treating a nonconstant primitive common factor in curvature `S` as
an automatic consequence of the Full187 contact kernel. In a faithful exact
small control, the primitive common gcd is `1`, even though ten genuine
selected polynomial graph sections vanish on every row of the complete
kernel.

The surviving direction is the residual ideal / ruled-projection dichotomy:
the selected sections can live in a common zero scheme of codimension at
least two without lying on a height-one relative-`S` factor. A positive
target route must retain that ideal or prove an extra target-specific
height-one theorem. It cannot replace the terminal producer by “take the
common `S`-gcd.”

## Exact control

The executable reuses the received affine line and ten close non-pencil
degree-two candidates from
`moving_scalar_pade_component_counterexample.py`. It constructs the literal
all-seven-node order-two contact matrix over `GF(11)` for

```text
(n,w,g,m,D,s,t,J,L) = (7,2,4,3,12,2,1,5,7),  D=m*g.
```

Its local coordinate change is exactly

```text
Y = u0 + Z*u1 + E + T*R - T^2*S/2,
wt(T)=1, wt(E)=3.
```

The graph specialization is the formal Full187 one
`(Y,R,S,Z)=(P,P',P'',gamma)`; the minus sign belongs to the local coordinate
change, not to the global graph value.

The complete exact matrix gives

```text
source columns       971
contact rows          987
actual rank           941
kernel dimension       30
closed rank bound      952
closed margin           19
```

Regarding every kernel basis row as a polynomial in `S` over
`GF(11)(X,Y,R,Z)`, its `S`-degree histogram is

```text
degree 0:  1 row
degree 1: 29 rows.
```

The degree-zero row is nonzero (409 terms, base multidegree
`(10,5,1,7)` in `(X,Y,R,Z)`). It is a unit over the coefficient fraction
field, so the monic common gcd in `GF(11)(X,Y,R,Z)[S]` is exactly `1`.
Equivalently, the primitive common gcd in curvature is `1`; division changes
no row, and the quotient `S`-degree histogram remains `(0:1, 1:29)`.

All ten selected candidates have exactly four agreements. The executable
checks all `10*30=300` graph substitutions as exact zero polynomial
identities in `X`; their maximum affine-pencil occupancy is only two. Since
the primitive gcd is `1`, none lies on a primitive common-gcd branch. Thus
the vanishing is genuinely ideal-theoretic rather than explained by one
relative hypersurface.

This primitive calculation intentionally treats nonzero elements of
`GF(11)[X,Y,R,Z]` as coefficient-field units. It therefore rules out a
common factor of positive `S`-degree; it does not by itself rule out
`S`-independent content, a specially selected pair/subspace with a factor,
or a target-only structural theorem.

## Replay

```text
prlimit --as=3221225472 python3 \
  .experiments/full187_relative_s_gcd_discriminator_6900.py
```

The successful replay took about six seconds and reported peak RSS
`108196 KiB`. Stable receipt hashes:

```text
canonical payload sha256
  8ebca1430353be0c7fd69df9ef6976af3afe3b9ab41ff078a99dc7d656dfacd0
script sha256
  a35123b4b75577045a75aa7bf0a588d96ae4f45908627aaed5a2aed5058d3ecb
```

