# K0 low-head contact boundary readout

Date: 2026-09-15 UTC. Scope: lower-6900 local algebra and terminal-route
interface. This is not a target CRT theorem, candidate, or submission.

## Result

The feared semantic obstruction in the extra-node proposal is absent.  An
ordinary literal contact block already determines all four boundary
derivatives.  No augmented ambient-`Y` jet is needed.

For

```text
G(e,S,T,R,Z) =
  Q(x+e,S,u0+u1*Z+e*R-e^2*S+e^3*T,R,Z),
```

and the compatible point `Y=u0+u1*z`, the exact readout is

```text
Q_Y = eval [e^3] d_T G
Q_R = eval_(e=0) d_R G
Q_S = eval_(e=0) d_S G
Q_Z = eval_(e=0) d_Z G - u1*Q_Y.
```

`K0LowHeadContactBoundaryReadout6900.lean` proves the four polynomial chain
rules, the coefficient extraction identity, the combined factorization, and
surjectivity of this four-scalar readout.  An explicit local section sends a
boundary vector `(y,r,s,z)` to

```text
y*(e^3*T + u1*Z) + r*R + s*S + z*Z.
```

The `u1*Z` term cancels the chain-rule correction in the fourth coordinate.
All results are characteristic-independent; the `e^3*T` coefficient is used
directly, so no division by `3!` occurs.

## Exact scope condition

The low head must retain epsilon order three.  For a final-three split this
means

```text
m-3 > 3, equivalently m >= 7.
```

The lower-6900 target has `m=47` and low-head order `44`, so the condition is
satisfied.  Small `m=4` or `m=6` controls cannot justify this readout even if
their boundary rank happens to become four by another mechanism.

The four section monomials are legal in the target local box: `e^3*T`, `R`,
`S`, and `Z` obey `T-degree <= epsilon-degree`, the `B=16`, `s=8`, and
`L=3757` caps.  This proves local readout surjectivity, not global source
realization.

## What remains

The correct global target is now only the rank gain of four scalar rows:

```text
rank(old low heads, fresh boundary4) = rank(old low heads) + 4.
```

Surjectivity onto an entire extra 213,740,910-dimensional low-head block is
strictly stronger and unnecessary.  The existing 9.03-trillion dimension
margin is useful capacity, but cannot prove this four-row independence.  A
target-uniform dual/CRT or recurrence theorem is still required.

## Verification

```bash
LEAN_PATH=.experiments lake env lean \
  .experiments/K0LowHeadContactBoundaryReadout6900.lean -j1 -M4200
```

Replay takes about 21 seconds.  Every printed theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`.  There is no `sorry`, `admit`,
`decide`, `native_decide`, explicit axiom, or unsafe declaration.

