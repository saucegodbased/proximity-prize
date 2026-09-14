# K0 critical raw-S nilpotent staircase

Date: 2026-09-14 UTC. Scope: full m47 exact-G lower-6900 source. This is a
compiled local/contact identity and source-legality receipt, not the global
rank-four theorem.

## Exact identity

At node `i`, set

```text
W_i = u0_i + u1_i Z,
N_i = epsilon R - epsilon^2 S + epsilon^3 T,
V_i = W_i + N_i.
```

Because `epsilon | N_i`, one has `epsilon^m | (V_i-W_i)^m`. Expanding the
binomial gives the exact truncated-contact relation

```text
S V_i^m =
  - sum_(0 <= y < m) (-1)^(y+m) binom(m,y)
      S V_i^y W_i^(m-y)                (mod epsilon^m),

W_i^(m-y) =
  sum_(0 <= z <= m-y) binom(m-y,z)
      u0_i^(m-y-z) u1_i^z Z^z.
```

Thus the first critical column `Y^m S` closes against exactly the complete
causal staircase `Y^y S Z^z` with `y<m`, `z<=m-y`. This algebraic identity
explains all three sharp features of the deterministic m5/m6 filtration:

- nothing closes before Y-degree m;
- the critical band cannot close without the lower-Y S prefix;
- seed zero is enough, because the required positive Z bands occur on the
  subcritical side of the expansion.

The Lean artifact proves divisibility in the literal flattened
multivariate contact algebra, not by a rank count.

## Target legality

For m47, the critical band has

```text
X^a Y^47 S,  0 <= a < 2,188,005.
```

Every lower term in the binomial identity has `y<47`, `z<=47-y` and the
same `a`. The compiled `m47_critical_and_lower_staircase_legal` theorem
checks all five real relaxed-source inequalities. It is uniform for every
`sCap>=1` and `L>=48`, so both `(sCap,L)=(8,3757)` and `(6,5107)` contain
the entire relation.

## Exact remaining global obstruction

The coefficients `u0_i^(...) u1_i^(...)` vary with the node. The local
identity therefore does not yet give one global raw source vector: they must
be synthesized by the tapered X windows, with the agreement part canceled
and the error part retained. On an exact agreement set, write

```text
u1_i = Q(x_i),
u0_i = P(x_i) - gamma Q(x_i),
W_i = P(x_i) + (Z-gamma)Q(x_i).
```

The naive global lift

```text
S * (Y - P(X) - (Z-gamma)Q(X))^m
```

has the correct contact divisibility but is not automatically inside the
weighted source: its low-Y coefficient powers of the degree-`<g`
interpolant Q can exceed the corresponding X tapers. The global theorem must
show that the `{1,R}` connection and the causal lower-S staircase absorb
exactly this high-X tail. The downstream endpoint only needs the resulting
boundary identity `lambdaS • Q'' = 0` (commit d215db5); no stronger recovery
of Q is required.

This node-coefficient/taper confluence is the only unproved part of this
checkpoint. Treating the nodewise binomial relation as a global linear
combination would be invalid.

## Artifact

`K0CriticalRawSStaircase6900.lean` compiles in about four seconds with one
Lean thread under an 8 GiB virtual-memory cap. Printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`,
`native_decide`, or unsafe oracle.

