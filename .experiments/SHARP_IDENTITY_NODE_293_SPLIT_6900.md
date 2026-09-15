# Sharp identity-node 293 split for 6900

## Outcome

The sharp two-source/projective/high-E leaf now feeds an exact, formal
identity-node dichotomy without changing its witnesses.  Let

```
F_i(gamma) = row0(i) + gamma * row1(i)
```

be the evaluation at domain node `i` of the retained scalar residual
identity.  Every retained seed satisfies `F_i(gamma)=0` on every node of its
original agreement set.

Define `Z` to be the nodes where both fixed coefficients vanish.  Outside
`Z`, a node can belong to the agreement support of at most one seed: two
distinct roots of a nonzero affine polynomial would force both coefficients
to vanish.  Choosing one escaping node for each non-core seed therefore
injects the escaping seeds into the complement of `Z`.

Lean now proves that the exact benchmark-facing leaf implies either

1. `Z.card <= 261851`, and a core of at least
   `263611557201523206` seeds keeps its complete original agreement set
   inside `Z`; or
2. `261852 <= Z.card`, equivalently at most 292 domain nodes are outside the
   fixed identity locus.

The proof is in:

* `FixedLinearNodeSupportConcentration6900.lean`: generic affine-root
  injection and residual evaluation adapter;
* `IdentityNode293Dichotomy6900.lean`: exact cardinal split; and
* `TwoSourceSharpIdentityNodeSplit6900.lean`: same-witness attachment to the
  sharp projective/high-E incidence leaf.

All three targeted checks are green.  The two new endpoint declarations use
only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`,
`admit`, `decide`, `native_decide`, or unsafe declaration.

## Why 293 is exact

At scalar allowance `W=133225`, use the unrestricted weighted-helper profile

```
k = 61
m = 550
B = 99227150
M = 744
D = 244
```

on the subtype of identity nodes.  With `|Z|=261851`, the exact ledger is

```
rank per node       =   1,503,271,269
columns             = 394,079,022,659,582
kernel lower bound  =     445,937,600,663
J211 charge         =     438,524,534,360
J margin            =       7,413,066,303
D55 charge          =     445,520,033,855
D margin            =         417,566,808
```

At `|Z|=261852`, the D55 margin is `-1,085,704,461`.  Thus 293 fewer node
constraints are exactly the first integer point at which this profile turns
green.

Importantly, this is **not** the previously rejected arbitrary puncturing
argument.  Arbitrary puncturing reduced the agreement mass from 180413 to
180120 and invalidated `B=m*A`.  Here only seeds whose agreement sets escape
`Z` are discarded; every surviving seed retains all 180413 original
agreement nodes.  At most one seed is charged to each deleted node.

Even conservative already-formal target/charge receipts are positive on
`|Z|<=261851`:

```
columns lower       = 394,078,867,563,530
kernel lower        =     445,782,504,611
relaxed J upper     =     438,719,012,160  (margin 7,063,492,451)
relaxed D upper     =     445,571,141,730  (margin   211,362,881)
```

## Remaining proof debt

This is not yet a ProtocolClaim6900 proof.

* Small-`Z` branch: instantiate the generic weighted source on the subtype
  `{i // i in Z}`, specialize the numeric wrappers to `card <= 261851`, and
  connect the positive helper to the existing absorption/count consumer over
  the unchanged 180413-point supports.
* Large-`Z` branch: dispose of the case with at most 292 exceptional nodes.
  A promising exact consequence is
  `deg(E0) + |Z^c| <= 18414 + 292 = 18706`; localizing an original
  degree-81731 recurrence therefore reaches grade at most 100437 and leaves
  30634 shifts.  This must still be shown to provide equations independent of
  the scalar-source tautology.
* Degree window: after closing `W=133225`, either generalize the construction
  uniformly or cover the remaining allowances through 149485.

Current honest state: the witness-compatibility and agreement-loss risks of
this route are closed; helper integration, the <=292 branch, and full-window
coverage remain load-bearing.
