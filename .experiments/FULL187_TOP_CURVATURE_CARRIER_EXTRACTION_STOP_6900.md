# Full187 top-curvature carrier extraction: exact STOP gate

Date: 2026-09-14 UTC

Status: **STOP for the proposed free extraction theorem.**  The highest
curvature derivative is nonzero and `S`-free, but the order-60 contact premise
is not preserved.  This note does **not** prove that no specially chosen
global kernel vector can have a good top coefficient; such a choice would need
a new simultaneous-kernel theorem and cannot be obtained by commuting the
derivative through the existing contact equations.

## Proposed splice

The Full187 passive source is

```text
SeedPoly K = Polynomial (MvPolynomial (Fin 4) K)
```

with inner variables `(X,Y,R,S)` and outer variable `gamma`.  Given the
nonzero source `Q`, the proposal was to let `d` be its maximum inner `S`
degree and use

```text
H = (pderiv S)^[d] Q.
```

Because the challenge characteristic is much larger than `d <= 10`, the
usual top-derivative argument does prove that `H` is nonzero and `S`-free.
After flattening the outer variable, it is algebraically one fixed P4
polynomial in `(X,Y,R,gamma)`.  The missing claim was that `H` retains every
order-60 node contact equation, so the existing root-forcing theorem could be
re-run on it.

## False gate: the substitution is not curvature-constant

The literal local substitution is

```text
X |-> x + Z
Y |-> u + E + Z*R - (Z^2/2)*S
R |-> R
S |-> S.
```

It fixes the source generator `S`, but its image of `Y` also depends on local
`S`.  Hence the chain rule is

```text
d/dS (localSub Q)
  = localSub (dQ/dS) - (Z^2/2) * localSub (dQ/dY),
```

not `localSub (dQ/dS)`.  The contact truncation ignores the exponents of `R`
and `S`, but that does not remove the extra term: `Z^2/2` has contact weight
two while an exposed `Y` can cost three units.  One curvature derivative can
therefore lose one unit of contact.

## Exact Full187-shaped counterexample

Put

```text
L = Y - X*R + (X^2/2)*S
Q = X^57 * L.
```

At the node `(x,u)=(0,0)`, the literal local substitution sends `L` to `E`.
Therefore

```text
localSub Q = Z^57 * E,
contactWeight = 57 + 3 = 60,
contactTruncation 60 (localSub Q) = 0.
```

The maximum inner curvature degree is exactly one.  Its top derivative is

```text
dQ/dS = (1/2) * X^59,
localSub (dQ/dS) = (1/2) * Z^59,
contactWeight = 59 < 60.
```

Thus, when `2 != 0`,

```text
contactTruncation 60 (localSub (dQ/dS)) != 0.
```

This is not an out-of-box toy.  Expanding `Q` gives exactly the three source
monomials

```text
(a,y,r,s,seed) = (57,1,0,0,0),
                   (58,0,1,0,0),
                   (59,0,0,1,0).
```

All three satisfy the actual Full187 support restrictions

```text
y+r+s <= 82,
r+s   <= 21,
s     <= 10,
seed+y+r+s <= 2703,
a + 131071*y + 131070*r + 131069*s < 10824780.
```

Their last weighted degree is the same number, `131128`, far below
`10824780`.  The example has outer-seed degree zero, so it embeds unchanged in
the passive `SeedPoly` source.

## The numerical loss exactly defeats root forcing

Suppose one grants the strongest generic conclusion compatible with the
chain rule: `d` curvature derivatives retain contact order only `60-d`.
Taking the top `S` coefficient saves `d*(w-2) = 131069*d` units of weighted
degree.  At the target agreement `A=180413`, however,

```text
10824780 - 131069*d
  = (60-d)*180413 + 49344*d.
```

For every `1 <= d <= 10`, the extracted degree bound is therefore *above*
the available root-forcing budget by `49344*d`.  Here

```text
49344 = A - (w-2) = 49342 + 2,
```

where `49342` is the target agreement/error gap.  So the generic
contact-loss theorem cannot feed the accepted P4 carrier machinery either.

If full order 60 somehow held, the formal support caps of the top coefficient
would be excellent:

```text
S degree          = 0
Y+R               <= 82-d
R                 <= 21-d
seed+Y+R          <= 2703-d
X+131071Y+131070R < 10824780-131069d.
```

But the first counterexample shows that full contact does not follow from the
current hypotheses.

## What would actually reopen the route

One of the following genuinely new inputs is required:

1. prove that the **actual intersection** of all Full187 node kernels is
   stable under top-`S` extraction;
2. strengthen the source construction to choose `Q` with the relevant
   `Y`-derivative correction terms also in the contact kernel; or
3. build a node-independent covariant derivative that commutes with every
   local substitution.

The obvious covariant correction is node-dependent: at node `x` it contains
`(X-x)^2/2 * d/dY`.  Different nodes give different operators, so it does not
produce one fixed global carrier.  No current theorem supplies any of the
three reopeners.

## Kernel-checked receipt

The file

```text
.experiments/Full187TopCurvatureCarrierStop6900.lean
```

proves the local substitution identity, the derivative identity, exact
truncation zero/nonzero statements, all three Full187 cap checks, and the
`49344*d` root-budget identity.  It builds without `sorry`, `decide`, or
`native_decide` under the normal 3.5 GB cap:

```text
env LEAN_NUM_THREADS=1 lake env lean -j1 -M3500 \
  .experiments/Full187TopCurvatureCarrierStop6900.lean
```

The printed axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound` (the arithmetic identities need only `propext` and `Quot.sound`).

## Decision

Do not splice the raw top-curvature coefficient into `HigherInitial` or the
accepted 6810 factor geometry.  The fixed-carrier shape exists, but its
universal selected-root premise is unproved and false under the proposed
local commutation argument.  Continue only if a simultaneous-kernel
invariance theorem or a differently constructed source is found.
