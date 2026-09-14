# m69 physical-wedge source attachment: exact RED gate

Date: 2026-09-14 UTC. Scope: the literal `OriginalPassiveSeedSource6900`
interface and the DataEleven `(0,0,26)` top-diagonal chain. No endpoint or
submission file is changed.

## Corrected verdict

Neither of the two proposed shortcuts attaches the physical wedge

```text
d(X) U0 - c(X) U1
```

to the source theorem currently available at the leaf:

1. Directly replacing a received row by an X-dependent polynomial row shear
   does not preserve the constant-seed affine pencil, candidate degree cap, or
   strict weighted source box.
2. Combining the original mixed channels with binomial weights is a valid
   algebraic identity in isolation, but the actual top passive grade supplies
   only the last channel `g=h`. It does not supply the full mixed family.

The second point corrects an earlier draft that incorrectly treated `q=26`
as a passive-seed cap and used 94 in the seed accounting. Here `q=26` is an
X-Hasse/order parameter. The actual passive seed cap is 2369.

## Exact top-grade obstruction

Fix output row `y` and source contact `k=y+h`. A mixed term with exponent `g`
of the original second row starts at input passive seed `z` and lands at
output passive seed `z+g`.

At the top passive output grade, alignment and source legality are

```text
z + g = seedCap - y,
z + (y+h) <= seedCap,
g <= h.
```

Adding `y` to the first equality and comparing with the second inequality
forces `h <= g`. Hence `g=h`. If `h>0`, already the `g=0` term required by the
binomial expansion is absent.

For the literal chain:

```text
seedCap = 2369
row 41 top output seed = 2369-41 = 2328
row 42 top output seed = 2369-42 = 2327
input seed at contact k = 2369-k
```

On row 41, `h=k-41`, so the surviving term has `g=h` and

```text
(2369-k) + (k-41) = 2328.
```

On row 42 the analogous identity is

```text
(2369-k) + (k-42) = 2327.
```

This applies throughout the top diagonal, including contact 68. Contact 68
does not fail because a hypothetical `g=27` has a negative seed index; rather,
`g=27` is exactly the sole legal top-grade channel for row 41. The failure is
that all the other channels are missing.

The only retained binomial summand is

```text
(-c U1)^h (d U0)^0 choose(h,h) = (-c U1)^h.
```

It is not `(d U0-c U1)^h` in general. Thus the source's literal top-diagonal
variable remains the original `U1`, not the DataEleven physical wedge.

There is also a useful quantitative repair condition. If the desired output
is lowered by passive slack `ell`, the same comparison gives

```text
h <= g + ell.
```

Therefore recovering even the first channel `g=0`, and hence any full mixed
family, requires at least `ell>=h` passive grades of slack. Any viable
off-top reconstruction must explicitly pay that loss and reconnect the
resulting lower passive grade to the terminal consumer.

`M69CovariantWedgeSourceCombination6900.lean` formalizes all of these claims,
the hypothetical binomial identity, and the independent polynomial-degree
cost `h*max(deg c,deg d)`. It compiles without `sorry`, `decide`,
`native_decide`, or nonstandard axioms.

## Why direct polynomial GL2 transport is also unavailable

`OriginalPassiveSeedSource6900.lean` consumes

```text
errorE |-> contactY + U0 + U1*seed.
```

After specializing the passive seed to a field scalar `gamma`, its exact
naturality theorem still uses the affine graph `U0+gamma*U1`. An
X-dependent row matrix `[[a,b],[d,-c]]` changes this to

```text
(a+gamma*d) U0 + (b-gamma*c) U1.
```

That is not a node-independent Mobius reparametrization of `gamma` unless the
matrix is projectively constant. Coprimality of `c,d` can make the matrix
unimodular, but does not make it projectively constant.

The smallest model is already decisive:

```text
M(X) = [[1,0],[X,-1]],  det M = -1.
```

It sends the pencil to `(1+gamma X)U0-gamma U1`, whose direction varies with
the node X. The formal affine-pencils theorem says that a replacement
intercept/direction agreeing at two distinct seed values must equal the
original pair.

The same operation also fails the exact source filtration. With
`D=69*180413` and `w=131071`, the monomial

```text
Q = X^(D-w-1) Y
```

has weighted degree `D-1` and lies in the source box. The degree-one scaling
`Y -> X*Y` sends it to `X^(D-w)Y`, of weighted degree exactly `D`, outside the
strict box. A polynomial wedge representative also has honest degree bound
`w+s`, sharp even for `s=1`, so it leaves the degree-`w` selected-candidate
class.

`M69PolynomialRowShearSourceBoxCountergate6900.lean` formalizes the affine
pencil rigidity, the literal MvPolynomial substitution, both weighted-box
membership decisions at the m69 constants, the sharp candidate-degree cost,
unimodularity of the small model, and the two-support intersection arithmetic.

## Consequence and next honest route

The conditional proposition

```text
LiteralC00Chain0026SourceEquation (normalizedW E0 N0) ...
```

is still not derived from `OriginalPassiveSeedSource6900` and the actual leaf.
The high-wrap Padé/rank problem is downstream of this missing attachment, not
the first live blocker.

A repair must now prove one of the following genuinely new interfaces:

1. rebuild the consumer at a lower passive output grade and pay at least `h`
   seed slack plus the coefficient degree cost;
2. construct a source whose received variable is the physical wedge from the
   outset and re-establish its selected-graph hypotheses and dimension count;
3. prove an additional leaf identity making the original `U1` itself the
   required physical direction; or
4. bypass this DataEleven chain with a terminal consumer attached directly to
   the literal source variable.

Even after such an interface, the separate extraction of `cross.C00` into the
contact-94/order-26 terminal polynomial remains missing, as recorded by commit
`5f3f931`.

## Reproduction

```bash
env LEAN_PATH=.experiments LEAN_NUM_THREADS=1 \
  lake env lean -j1 -M8000 \
  .experiments/M69CovariantWedgeSourceCombination6900.lean

env LEAN_PATH=.experiments LEAN_NUM_THREADS=1 \
  lake env lean -j1 -M8000 \
  .experiments/M69PolynomialRowShearSourceBoxCountergate6900.lean
```
