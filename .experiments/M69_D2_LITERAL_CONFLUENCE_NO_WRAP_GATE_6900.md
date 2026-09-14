# Literal m69 two-row confluence: proved no-wrap gate

## Scope

This checkpoint concerns only the first nontrivial chain
`(r,s,q) = (0,0,26)`, whose target contacts are `Y = {41,42}`.
It does **not** claim the full 6900 endpoint, a leaf-to-contact producer, or a
simultaneous section for all chains.

After harmless nonzero row and column rescaling, the literal Pascal block is
the value/first-Hasse-derivative block.  Its dual sequence has the nodal
second-order relation

```text
N^2 H_t - 2 N E H_(t+1) + E^2 H_(t+2) = 0.
```

When the three even-start relations at physical contacts `41,...,47` are
shorter than `X^262144-1`, they are genuine polynomial equalities.  Two
overlapping equalities force each intervening short even-prefix polynomial to
be divisible by both coprime `E` and `N`.  Its degree cap then forces it to be
zero; the equality between the two zeros kills the intervening odd-prefix
polynomial too.

`M69ConfluentD2NoWrapGate6900.lean` proves the abstract coprime divisibility,
degree-kill, and exact physical integer inequalities without `sorry`,
`decide`, `native_decide`, or nonstandard axioms.

## Exact covered parameter range

Write `e = deg E` and `n = deg N`.  Under the actual leaf bounds

```text
2151 <= e <= 18414,     n <= 149776,
```

the ordinary high-low-high gate covers exactly the sub-band

```text
3300 <= e+n <= 127771.
```

Equivalently, for each fixed `e`, it covers
`max(0,3300-e) <= n <= 127771-e`.  The lower exclusion exists only when
`e < 3300`; the upper cyclic-wrap exclusion begins at `n = 127772-e`.
This is a parameter-band statement, not yet a census of actual leaves.

The same Lean file now closes the complementary low-sum band
`e+n < 3300`.  It restricts to the all-high even contacts
`41,43,...,53`.  Their direct step-two recurrence has factors `E^2,N^2`;
all products have degree below 16,500, and overlapping relations force the
middle high polynomials to contain `E^2*N^2`, whose degree already exceeds
their caps.  A formal pointwise determinant then shows that vanishing modes at
offsets 4 and 6 kill both literal dual coefficients and hence the terminal
offset-53 mode (with `W=0` handled separately).

Thus the proved algebra and arithmetic cover every parameter with

```text
e+n <= 127771.
```

provided the required nodal relations and bounded polynomial representatives
are supplied by the still-missing leaf adapter.

## What was falsified

The full first-order `D_t = E H_(t+1)-N H_t` chain cannot simply be lifted
from nodal equality to polynomial equality over the whole stated band.  The
odd-start relations contain the long low-prefix polynomials and can wrap
modulo `X^262144-1`.  The proof deliberately uses only even-start
high-low-high triples, for which all three exact bounds are below the modulus.

## Remaining d=2 work

1. For `e+n >= 127772`, retain the quotient by `X^262144-1` and prove the
   needed cyclic Sylvester/resultant statement rather than pretending there is
   no wrap.
2. Derive these polynomial/nodal hypotheses from an actual m69 leaf and attach
   their vanishing conclusion to the terminal coefficient.  No current module
   provides that source/terminal provenance.

Only after those edges are formal is it sound to generalize from `d=2` to all
9,900 literal chains and then solve the shared four-component endpoint.
