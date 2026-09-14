# m69 literal Pascal two-row chain: four-high denominator-only GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 m69 source research only. Production,
score, radius, candidate, and submission roots are unchanged.

## Decision

For the literal m69 chain

```text
(r,s,q)=(0,0,26),  Y={41,42},  terminal T=94,
```

the four high-prefix contacts

```text
k=41,43,45,47
```

already span the complete two-row cyclic output whenever

```text
W=1/E,
2151 <= deg E <= 18414,
gcd(E,X^262144-1)=1.
```

This includes the minimal nondividing example `E=X^2151-2`. No divisor
block decomposition, random rank heuristic, or fixed-lambda recurrence is
used. The proof instead uses the correct literal Pascal adjoint and two
finite differences.

## Literal source-facing duals

After multiplying output row `y` by the unit `E^(94-y)`, contact `k` acts by

```text
binom(k,y) E^(94-k) P_k.
```

Let `lambda_41,lambda_42` be an annihilator of the complete two-row source.
The axiom-clean prefix-dual theorem in
`M69FixedShapePascalAdjointCountergate6900.lean` gives one short polynomial
for each contact. For the same-parity contacts `k=41+2j`, divide by the
nonzero scalar `binom(k,41)`. The exact ratio is

```text
binom(41+2j,42) / binom(41+2j,41) = j/21.
```

Thus the four normalized encodings are

```text
E^(53-2j) * (lambda_41 + (j/21) lambda_42) = x G_j,
j=0,1,2,3.
```

Their physical prefix complements are

```text
deg G_0 < 3302,
deg G_1 < 3300,
deg G_2 < 3298,
deg G_3 < 3296.
```

## Correct recurrence: a Pascal second difference

Multiplying the `j`th equality by `E^(2j)` makes the left side affine in
`j`. Two consecutive second differences vanish at every NTT node:

```text
E^4 G_2 - 2 E^2 G_1 + G_0 = 0,
E^4 G_3 - 2 E^2 G_2 + G_1 = 0.
```

These are honest polynomial identities, because throughout the full allowed
denominator interval their maximum degrees are

```text
4*18414 + 3297 = 76953 < 262144,
4*18414 + 3295 = 76951 < 262144.
```

This is the correct two-output replacement for the invalid first-order
fixed-lambda recurrence. The extra output covector disappears only after a
second difference, exactly as the Pascal transpose predicts.

## Divisibility kills both output covectors

Rearranging the identities gives

```text
G_0 = E^2 (2 G_1 - E^2 G_2),
G_1 = E^2 (2 G_2 - E^2 G_3).
```

Hence `E^2` divides both `G_0` and `G_1`. But

```text
deg(E^2) >= 2*2151 = 4302,
deg G_0 < 3302,
deg G_1 < 3300.
```

Therefore `G_0=G_1=0`. Root-freeness of `E` in the first two nodal
encodings then gives

```text
lambda_41=lambda_42=0.
```

Every source annihilator is zero, so finite-dimensional duality makes the
four-contact source map onto the entire two-row output. Terminal containment
is an immediate consequence.

## Minimal nondividing exact witness

Take

```text
E=X^2151-2.
```

Since `gcd(2151,262144)=1`, exponentiation by 2151 permutes the NTT subgroup.
The denominator is root-free because

```text
2^262144 mod 2130706433 = 2042248820 != 1.
```

This proves the minimal nondividing case without constructing the enormous
`524288`-row matrix. It also shows that the earlier `4096 | 262144` block
decomposition was a convenient oracle, not the reason for full rank.

## Formal and executable artifacts

`M69LiteralPascalFourHighDenominatorOne6900.lean` proves:

1. the scalar Pascal second-difference identity;
2. the short-polynomial `E^2` divisibility kill;
3. vanishing of both output duals from the first two encodings;
4. the exact no-wrap arithmetic.

It compiles under

```text
LEAN_NUM_THREADS=1 lake env lean -j1 -M3500
```

and prints only

```text
[propext, Classical.choice, Quot.sound].
```

It contains no `sorry`, `admit`, `decide`, `native_decide`, unsafe
declaration, or generated table.

`m69_literal_pascal_four_high_denominator_one_gate_6900.py` independently
reconstructs the exact deficient chain, all four caps, Pascal ratios, degree
inequalities, and the root-free nondividing witness. Its canonical receipt is

```text
09c3caf4db26615cf6177d93077a132c63cca3596501ca81163aedfabdfed775
```

and peak RSS was about `38 MiB`.

## Scope and next gate

This closes the genuine simultaneous source problem for the two-row chain in
the denominator-only branch. It does not yet handle a nonconstant numerator.

For `W=N0/E`, the same alignment gives the weighted identity

```text
E^4 G_2 - 2 N0^2 E^2 G_1 + N0^4 G_0 = 0
```

up to orientation/normalization. The next exact task is to derive that
identity from the literal adjoint, compute its no-wrap region, and use
`gcd(E,N0)=1` plus the numerator root split. That is the only honest extension
of this breakthrough; returning to the fixed-lambda Padé recurrence would be
an adapter regression.
