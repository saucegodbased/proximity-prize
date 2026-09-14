# m69 literal Pascal chain: binomial-denominator block rank GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 m69 source research only. Production,
score, radius, candidate, and submission roots are unchanged.

## Outcome

The genuine simultaneous shared-tail map for the exact two-row m69 chain

```text
(r,s,q) = (0,0,26),  Y={41,42},  terminal T=94
```

has full output rank for the allowed rational function

```text
N0 = 1,
E  = X^4096-2,
W  = N0/E
```

over the benchmark field. This is stronger than terminal-column containment:
all `2*262144` output coordinates lie in the source image.

The computation uses the literal Pascal transpose/source map and the real
alternating caps. It does not use the now-RED fixed-lambda recurrence.

## Why this denominator is admissible

Its degree is inside the exact leaf interval:

```text
2151 <= 4096 <= 18414.
```

It is coprime to `X^262144-1`. If a common root existed, then

```text
x^4096 = 2,
x^262144 = (x^4096)^64 = 2^64 = 1.
```

But exact benchmark-field arithmetic gives

```text
2^64 mod 2130706433 = 402124772 != 1.
```

Thus `E` is nonzero on every NTT node, `W` is defined everywhere, and
`gcd(E,N0)=1`.

## Exact literal equations

After absorbing each already-audited nonzero source Hasse diagonal, let
`P_k` range over the physical prefix of size

```text
258842, 127771, 258844, 127773, ..., 258868, 127797
```

for contacts `k=41,...,68`. A terminal polynomial has physical exponents

```text
26 <= j < 127823
```

and hence dimension `127797`.

The two actual output equations are

```text
sum_k binom(k,y) W^(k-y) P_k
  = binom(94,y) W^(94-y) C,
y=41,42.
```

Multiplication by the unit `E^(94-y)` gives the equivalent polynomial
equations modulo `X^262144-1`

```text
sum_k binom(k,y) E^(94-k) P_k = binom(94,y) C,
y=41,42.
```

This is the matrix tested by the executable.

## Small exact block decomposition

Because `4096 | 262144`, put

```text
Z = X^4096,
X^262144-1 = Z^64-1.
```

Multiplication by `E=Z-2` preserves the exponent modulo `4096`. The full
map therefore splits into `4096` independent blocks, each with `128` output
rows. Prefix sizes in a fixed residue are exact truncations of the 64-term
`Z` basis. Across all residues there are only `31` distinct cap patterns.

For each pattern, the executable constructs every column of

```text
binom(k,y) (Z-2)^(94-k) Z^j mod (Z^64-1)
```

over `F_2130706433` and computes both source rank and source-plus-terminal
rank using FLINT. The residue-weighted result is

```text
source rank 128 of 128: 4096 residues
target containment defect 0: 4096 residues.
```

Full rank over the prime field remains full rank over the actual degree-six
benchmark extension.

The pattern-record receipt is

```text
8d3cc9b0b3b966b69b4e3cddfe25ee72492264481d5350f43f43e9a70f4f2fe0
```

and the canonical output receipt is

```text
390366b73a3cdfb5105d994f12d02f4c976d6077ed903bc6121fa3ddbd627148
```

Peak RSS was about `58 MiB`; runtime was about eight seconds.

## Verified preimage

For residue zero, the first literal terminal monomial is physical exponent
`4096` (block degree one). The script selects a deterministic 128-column
source minor, solves it exactly, multiplies the solution back by the minor,
and asserts equality to that terminal column.

The solution uses only contacts `41`, `42`, and `43`; it has `128` nonzero
field coefficients. Its exact sparse-support receipt is

```text
30531d9574d641f827b6e949fd49d7ea6b30e78432ee6cf3f62faaba65c304e7
```

This is a compact reproducible witness that the rank result is not an
augmented-matrix bookkeeping accident.

## Interpretation and scope guard

This result is a positive discriminator, not the arbitrary-rational theorem:

```text
GREEN: one literal chain, one admissible nonmonomial rational W;
OPEN:  the same chain for an arbitrary coprime root-free E,N0;
OPEN:  all 9900 chains simultaneously inside the actual leaf adapter.
```

It changes the strategic picture in one useful way. The monomial reciprocal
case was not GREEN merely because multiplication permuted coordinates: this
nonmonomial binomial denominator is also fully onto. The shared Pascal tails
have much more rank than the fixed-lambda Padé model exposed.

The block split does rely on `4096 | 262144`, so the next discriminator is a
nondividing denominator degree, preferably the minimal allowed `2151`. That
test determines whether the divisor decomposition is the essential reason
for full rank or just a convenient proof oracle.
