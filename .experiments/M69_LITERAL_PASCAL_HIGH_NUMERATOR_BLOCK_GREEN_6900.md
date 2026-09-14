# Literal m69 two-row map: exact high-numerator GREEN instance

## Decision

**GREEN for one genuine high-numerator, cyclic-wrap instance.**

For the literal shared-tail chain

```text
(r,s,q) = (0,0,26),  Y = {41,42},  terminal T = 94,
```

take, over the benchmark field of order `2130706433`,

```text
Z  = X^4096,
E  = Z - 2                  (degree 4096),
N0 = Z^32 - 3              (degree 131072),
W  = N0/E.
```

The numerator degree lies in the unresolved high band
`130509..149776`, far beyond the ordinary no-wrap boundary.  Nevertheless,
the exact literal Pascal source spans the complete two-row terminal output.
Every block source matrix has rank `128/128`, and adjoining every permitted
terminal column increases rank by zero.

This falsifies the idea that cyclic wrap itself creates an obstruction for
the first two-row chain.  It does **not** prove arbitrary-rational
surjectivity.

## Admissibility receipts

The ambient cyclic modulus is `X^262144-1`, so `Z^64=1`.

* `E` is root-free: a common root would give `2^64=1`, whereas
  `2^64 mod p = 402124772`.
* `N0` is root-free: on `Z^64=1`, `Z^32` is `+1` or `-1`, hence never `3`.
* `gcd(E,N0)=1`: reducing `N0` at `Z=2` gives
  `2^32-3 = 33554427 mod p`, nonzero.
* The degrees obey the actual leaf ranges.

## Exact literal equations

For each output row `y=41,42`, clearing the denominator by
`E^(94-y)` gives

```text
sum_{k=41}^{68} binom(k,y) N0^(k-y) E^(94-k) P_k
    = binom(94,y) N0^(94-y) C.
```

The `P_k` have the real alternating physical caps

```text
258842,127771,258844,127773,...,258868,127797.
```

The target `C` has physical exponent interval `[26,127823)`, dimension
`127797`.  No fixed-lambda or geometric-sequence surrogate is used.

Because every coefficient is a polynomial in `Z`, residue modulo `4096` is
preserved.  The full cyclic map therefore decomposes into `4096` exact
systems with `128` output rows each.  There are only `31` distinct cap
patterns.  Python-FLINT computes source and augmented ranks over the exact
benchmark field; no probabilistic projection is involved.

## Reproduction

```bash
python3 .experiments/m69_literal_pascal_high_numerator_block_gate_6900.py
```

Observed receipt:

```text
source rank histogram:             {(128, 4096)}
target containment defect:         {(0, 4096)}
distinct residue-cap patterns:     31
peak RSS:                           59996 KiB
canonical SHA256:                  0c67eec9c437acf413d25fd5e57797f1d78ef2d988c608c7500c79d4d932bd4f
pattern-record SHA256:             8d3cc9b0b3b966b69b4e3cddfe25ee72492264481d5350f43f43e9a70f4f2fe0
```

## Consequence for the proof search

The low/no-wrap proof is genuinely useful but its failure above
`deg E + deg N0 = 127771` is a proof-boundary, not evidence for a hostile
leaf.  The correct high-band target is a cyclic/module version of confluent
Hermite interpolation.  Any proposed universal obstruction based only on
the quotient terms in the weighted second difference is RED: this instance
has enormous quotient terms and is still onto.

The structured block split is only an oracle device.  A universal theorem
still has to handle arbitrary coprime root-free `E,N0`, most of which do not
preserve a small monomial residue decomposition.
