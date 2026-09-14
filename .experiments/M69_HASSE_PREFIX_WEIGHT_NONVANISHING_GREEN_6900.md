# m69 direct-prefix Hasse weights: GREEN

Date: 2026-09-14 UTC.  This is a lower-6900 experiment only; production and
the accepted 6806 submission are unchanged.

## Outcome

The direct m69 cyclic-prefix model survives a previously unchecked algebraic
gate.  Every coefficient basis vector in every physical predecessor fringe
has a nonzero Hasse weight over the literal benchmark field.  Thus each
claimed residual interval is an exact prefix image, not merely a dimension
upper bound with hidden zero columns.

This repairs one mechanical premise of the reciprocal-monomial interval
GREEN.  It does **not** prove arbitrary-rational rank or simultaneous reuse of
the same source freedom across different missing coefficients.

## Exact identity

Put `Omega=X^N-1`.  A variation after preserving `depth` complete nodal jets
has the form

```text
Omega^depth * X^j.
```

At an N-th root, after multiplying by the harmless monomial normalization,
its order-`q` Hasse weight is

```text
[z^q] (((1+z)^N-1)^depth * (1+z)^j).
```

Since `N=262144` is nonzero modulo `p=2130706433`, divide by `N^depth` and
write `k=q-depth`.  The normalized weight is the degree-`k` polynomial in
`j`

```text
[z^k] A(z)^depth * (1+z)^j,
A(z)=((1+z)^N-1)/(N*z).
```

The executable constructs this polynomial exactly over `F_p`, factors it
with FLINT, and enumerates all of its field roots.  It checks the superset

```text
1 <= depth <= 47,   depth <= q <= 68
```

containing 2,115 `(depth,q)` pairs.  Across those polynomials FLINT finds
3,046 distinct field-root entries, but none is represented by an integer
`0 <= j < 262144`.  All roots are simple.  The complete polynomial/root
receipt hash is

```text
f2726daf754df8a0d32c1a739922f8c76ce77cb51548af5511b7f5c14f80df0e
```

## Physical reconnection

The exact m69 defect census has 140,153 deliberately rank-insensitive
deficient physical coefficients.  Expanding every available direct
higher-contact predecessor gives 7,918,984 physical channels and 2,010
distinct `(depth,q)` pairs.  For every channel the executable independently
checks

```text
1 <= depth <= q <= 68,
0 < fringe < N,
binom(source_y,target_y) != 0 mod p.
```

The physical stream hash is

```text
a431bc3e9c9d99f9e40b717e746a422313ff5e8694ae7cfba3972ed6a974a828
```

Consequently the Hasse operation is a nonzero diagonal rescaling of every
coefficient prefix used by the cyclic interval model.

## Process audit

The first implementation accumulated all 7.9 million records and attempted
to format one giant tuple for hashing.  It hit the deliberate 2 GiB address-
space cap after the algebraic root gate had passed.  The corrected version
streams each record into SHA-256 and peaks at only 54,884 KiB.  No cap was
raised, and no mathematical conclusion depends on the failed formatting run.

Recorded bounded run:

```text
prlimit --as=2147483648 --cpu=300 -- \
  python3 -B \
  .experiments/m69_hasse_prefix_weight_nonvanishing_gate_6900.py

exit 0
peak RSS       54,884 KiB
canonical SHA  6c5ae3427e6194ee244ff9da41eebc81098fcec05da31c5489f7b4e37c96b750
script SHA     ec5a2c3db24985f6822f88f4918adc393e4bdcae785264de3446fbd7c0f7762c
```

## Route decision

Do not revisit coefficient-weight nonvanishing unless the m69 profile or
field changes.  The remaining hard gates are genuinely structural:

1. containment of the actual W-positive residual in the joint rational
   prefix image, especially `129450 <= deg N0 <= 149776`;
2. simultaneous multi-stratum allocation/confluence;
3. the separate content-root/Live adapter and lower-passive tails.

