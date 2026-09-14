# Canonical m6 three-shape witness and locator-factor STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

The exact arbitrary-error `m=6` control has a coefficientwise lift of all
four boundary packets through the first-shell `{pure,R,S}` block, but the
lift is highly nonunique and dense. A visually attractive full-domain
locator factor in the canonical `S` coefficients is **not invariant under
the shell kernel**. It is an RREF basis artifact and must not be promoted to
a symbolic recurrence.

This closes one specific reverse-engineering path. The finite rank result
still supports the three-block span, but it supplies no sparse canonical
formula.

## Frozen control

The script reuses the exact `F_101` arbitrary-error chamber

```text
(n,w,g,m,D,q,t,J,L)=(10,4,7,6,42,1,1,8,12),
agreement nodes 0,...,6,
error nodes     7,8,9,
error offsets   (3,5,7),
Q               = Xi_E^2.
```

Modulo the complete grade-at-most-eight prefix, the three grade-nine shape
groups have 642 columns. The exact solve receipt is

```text
contact-quotient rows       972
shell columns               642
shell rank                  610
shell nullity                32
four packet targets contained yes
```

The executable computes one deterministic solution by setting all 32 free
variables to zero and independently constructs and verifies all 32 RREF
kernel basis vectors.

## Density receipt

The canonical representatives use 596, 599, 598, and 597 of the 642 shell
coefficients for `F0,F1,F2,F3`. Their nonzero counts by `(r,s)` group are:

| packet | pure `(0,0)` | curvature `(0,1)` | slope `(1,0)` |
|---|---:|---:|---:|
| F0 | 233 | 168 | 195 |
| F1 | 233 | 168 | 198 |
| F2 | 233 | 168 | 197 |
| F3 | 231 | 168 | 198 |

The pure and slope groups have polynomial gcd one in every packet. The six
nonzero curvature layers have common gcd equal to the degree-ten full-domain
locator in `F0,F1,F2`; in `F3` the gcd has degree eleven and contains that
locator. Every individual canonical curvature layer is divisible by the
full-domain locator.

That pattern is not forced. Only four of the 32 checked kernel basis vectors
retain full-domain-locator divisibility in every curvature layer; the other
28 violate it. Adding any such direction to a packet solution produces an
equally valid lift without the apparent common factor. Therefore neither
the gcd nor the RREF representative defines an intrinsic connector.

## Consequence

```text
STOP  infer a locator/CRT formula from the canonical dense coefficients
STOP  call the shell lift unique
GO    retain only the exact three-block containment evidence
GO    seek a target-window transpose or a basis-independent syzygy theorem
```

This negative result is especially important because a single canonical
solve can look much more structured than the affine solution space really
is. Future witness mining must first quotient by or sample the homogeneous
kernel before treating a factor pattern as mathematical evidence.

## Reproduction

```text
prlimit --as=3221225472 -- \
  python3 .experiments/f101_m6_offset_three_shape_connector_witness_6900.py
```

Recorded capped run:

```text
elapsed seconds          73.326880
peak RSS KiB             603280
canonical JSON SHA-256   81e7c011fae43103736ff00bf05fa1d6f46494df3ca5cfb2d457c09cbb304bb6
script SHA-256           2ab336141e2d4b77a2f54366d7c8a1663eee0983e2ec7ce41f437a35d3d7198c
```

The calculation uses no `decide`, `native_decide`, production module, or
submission artifact.
