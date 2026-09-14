# m47 reduced-curvature profile gate for lower 6900

Date: 2026-09-14 UTC. Scope: exact-`G`, k=0 lower 6900. This is an exact
source/consumer arithmetic receipt, not a conormal-rank theorem or candidate.

## Result

The working profile

```text
(m,B,s,U,L,k,n0) = (47,16,8,64,3757,0,1)
```

is not the shallowest target-green profile with the same terminal strip.
Keeping `(m,B,U)=(47,16,64)`, lowering the curvature cap by two layers, and
buying passive-seed width gives

```text
(m,B,s,U,L,k,n0) = (47,16,6,64,5107,0,1).
```

The literal source formulas evaluate to

```text
source columns                  84,240,729,954,206
one-node local-rank bound              321,352,836
262144 * local-rank bound       84,240,717,840,384
source margin                           12,113,822
```

The terminal/error locator check is unchanged because it depends on
`(m,B,U)`, not `s` or `L`:

```text
47*180413 - 131071*(16+47+1) = 90,867 > 81,731 errors.
```

The exact-cardinality consumer remains comfortably green:

```text
one-stratum 52-chart cost        2,098,345,279,488
81,732 strata total            171,501,956,383,113,216
MCA allowance                  254,684,620,614,660,120
remaining slack                 83,182,664,231,546,904
```

Both active and inactive projection bounds remain below characteristic.
These equalities and inequalities compile axiom-clean (only the standard
`propext`, `Classical.choice`, and `Quot.sound`) in
`SecondJetK0ReducedCurvatureArithmetic6900.lean`.

## Why this matters

The global recurrence is the current proof bottleneck. The alternative
profile removes raw curvature layers `S^7,S^8` and increases the source
margin by roughly five times. Its extra `Z` window is potentially helpful for
the translated passive-seed recurrence. Therefore future symbolic work should
be parameterized in `(s,L)` and tested against both profiles rather than
silently hard-coding `s=8,L=3757`.

This is not yet a reason to discard the original profile. The rank-four
mechanism still has to be checked in faithful reduced-curvature controls, and
the proof may only use the low `{1,R,S}` semantic layer anyway. If the first
raw transpose recurrence is independent of the top two curvature layers, the
new profile is strictly simpler at no protocol cost. If it needs those layers,
the old profile remains available.

## Search boundary

At fixed `(m,B,U)=(47,16,64)`, exact affine-in-`L` evaluation gives the first
positive passive-seed caps:

| curvature cap `s` | first positive `L` | source margin | consumer status |
|---:|---:|---:|---|
| 5 | 1,035,343 | 16,055 | far beyond allowance |
| 6 | 5,107 | 12,113,822 | green |
| 7 | 3,788 | 479,478 | green |
| 8 | 3,757 | 2,371,080 | green |

For `s<=4` the signed source margin has negative `L` slope, so increasing the
passive-seed cap cannot rescue those envelopes under the published local-rank
bound. Thus `s=6` is the shallowest member of this fixed terminal family that
passes both current source and consumer gates.

