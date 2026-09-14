# k=0 target-ratio raw `{1,R,S}` layer survivor

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G`, after the high-`Y`
transport STOP in `d251e34`. This changes no production file, score,
candidate, or submission.

## Verdict

The strongest finite structure which survives the target-ratio controls is
not the all-anchor packet or the high-`Y` seed pair. It is the literal raw
derivative filtration

```text
{1}  ->  {1,R}  ->  {1,R,S}  ->  {1,R,S,R^2}.
```

In both deterministic constant-`T`, equal-mismatch controls:

```text
raw {1}                 contact-injective, boundary gain 0
raw {1,R}               boundary gain 3
raw {1,R,R^2}           boundary gain 3
raw {1,R,S}             boundary gain 4
full {1,R,S,R^2}        boundary gain 4
```

More sharply, the unique compatible boundary covector after raw `{1,R}` is
literally

```text
(0,0,1,0) in coordinates (Y,R,S,Z).
```

Adding `R^2` leaves that same pure-`S` line. Adding raw `S` kills it. Yet raw
`{1,S}` and `{1,S,R^2}` are contact-injective and give no boundary normal at
all. Thus `S` is not an independent fourth witness: `R` first creates the
contact kernel and the `Y/R/Z` normal hyperplane, and an `R-S` coupled
relation then supplies the curvature direction.

This pattern survives both m5 and m6 target-ratio profiles and agrees with
the earlier two-error `{1,R,S}` discriminator. It is a substantially better
theorem target than transporting the m4 high-`Y` circuit.

## 1. Exact ranks

The script

```text
.experiments/k0_target_ratio_raw_1rs_layer_gate_6900.py
```

builds the complete literal raw contact matrix once per profile and takes
exact submatrices for seven prescribed derivative-shape families. It uses no
randomness and no parameter grid.

For the exact-ratio profile

```text
(n,w,g,m,B,s,U,L)=(11,5,8,5,2,1,8,8),
```

the results are:

| raw family | columns | contact rank | kernel | boundary gain | compatible dual |
|---|---:|---:|---:|---:|---|
| `{1}` | 1200 | 1200 | 0 | 0 | all four dimensions |
| `{1,S}` | 2112 | 2112 | 0 | 0 | all four dimensions |
| `{1,S,R^2}` | 2728 | 2728 | 0 | 0 | all four dimensions |
| `{1,R}` | 2076 | 2038 | 38 | 3 | `span{S*}` |
| `{1,R,R^2}` | 2692 | 2601 | 91 | 3 | `span{S*}` |
| `{1,R,S}` | 2988 | 2916 | 72 | 4 | zero |
| full | 3604 | 3418 | 186 | 4 | zero |

For the ceiling profile

```text
(n,w,g,m,B,s,U,L)=(11,5,8,6,2,1,8,8),
```

the results are:

| raw family | columns | contact rank | kernel | boundary gain | compatible dual |
|---|---:|---:|---:|---:|---|
| `{1}` | 1560 | 1560 | 0 | 0 | all four dimensions |
| `{1,S}` | 2760 | 2760 | 0 | 0 | all four dimensions |
| `{1,S,R^2}` | 3600 | 3600 | 0 | 0 | all four dimensions |
| `{1,R}` | 2724 | 2713 | 11 | 3 | `span{S*}` |
| `{1,R,R^2}` | 3564 | 3508 | 56 | 3 | `span{S*}` |
| `{1,R,S}` | 3924 | 3895 | 29 | 4 | zero |
| full | 4764 | 4635 | 129 | 4 | zero |

The compatible dual is computed as the exact left nullspace of the boundary
image of the complete contact kernel, not inferred from separate coordinate
gains.

Receipt:

```text
canonical SHA-256  2a662660ba79af708f21821fd021d24887b94bbbe59eb99ff31b409fd6923d90
script SHA-256     2eeb3a80c86d0ad3c59903c1dd2a386c13b290b26fc2174dad90b5605c8211cc
runtime            258.7 s, 1.37 GiB peak RSS, 7 GiB process cap
```

## 2. Structural statement that survives

The repeated finite statement is the following two-stage factorization of
the conormal problem:

```text
SLOPE-STAGE:
  ker(contact on raw {1,R}) maps onto the boundary hyperplane S=0.

CURVATURE-STAGE:
  after raw S is admitted, one additional contact-kernel class has nonzero
  S boundary coordinate.
```

`R^2` affects neither semantic stage: it enlarges the contact kernel but does
not change its boundary image. Conversely, `S` without `R` does not create a
kernel in these controls. The fourth direction is therefore a mixed
curvature connecting class, not a direct raw-`S` column and not a scalar
`T''` trace.

This is compatible with the already formal
`ThreeShapeLocalConnector6900.connectorMatrix_det` identity: locally, the
three raw channels have a triangular connector with nonzero equal diagonal.
The new exact ranks identify the global order in which those channels become
effective. The outstanding issue remains the global tapered-X/seed/contact
recurrence, not the local `3 x 3` determinant.

The generic Lean interface in `K0LineThenKill6900.lean` now has exactly the
right specialization:

```text
lambda0 = S-coordinate covector,
packet   = raw {1,R} subspace,
killer   = an R-S coupled relative contact repair.
```

Unlike the earlier all-anchor packet, this packet-line description is stable
in both target-ratio controls.

## 3. Target scaling scope

This does not prove that raw `{1,R,S}` alone is a target source. The smallest
nested target envelope containing these shapes is `(B,s)=(2,1)`, and its
published m47 source ledger is far red:

```text
columns                          8,801,286,669,304
one-node contact-rank bound             34,984,662
all-node margin                    -369,732,566,024.
```

The full `(B,s,U)=(16,8,64)` source is the only green nested envelope under
the current rank theorem. Therefore the safe target claim is:

```text
the low raw {1,R,S} channels are the observed semantic normal mechanism;
the higher raw layers are still required as capacity/kernel scaffolding.
```

A proof must derive the two stages from the complete green source, or prove
a sharper rank theorem for a non-nested source. It cannot simply discard the
higher layers.

## 4. Exact remaining universal hypotheses

The next symbolic target is now narrower than arbitrary full-source DUAL0:

```text
1. Prove, for arbitrary exact-G bad data, that every boundary covector
   compatible with the complete contact equations on the legal raw {1,R}
   projection is a multiple of S*.

2. Construct from the complete legal source an R-S coupled relative repair
   whose complete contact trace is already in the {1,R} contact image and
   whose boundary difference has nonzero S coordinate.

3. Show that the full-source dimension kernel can be reduced to those low
   semantic channels without losing the tapered X and passive-seed windows.
```

The finite controls give exact evidence for all three-channel geometry but
do not prove any of these target-uniform statements. In particular, local
triangularity alone does not establish the global relative repair.

