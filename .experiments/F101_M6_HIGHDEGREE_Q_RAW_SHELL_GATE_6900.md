# m6 maximal-degree arbitrary-error raw-shell gate

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

**GREEN, with a unique minimal three-shape connector in this control.**  In
the target-scaled `m=6`, `J=8` chamber, with a maximal-degree agreement
polynomial and independent values at every error, the first raw shell closes
the exact coefficientwise `F0,F1,F2,F3` packet if and only if all three
available derivative-shape groups are present:

```text
{(r,s)=(0,0), (1,0), (0,1)}.
```

Every proper subset leaves every packet individually at defect one and the
four packets jointly at defect four.  This exactly reproduces the earlier
`Xi_E^2` arbitrary-error answer while removing its extra degree headroom.

This is the strongest finite evidence so far for a raw `Y/R/S` first-shell
connector.  It is not a uniform confluence theorem and does not establish
`ProtocolClaim6900`.

## 1. Frozen maximal-degree retained-bad direction

The predeclared chamber is

```text
F_101
(n,w,g,m,D,q,t,J,L) = (10,4,7,6,42,1,1,8,12)
G = {0,...,6}, E = {7,8,9}, H = {0,...,4}.
```

Put

```text
q_H = 1+X,
Q   = q_H + Lambda_H (1+X).
```

Then

```text
deg Q = deg(Q-q_H) = 6 = g-1 > w=4.
```

Interpolation on the five anchors recovers exactly `q_H=1+X`.  The five
anchor equalities force any hypothetical degree-at-most-`w` match to equal
`q_H`, while `Q-q_H` is nonzero on the remaining agreements, so this is
genuinely retained-bad.

The actual `U1` values agree with `Q` on `G`.  Only at the three errors, add
the fixed offsets `(3,5,7)`, producing actual values `(72,96,20)`.  Every
actual `U1` value is nonzero.  Thus no single polynomial `Q` describes all
nodes, and the computation tests arbitrary-error robustness rather than a
matched-error specialization.

The exact four normals have source support sizes

```text
F0,F1,F2,F3 = 68,99,129,67
```

and error-contact support sizes `72,72,81,70`.  They are all source-legal and
their literal contacts vanish at every agreement.

## 2. Exact coefficientwise connector table

Modulo the complete legal centered-grade-at-most-`J=8` prefix:

```text
prefix columns / rank                 3582 / 3582
each packet individual defect                  1
joint packet quotient rank                      4
```

The first post-prefix shell has total grade nine.  Its three raw legal shape
groups have 234, 200, and 208 columns respectively.  The complete exact table
over `F_101` is:

| raw shell shapes | columns | shell quotient rank | individual defects F0..F3 | joint defect |
|---|---:|---:|---:|---:|
| `{00}` | 234 | 234 | `(1,1,1,1)` | 4 |
| `{10}` | 200 | 200 | `(1,1,1,1)` | 4 |
| `{01}` | 208 | 208 | `(1,1,1,1)` | 4 |
| `{00,10}` | 434 | 434 | `(1,1,1,1)` | 4 |
| `{00,01}` | 442 | 442 | `(1,1,1,1)` | 4 |
| `{10,01}` | 408 | 408 | `(1,1,1,1)` | 4 |
| `{00,10,01}` | 642 | 610 | `(0,0,0,0)` | 0 |

There is no fraction-field localization in this calculation.  Each source
coefficient window is retained literally, and the targets are the exact
four polynomial boundary columns coupled to the complete all-node contact
map.  The full legal `L=12` source is also green: 6,150 columns, rank 5,812,
and joint packet defect zero.

## 3. Safe-face and source-legality audit

Applying the same strong affine-error safe criterion with margin `n-g=3`
classifies all available shapes as safe:

```text
safe   (0,0),(1,0),(0,1)
unsafe none.
```

Thus the conservative terminal deletion is explicitly checked but vacuous in
this three-shape chamber.  All raw shell columns in the table are legal by
construction.

For this small chamber, even the three compact centered expressions happen
to be source-legal:

```text
(Y-QZ)^6 Z^3,
R (Y-QZ)^6 Z^2,
S (Y-QZ)^6 Z^2.
```

That convenience must not be extrapolated to the target for arbitrary
`deg Q=g-1`: the `R` and `S` centered expansions can exceed the target's
weighted X windows.  The reusable positive observation is about the complete
raw shape groups and their coupled cancellations, not three universally
legal compact formulas.

## 4. Relationship to the under-scaled tight control

The separate nonzero-node chamber

```text
(n,w,g,m,D,q,t,J,L)=(18,8,14,6,84,4,1,5,5)
```

is useful as a falsifier for a same-cap safe-terminal theorem, but its
`J=5<m=6`.  It cannot contain the full centered multiplicity-six head.  In
that chamber the same raw three-shape transplant improves the exact packet
defects from `(1,1,1,1)` to `(0,1,1,1)` but remains red.  This is not a
target-scaled counterexample to the connector, because the target has
`J-m=22` rather than `J<m`.

Restoring the one deleted unsafe terminal shape in that under-scaled chamber
is completely inert: all 49 restored columns increase contact rank by 49 and
leave the complete-contact nullity and every packet defect unchanged.

## 5. Honest target consequence

The result survives the two degeneracies that invalidated earlier optimism:

```text
Q has maximal permitted agreement degree g-1;
error U1 values are independent offsets from Q.
```

Together with the existing `m=6,7,8` arbitrary-error controls, it supports
one narrow next conjecture: the first raw shell's complete `Y/R/S` groups
jointly span the four packet residues, with no growth beyond `r,s<=1` yet
observed.  A proof still has to retain source windows and derive the coupled
three-block cancellation uniformly in `m`, `q`, `t`, and field size.  No
formal target theorem should be claimed from the finite ranks alone.

## 6. Reproduction

```text
prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/f101_m6_highdegree_q_raw_shell_gate_6900.py
```

Recorded run:

```text
elapsed        236.390276 seconds
peak RSS       603,304 KiB
canonical SHA  9716f627ef28c096501a73beb08162dca757948f3f5fc116c8ce3f0b2353f647
script SHA     72d62c921aced2cc461592dc9b516f723325ea661aedbabb8160698bd2eaff99
```

The executable uses no `decide`, `native_decide`, production module, or
submission artifact.
