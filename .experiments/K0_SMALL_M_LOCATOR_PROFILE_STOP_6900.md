# K0 small-m all-node locator: exhaustive target STOP

Date: 2026-09-15 UTC. Scope: lower score 6900, exact target constants only.
This is a route-selection receipt, not a candidate or submission change.

## Question

The faithful `m=8` control has an explicit four-row separator built from the
all-node Hermite locator `Omega^(m-3)`.  Could we retune the target source to
a similarly small `m`, keep positive source capacity, and thereby replace the
open global four-row theorem with the same explicit construction?

For all four boundary axes, the worst carrier uses one active coordinate of
weight `w=131071`.  The literal construction therefore needs

```text
(m-3)*n + w < m*g,
n = 262144, g = 180413.
```

This holds only through `m=8`; at `m=8` it has just 1,513 degrees of slack,
and at `m=9` it is already 80,218 degrees too large.

## Exhaustive result

`k0_small_m_locator_profile_scan_6900.cpp` enumerates every tuple admitted by
the same exact k=0 shape constraints used by
`k0_rank4_source_search_6900.cpp`, for every `2 <= m <= 47`:

```text
1 <= s <= floor(m/2)
2s <= B <= m
max(m+s,B) <= U <= ceil(m*g/w)
```

For each tuple it computes the exact affine-in-`L` source margin, chooses the
first positive `L` when one exists, and applies the existing cap-slack and
ordinary-projection gates.  The enumeration covers 67,383 tuples.

```text
capacity-positive tuples                 592
first capacity-positive multiplicity     m=38
first hit                                (m,B,s,U,L)=(38,16,8,52,8596)
first-hit source margin                  2,631,120
capacity + four-axis locator overlap     0
```

Thus the regimes are disjoint by a factor of almost five in multiplicity:
the explicit locator fits only at `m<=8`, while source capacity starts only
at `m=38`.  The small finite determinant remains a valid semantic detector,
but no retuning inside this k=0 family makes its literal witness target-legal.

The scan deliberately excludes `s=0`: a source with no `S` coordinate cannot
realize the required four-coordinate `(Y,R,S,Z)` boundary readout, so it
cannot rescue the four-axis construction.

## Reproduction and integrity

```bash
g++ -O2 -std=c++17 \
  .experiments/k0_small_m_locator_profile_scan_6900.cpp \
  -o /tmp/k0_small_m_locator_profile_scan_6900
/tmp/k0_small_m_locator_profile_scan_6900
```

The run takes well under one second and uses only integer arithmetic.

```text
source SHA-256   21631c4348f689801aee7566c77e6c51b94a8607cf2fc6f94f92d485862c85ed
binary SHA-256   29e44c7a102ca5554ba6e83347cf595d0eb489eeda0c0b0fe9bfd9a1d407753e
output SHA-256   d948727dedfc3c3dd8f5313e602e1ad9dbaeb3722501f7a607c42211dc66e8eb
```

## Process consequence

Stop spending cycles on literal all-node-locator retuning.  The target proof
must exploit coupled active shapes: either a rank-three carrier plus one new
syndrome, a boundary-restricted recurrence/confluence theorem, or another
construction that pays less than uniform depth at all 262,144 old nodes.

