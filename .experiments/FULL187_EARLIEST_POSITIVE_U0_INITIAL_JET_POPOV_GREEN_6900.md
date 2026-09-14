# Full187 earliest positive-u0 frontier: initial-jet Popov GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This follows the
whole-first-later-Z receipt `b86d33b`; it does not change production or a
submission.

## Verdict

The complete earliest error-facing diagonal exported by the band-1 sections
in `b86d33b` is **GREEN**, after repairing a load-bearing section error in the
first attempt.

The exact diagonal is

```text
(outer Z, active degree) = (2625,77).
```

It contains 110 physical full-contact coefficient coordinates and 73 target
row types. A legal 56-coordinate initial-jet basis spans the entire raw
56-dimensional diagonal module. Its deterministic square minor has

```text
rank = 56,       determinant = 1/4 mod 2130706433.
```

After expansion at all `N=262144` nodes, the block has rank `56N=14680064`.
Every higher coefficient jet induced by the chosen Hermite sections lands in
a later SCC, so the determinant is nonzero for the actual higher-jet
operators, not merely when they are set to zero.

This closes only this one same-filtration block. The 44 physical sections
emit more than 177 million later occurrences, which remain open.

## 1. Exact frontier and all physical provenance

The initially visible frontier consists of seven rows of contact weights
57, 58, and 59. They have, respectively,

```text
11, 11, 20, 11, 11, 20, 30
```

same-key original-source origins: 114 in total, every one with `u0` power
one. Their combined frozen provenance hash is

```text
bd9c614a026237f64f068df644ec471e9121d6d6eb7cd084985d57834ca98b97.
```

The executable does not stop at those seven rows. At active degree 77 the
source derivative cap `r+s<=21` forces `y>=56`; contact truncation forces
`y<=59`. It enumerates every

```text
y=56,...,59,
s=0,...,10,
r=77-y-s,
q=0,...,59-y.
```

These are 110 raw coordinates. Expanding every `contactY^y` gives exactly 73
distinct rows. Independently inverting the original terminal/C/P expansion
on every row finds

```text
880 origins = 616 P origins + 264 C origins,
330 distinct physical origin blocks,
all with u0 power one.
```

For every one of the 880 origins, the tuple
`(contact_f,r,s,coefficient_q,2625)` is one of the 110 enumerated raw
coordinates. Thus arbitrary aggregation of all original same-key origins is
already inside the raw module spanned below; this conclusion does not depend
on a sampled coefficient or on a hoped-for Pascal cancellation.

The 73-row and 880-origin hashes are

```text
rows     79abd3e7ccb5e7c7426688fd65ef09e612f29541e9912ba0b27e6fd835788c3b
origins  a4ec451ac2a3996f0fad96b9bf23a3e330ed4f04c0abbdbe693b68575824f7fa.
```

Thus the SCC below is the whole earliest same-key frontier, not a sample of
named rows.

## 2. The rejected antiderivative section

The first attempt selected a raw 45-column basis with eleven isolated `q=1`
coordinates on `y=56` and one extra isolated `q=2` coordinate. It proposed:

```text
construct H_q(P), then take a q-fold coefficientwise Hasse antiderivative
with all lower jets zero.
```

That sentence is false. A coefficientwise antiderivative has only its usual
integration constants; it does not make `H_0(P),...,H_{q-1}(P)` vanish at
262144 nodes. The omitted lower jets enter the same diagonal, including all
eleven individually non-strong-capacity `y=56,q=0` heads. Therefore the old
45-by-45 GREEN was withdrawn before commit.

The process lesson is strict: never select a noninitial Hasse set unless a
literal section proves every lower jet, or the dependency graph includes it.

## 3. Legal initial-jet repair

The repaired basis includes `q=0` wherever it uses `q=1`, and replaces the
extra `q=2` direction at `(y,r,s)=(56,11,10)` by the equally rank-raising
`q=1` direction at `(57,10,10)`. Its 44 physical polynomials are:

```text
11 sections  (y,r,s)=(56,21-s,s), s=0,...,10, prescribing {H0,H1};
 1 section   (y,r,s)=(57,10,10),                 prescribing {H0,H1};
10 sections  (y,r,s)=(57,20-s,s), s=0,...,9,   prescribing {H0};
11 sections  y=58, r=19-s, s=0,...,10,          prescribing {H0};
11 sections  y=59, r=18-s, s=0,...,10,          prescribing {H0}.
```

So the Hasse-set histogram is

```text
{0}   : 32 physical polynomials,
{0,1} : 12 physical polynomials.
```

Ordinary confluent interpolation realizes an arbitrary initial `k`-jet at
all nodes in degree less than `kN`. Every literal coefficient width is larger
than the required window. The smallest two-jet case is

```text
(y,r,s)=(56,21,0): width=732334,
2N=524288, slack=208046.
```

The smallest one-jet slack is `470187`. No mixed-CRT extrapolation and no
lower-jet-zero assertion is used.

The physical curvature staircase `s=0,...,10` is explicit. In particular,
the `s=9` contact-curvature output and the `s=10` physical group are both in
the matrix. This is the Full187 counterpart to retaining the `+S` group in
the robust F101 small chambers; the calculation does **not** assume that the
F101 connecting map or its coefficients transfer.

## 4. Exact rank, SCCs, and higher jets

The selected 73-by-56 raw matrix has rank 56. A deterministic support
matching selects a 56-by-56 minor with determinant

```text
1/4 = 1598029825 mod 2130706433.
```

The dependency graph contains the exact selected-column support and every
unprescribed higher jet of each physical section. Its SCCs are

```text
32 singleton SCCs, determinant 1;
10 two-node SCCs, determinant -1;
 2 two-node SCCs, determinant -1/2.
```

For `s=0,...,9`, the repeated two-node matrix is

```text
[[56,57],
 [ 1, 1]],                 determinant -1.
```

At the curvature cap, adjacent contact/curvature slopes give the two
determinants `-1/2`. Their product with the ten `-1` determinants is `1/4`.

There are 109 retained induced-higher-jet dependency incidences. None is
inside an SCC, and every one strictly raises contact weight. Therefore the
SCC condensation is triangular for the actual induced operators. The
expanded diagonal determinants are scalar determinants tensored with
`I_N`; arbitrary off-diagonal higher-jet operators cannot change them.

## 5. Why the ambient cokernel 17 is harmless here

The complete 73-row raw diagonal has rank 56, hence ambient row-type
cokernel 17. The selected 56 columns span all 110 physical raw coordinates:

```text
rank(selected) = rank(selected + all 110 coordinates) = 56.
```

Thus every same-diagonal higher jet emitted by the 44 selected physical
polynomials—and every aggregate of the 880 original same-key origins—is also
in the selected image. Checking the 56 matched rows is enough; the other 17
row values are recovered by the exact raw-module relations.

There is also an independently useful smaller receipt. The 99 individually
strong-capacity coordinates occupy 47 rows and have rank 45. Their two exact
row relations are

```text
row(56,1,66,10) + 2 row(58,0,66,11) = 0,
-14 row(56,1,66,10) + 399 row(57,0,67,10)
  + row(59,0,65,12) = 0.
```

The actual post-Pascal frontier has 10 safe zero blocks, six safe nonzero
blocks, and three unsafe blocks which cancel identically. All six arbitrary
variations made by the preceding `b86d33b` sections also have safe sinks.
Consequently the actual RHS is in the safe rank-45 module and both displayed
dual evaluations are exactly zero. Since the selected rank-56 image contains
the entire safe module, the ambient cokernel 17 imposes no new condition on
this actual tail.

## 6. Common order and exact outgoing scope

Within `(outer Z,active)=(2625,77)`, the finite SCCs above are solved in the
condensation order. For every non-full-contact output, retain the common
well-founded order

```text
(outer passive Z, J-active degree), lexicographically.
```

If frozen-`U` exponent is positive, outer `Z` increases. If it is zero,
active degree decreases, so the second coordinate increases. Exhaustive
expansion of all 44 physical sections gives

```text
same-filtration full-contact occurrences             264
same-filtration distinct rows                          73
strictly later u0-free occurrences              4,803,260
strictly later positive-u0 occurrences        172,449,684.
```

The 73 same-filtration rows equal the complete row universe above. Every
omitted occurrence strictly advances the displayed common order.

## 7. Scope guard and next interface

This is a genuine local Popov section for the first positive-u0 diagonal. It
does not prove a passive-band induction, close the 177,252,944 outgoing
occurrences, connect the four exact packets, prove F3 containment, or create
a 6900 candidate.

The next admissible use is to quotient this solved 56-dimensional diagonal
and inspect the earliest outgoing filtration component. Reusing the rejected
isolated-q antiderivative model would regress the proof.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=3221225472 --cpu=600 -- \
  python3 -B \
  .experiments/full187_earliest_positive_u0_curvature_frontier_gate_6900.py
```

Recorded run: exit zero in about one second, peak RSS about 20 MiB.

```text
canonical sha256  227cf49e760bd5d9bbcd3c49f479fce8a43c56b8be191c238948913e9aada0c0
script sha256     9111bd64484b3238a3c78fb7d880a4fcaf033f594e3ca2d169f64bae6714962c
```
