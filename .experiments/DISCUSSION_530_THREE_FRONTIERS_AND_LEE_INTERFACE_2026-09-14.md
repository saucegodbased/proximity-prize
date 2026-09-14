### Lower 6900: three exact frontier layers, a uniform staircase formula, and the existing CompPoly completeness bridge

Status first: the live verified benchmark is **68.10**, while accepted
production in this research checkout remains 68.06. There is still no 69.00
candidate, build, comparator run, or submission. The results below reduce the
Full187 construction gap; they do not yet close it.

#### 1. The first three positive-u0/error-facing layers are exact GREEN

The whole first later-Z section from the preceding update exported its first
positive-u0 block at `(outer Z, active)=(2625,77)`. Commits `a2363b8` and
`0feaaa1` enumerate the complete same-key block, not selected rows:

```text
110 raw contact coordinates -> 73 rows
880 original same-key origins in 330 complete physical groups
legal section: 44 physical polynomials / 56 initial Hasse jets
selected rank: 56; selected image spans all 110 raw coordinates
expanded all-node rank: 56*N = 14,680,064
```

Every physical group is checked coefficientwise to equal its full raw contact
column times the common Pascal scalar. Twelve polynomials prescribe the honest
initial jet set `{H0,H1}` and 32 prescribe `{H0}`; no isolated higher jet is
silently set while omitting its predecessors. All 109 induced higher-jet
incidences leave their SCC and strictly increase contact weight. Every
non-full-contact export advances the common well-founded order
`(outer Z, J-active)`.

Commit `6791b40` quotients that block and closes the complete next layer
`(2625,76)`:

```text
165 coordinates -> 112 rows, raw rank 79
1,595 original origins in 451 complete groups
55 physical polynomials / 79 initial jets
q-set histogram: 32*{0}, 22*{0,1}, 1*{0,1,2}
selected image spans all 165 coordinates
expanded rank: 79*N = 20,709,376
```

Commit `79637e2` closes `(2625,75)` independently:

```text
231 coordinates -> 154 rows, raw rank 103
2,629 original origins in 583 complete groups
66 physical polynomials / 103 initial jets
q-set histogram: 32*{0}, 31*{0,1}, 3*{0,1,2}
selected image spans all 231 coordinates
```

All three computations retain every incoming physical occurrence and every
outgoing term. The active-75 gate also caught a process trap: arbitrary
support matching can select a singular minor even when the map has full rank;
the certified construction first selects independent rows, then matches.

Most importantly, the three layers expose one closed candidate staircase.
For a physical shape with `d=60-y`, take the initial prefix `q=0..qmax`, where

```text
qmax = max(0, floor((d-1)/3), floor((d+s-11)/2)).
```

Equivalently, positive `q` is admitted iff `d>=3q+1`, or
`2q<d<=3q` and `s>=11-(d-2q)`. This formula reproduces the exact bases at
active 77, 76, and 75. A global integer audit over all 11,154 admissible
physical shapes at active `0..77` proves every such initial-jet prefix fits
inside its literal Hermite coefficient window. The worst slack is still
76,929 coefficients. Under `A -> A-1, y -> y-1`, `qmax` grows by at most one.

This converts the 177M/218M outgoing occurrence ledgers into one plausible
well-founded induction. The honest missing theorem is now specific: prove
symbolically that this `B_A` staircase spans the whole raw same-grade module,
including the `r+s=21` and `s=10` boundaries, via Pascal/finite-difference
straightening and unit SCC minors. Matrix proofs currently establish that
span only for active 75, 76, and 77.

#### 2. The first genuinely coupled pure-face obstruction is GREEN

Commit `7edc5cc` corrects and completes the coupled `k=17,18` dual gate. The
literal normalized rows on the three legal lanes `(A2,A72,A29)` are

```text
(931238467, 1, 0)
( 95217577, 1, 1).
```

Residue pairing reduces the possible left dual to 41,999 coefficients. A
compact 4x2 PM-basis computation returns final shifts

```text
(95902,95903,95902,95902)
```

against threshold 81,730: the minimum misses by 14,172, so no nonzero dual
exists. An independent FLINT verifier checks every approximant product, the
exact shift/determinant sum 303,637, and leading determinant 1. Peak PM RSS was
about 0.91 GiB. Therefore the restricted three-lane primal is already
surjective onto these two coupled projections. This rules out the first
vector-dual obstruction as well as the earlier scalar ones; it is positive
evidence but not full membership of the fixed 60-row residue.

#### 3. Patched CompPoly already formalizes the exact pure-face module

Commit `7800a3b` corrects another process assumption. The bivariate pure face
does not need a new contact-completeness theorem. Let `Rcv` be the degree-`<N`
indicator which is zero on agreement roots and one on error roots. The graph
ideal is

```text
J=(X^N-1,Y-Rcv)=(E*Y,G*(Y-1)),
Rcv=G*(N^-1 X E').
```

With CompPoly parameters

```text
messageDegree=131072, multiplicity=60,
weightedDegreeBound=D-1=10824779,
```

the library computes `yWeight=131071`, `Y` cap 82, and width 83. Its proved
Lee--O'Sullivan basis is exactly

```text
Y^(i-t) (Y-Rcv)^t (X^N-1)^(60-t),
t=min(i,60), 0<=i<=82.
```

The field is exactly KoalaBear (`2130706433`), and CompPoly exposes a native
fast backend plus soundness/completeness and row-span-preserving shifted
reduction theorems. The local Lean interface probe compiles without
`native_decide` or new axioms.

The remaining caveat is important: the stock operation finds an arbitrary
least-degree nonzero interpolant, while this packet requires the fixed linear
coefficient `[Y]Q=H^59 Rloc^60`. Also, naively materializing the target 83-row
power basis is not memory-safe. We are investigating a fast PM-basis/affine
membership realization, not claiming the library call has decided the target.

#### Current critical path

1. Prove or falsify the uniform `B_A` Pascal/finite-difference span theorem.
2. Finish the running ratio-faithful pure+slope connector discriminator.
3. Extend the coupled residue test only where it adds information (next order
   or direct fixed-residue membership), under a strict memory gate.
4. Integrate the four packet boundaries and passive-band ownership, then move
   to Lean/build/verifier work.

The frontier is materially narrower and more formalized, but it is not yet
mechanical and confidence in a complete 69.00 submission is not yet high.

