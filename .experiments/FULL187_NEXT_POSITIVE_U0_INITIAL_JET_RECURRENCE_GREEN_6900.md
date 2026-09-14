# Full187 next positive-u0 block: second initial-jet GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This quotients the
GREEN active-77 block in commits `a2363b8` and `0feaaa1`; it does not modify
production or a submission.

## Verdict

The lexicographically earliest outgoing component is exactly

```text
(outer Z, active degree) = (2625,76),
```

and the whole component is **GREEN** under the same corrected initial-Hasse-
jet strategy. Its raw contact module has 165 coordinates, 112 row types, and
rank 79. A legal prefix-closed 79-coordinate basis spans all 165 coordinates.
The deterministic minor is

```text
rank 79, determinant 55/64 = 299630593 mod 2130706433.
```

At all `N=262144` nodes this gives rank `79N=20709376`. All induced higher
jets lie outside their source SCC and strictly raise contact weight.

This is a second consecutive exact block, and it reveals a plausible uniform
initial-jet recurrence. It is not yet the parameterized theorem needed to
close every outgoing term.

## 1. Why this is the next component

The solved active-77 sections have source order

```text
(outer Z, J-active)=(2625,5).
```

For a non-full contact choose `f<y`, frozen-`U` exponent `h`, and remaining
`u0` exponent `y-f-h`. Lexicographic order first minimizes outer `Z=2625+h`,
so `h=0`. It then minimizes `J-(f+r+s)`, so `f=y-1`. The remaining `u0`
power is exactly one, and active degree drops from 77 to 76. No occurrence
enumeration is needed for this derivation.

The 44 preceding physical sections have 154 coefficient-jet blocks at this
first outgoing contact, comprising 495 raw occurrences. Their row union is
the complete 112-row component. The frozen outgoing-block hash is

```text
9ecf401bc7b4d8458212a976cfcb487b9a552f1c99968c02e603d5a320a2fc7f.
```

## 2. Complete coordinate and provenance census

At active degree 76, the derivative cap forces `y>=55`. The whole raw census
is

```text
y=55: 11 shapes * 5 Hasse orders = 55 coordinates
y=56: 11 shapes * 4 Hasse orders = 44 coordinates
y=57: 11 shapes * 3 Hasse orders = 33 coordinates
y=58: 11 shapes * 2 Hasse orders = 22 coordinates
y=59: 11 shapes * 1 Hasse order  = 11 coordinates
                                             total 165.
```

Their 506 nonzero contact entries occupy 112 target rows. The exact modular
rank is 79, hence the ambient row-type cokernel is 33. The row-universe hash
is

```text
8ffd28f8ec2c692175e2b1ba2605d1cd5cf820ac299af3e5369b0da3a087c306.
```

The script also inverts the original terminal/C/P expansion on all 112 rows:

```text
1595 origins = 1089 P + 506 C,
451 physical origin groups,
every origin has u0 power two.
```

Grouping by complete provenance, every physical group equals its full raw
contact column times `binom(k,f) binom(k-f,h)`. Thus all original same-key
data—not only the outgoing 44-section tail—lies in the 165-coordinate raw
module. Frozen hashes:

```text
1595 origins  a9fc846aabafff443247e5a58485783c218c49f99fc546300ccfdf3f5c52e317
451 groups    9cb7365c3de2d0fffea7d5490f5e0ee447deafb24975750db97b31e73900a9b6.
```

## 3. Legal prefix-closed basis

The selected 79 coordinates are:

```text
H0 on all y=55,...,59 and s=0,...,10:                 55
H1 on all y=55,56 and s=0,...,10:                     22
H1 on the curvature-cap neighbour (y,r,s)=(57,9,10):  1
H2 on the bottom cap (y,r,s)=(55,11,10):               1
                                                        --
                                                        79.
```

Every physical Hasse set is initial. Across 55 physical polynomials the
histogram is

```text
{0}     : 32,
{0,1}   : 22,
{0,1,2} :  1.
```

The unique three-jet section is the tight case:

```text
(y,r,s)=(55,11,10),
width=863415,
3N=786432,
slack=76983.
```

The minimum two-jet and one-jet slacks are 339116 and 601257. Ordinary
all-node confluent Hermite interpolation therefore realizes every selected
initial jet. There is no antiderivative and no omitted lower-Hasse feedback.

Exact rank checks give

```text
rank(selected 79) = rank(selected 79 + all 165 raw coordinates) = 79.
```

Consequently the row cokernel 33 cannot obstruct either the incoming tail or
any higher same-diagonal jet induced by these sections.

## 4. SCC and determinant certificate

The graph contains every selected raw contact entry and every unprescribed
higher jet of its physical polynomial. Its SCC histogram is

```text
32 singleton SCCs,
21 two-node SCCs,
 1 five-node SCC.
```

The exact determinant histogram is

```text
32 * 1,
18 * (-1),
 2 * (1/2),
 1 * 1,
 1 * (55/16) for the five-node cap SCC.
```

Their product is `55/64`. The unique five-node SCC uses controls

```text
(y,r,s,q)=
(56,11,9,0), (57,9,10,0), (55,12,9,1),
(56,10,10,1), (55,11,10,2),
```

and matched rows

```text
(56,0,67,9), (57,0,66,10), (58,0,65,11),
(59,0,64,12), (56,1,65,10).
```

Its determinant is `55/16`, a unit in the target field. This is the new
curvature-cap block which was absent at active 77.

There are 258 induced-higher-jet incidences. None lies within an SCC, and all
strictly increase contact weight. Hence arbitrary actual higher-jet operators
are off-diagonal in the SCC condensation and cannot alter the determinant.

## 5. Is the pattern uniform?

It is exactly uniform in outer `Z` wherever the source grade is legal. The
raw contact coefficients do not depend on `Z`; `Z` is merely carried as a row
label. The coefficient width simplifies at fixed active degree `A` to

```text
width(y,A-y-s,s) = D - (w-1)A - y + s,
```

which is also independent of outer `Z`. Therefore the active-77 56-by-56
matrix, its SCCs, determinant `1/4`, and section windows repeat unchanged for
every legal outer carrier. The same is true of the active-76 79-by-79 block.

Across active degrees, two consecutive exact cases now exhibit one mechanism:

```text
active 77: 32 {0}, 12 {0,1};                    det 1/4
active 76: 32 {0}, 22 {0,1}, 1 {0,1,2};        det 55/64.
```

The new bottom contact layer is promoted to the next complete Hermite depth,
and the curvature-cap neighbours supply the boundary coordinates needed for
rank. This is strong evidence for a prefix-closed Popov staircase, but two
cases do not prove its formula for every lower active degree.

## 6. Smallest theorem that would close the outgoing tails

The needed result is a single parameterized **initial-jet Popov lemma**, not
an enumeration of 177 million terms.

For each legal state `(z,A)` define `V_A` to be the truncated contact module
spanned by

```text
H_q(P) contactY^y R^r S^s Z^z,
y+r+s=A, r+s<=21, s<=10, y+q<60.
```

It is enough to prove that there is a prefix-closed coordinate set `B_A`
such that:

1. for every physical polynomial, its selected set is
   `{H0,...,H_qmax}` and `(qmax+1)N <= width(y,r,s)`;
2. the contact matrix on `B_A` is an isomorphism onto `V_A`, with unit SCC
   determinants over `F_2130706433`;
3. every unselected higher jet reduces to a strictly later component of the
   SCC condensation;
4. every non-full contact output advances
   `(outer Z, J-active)` lexicographically.

The complete-origin grouping in this and the active-77 gate then places every
physical RHS in `V_A`. Well-founded induction on the displayed lexicographic
order solves each same-filtration Popov block once and routes all other terms
forward. That theorem would close the large outgoing occurrence multisets
symbolically; their cardinalities would no longer matter.

The remaining mathematical work is to give `B_A` and its unit determinants
uniformly for every active degree reached by the four packets. Testing active
75 would be evidence, not a substitute for that theorem.

## 7. Outgoing scope

The 55 new physical sections have exactly 506 same-filtration occurrences,
whose row union is the complete 112-row block above. Every other output
strictly advances the common order:

```text
strictly later u0-free occurrences          6,003,679
strictly later positive-u0 occurrences    212,560,172.
```

This receipt does not expand or close those 218,563,851 occurrences, prove
the parameterized Popov lemma, connect `F0..F3`, or create a 6900 candidate.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=3221225472 --cpu=600 -- \
  python3 -B \
  .experiments/full187_next_positive_u0_initial_jet_recurrence_gate_6900.py
```

Recorded run: exit zero in about 1.4 seconds, peak RSS about 22 MiB.

```text
canonical sha256  434e54f34b667f0ede061aeae72f174fa5d504e25c02d8b899df06e4bbc93198
script sha256     08cedb9b214d3bb5cf4b055178582732ebc21a26dbeb5e607b0b72fc32139804
```
