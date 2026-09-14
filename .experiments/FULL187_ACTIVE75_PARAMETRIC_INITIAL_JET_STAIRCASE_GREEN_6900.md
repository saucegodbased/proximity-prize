# Full187 active-75 GREEN and the parametric initial-jet staircase

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This is an exact
discriminator for the whole `(outer Z,active)=(2625,75)` diagonal and a
theorem-shaped invariant extracted from the three consecutive GREEN blocks
at active degrees 77, 76, and 75. It is not a Full187 closure theorem,
candidate, score, or submission.

## Decision

The third discriminator is **GREEN**. The complete active-75 raw contact
module has rank 103, and a closed, non-greedy staircase `B_75` selects exactly
103 source-legal initial Hasse jets which span it. After choosing an
independent target-row basis, the exact `103 x 103` determinant is

```text
-1/512  mod 2130706433 = 4161536.
```

Its dependency graph has only invertible equal-weight SCCs. All 534 edges
from unprescribed higher coefficient jets leave their SCC and strictly raise
contact weight. Every nonfull contact output strictly advances the same
lexicographic `(outer Z,J-active)` filtration used in the active-77 and
active-76 receipts.

More importantly, the three bases are instances of one formula. For an
admissible physical shape

```text
y+r+s=A,  r+s<=21,  0<=s<=10,  0<=y<60,
```

put `d=60-y` and

```text
qmax(y,s) = max(0, floor((d-1)/3), floor((d+s-11)/2)).
B_A(y,r,s) = {q : 0 <= q <= qmax(y,s)}.
```

Equivalently, `q=0` is always retained, and a positive `q` is retained iff

```text
d >= 3q+1,
```

or it lies in the curvature boundary

```text
2q < d <= 3q  and  s >= 11-(d-2q).
```

This formula exactly reproduces every selected coordinate at active 77 and
76 and gives the active-75 basis without a rank-guided choice. The arithmetic
part is global: all `11,154` admissible physical shapes for `0<=A<=77` have
literal coefficient capacity for their prescribed prefix. The algebraic
span statement `span(B_A)=V_A` is proved by exact matrices only at
`A=75,76,77`; its symbolic Pascal straightening proof remains the main gap.

## Frozen authorities

The script refuses to run if any of its three authority scripts differ from
these bytes:

```text
full187_cross_slope_second_fringe_confluence_6900.py
  2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29
full187_earliest_positive_u0_curvature_frontier_gate_6900.py
  cd763ffc825c0a9e1d73f055d1278b583fdcdac162a5ed597e289e24d4db53b0
full187_next_positive_u0_initial_jet_recurrence_gate_6900.py
  08cedb9b214d3bb5cf4b055178582732ebc21a26dbeb5e607b0b72fc32139804
```

The first two GREEN diagonal receipts are commits `0feaaa1` and `6791b40`.

## Three consecutive blocks and the closed formula

The exact reproduction table is:

| active `A` | raw coordinates | target rows | raw rank | `B_A` size/rank | physical initial-jet prefixes |
|---:|---:|---:|---:|---:|---|
| 77 | 110 | 73 | 56 | 56/56 | 32 `{0}`, 12 `{0,1}` |
| 76 | 165 | 112 | 79 | 79/79 | 32 `{0}`, 22 `{0,1}`, 1 `{0,1,2}` |
| 75 | 231 | 154 | 103 | 103/103 | 32 `{0}`, 31 `{0,1}`, 3 `{0,1,2}` |

Thus the repeated `32` singleton count and the enlarging two-/three-jet
boundary are not annotations retrofitted to greedy bases. They are the exact
Ferrers boundary of `qmax(y,s)`.

The active-75 coordinate-level histogram, where the contact filtration level
of a source coordinate is `y+q`, is

```text
54:11, 55:22, 56:24, 57:23, 58:12, 59:11.
```

The formula is initial-prefix closed on every physical polynomial. There are
66 physical polynomials and 103 prescribed coefficient jets. The tight
active-75 section is

```text
(y,r,s,z)=(54,12,9,2625), q={0,1,2},
width=994485, needed=3*262144=786432, slack=208053.
```

## Global literal-capacity arithmetic

The script enumerates only integer shape/width inequalities—not contact
matrices—for every possible positive-`u0` active degree `0<=A<=77`. It checks:

1. `0<=qmax<60-y` for every admissible physical shape;
2. each prescribed set is exactly the initial prefix `0..qmax`;
3. `(qmax+1)*262144 <= width(y,r,s)`;
4. under the descending transfer `(y,r,s)->(y-1,r,s)`, `qmax` grows by zero
   or one, never more.

The global minimum among all 11,154 shape checks is still positive:

```text
A=22, (y,r,s,z)=(1,11,10,2625), q=0..29,
width=7941249, needed=30*262144=7864320, slack=76929.
```

So literal all-node Hermite capacity is no longer an uncertainty for this
candidate staircase anywhere in the fixed outer-Z band. This does **not**
prove that its contact images span at lower active degrees.

## Complete active-75 provenance

The whole block, not selected rows, was enumerated:

```text
231 raw coordinates,
154 distinct target row types,
880 nonzero raw coordinate-row entries,
raw rank 103, ambient row cokernel 51.
```

Every same-key origin from the original top `C/P` source was recovered:

```text
2629 original origins = 880 C + 1749 P,
583 complete grouped raw columns,
every origin has u0 power exactly 3.
```

For every group, the literal source scalars aggregate to

```text
binom(k,f) * binom(k-f,h) * raw_contact_column(f,r,s,q,2625).
```

No origin was sampled or reconstructed from a representative. Stable hashes
of the 2,629 signatures and 583 grouped identities are respectively

```text
89f1da8aa8be0591f65682b9c0bd1ed9358b5b3fc998b14051b3c5f0441b8f88
8f990f496fba7d71030a196f48a8622fa06b3aa39af84fc1c669b5c099b8c019
```

The first outgoing tail from all 55 preceding active-76 physical sections is
also complete. Taking exactly `h=0,f=y-1` produces

```text
220 raw blocks, 869 row occurrences, union = all 154 target rows.
```

Its stable receipt hash is

```text
bf0dd355786c628703e5bfc7db10231c7089d17dc7e1b472db867244a697aff6.
```

This proves that the tested diagonal is the actual earliest lower-contact
interface of the preceding sections, not an unrelated rank model.

## Exact minor and dependency SCCs

There is one important process correction. A support-perfect matching from
the 103 selected columns directly into all 154 rows exists, but the resulting
minor is singular:

```text
rank 42, determinant 0.
```

This is not a rank defect. Support matching certifies only structural rank
and can choose a coefficient-singular row set. The corrected deterministic
procedure first scans the full `154 x 103` matrix for 103 independent rows,
then matches the columns inside that row basis. It yields rank 103 and
determinant `-1/512`. The independent-row and matched-minor hashes are

```text
row basis: a081213f5962ef725969557ecb024dcbb48d1af07a829698f1a7972f07617197
matching:  95516c0a1bd9789d0b85d375dd793473f87849569e9302d93020a297f7615286
```

The exact SCC-size histogram is

```text
32 singleton SCCs, 31 size-2 SCCs, one size-3 SCC, one size-6 SCC.
```

Their determinant histogram is

```text
32 * (1),
20 * (-1),
 9 * (1),
 2 * (-1/2),
 1 * (1/8)   [size 3],
 1 * (-1/16) [size 6].
```

The product is exactly `-1/512`. The two larger collision blocks are:

```text
size 6, determinant -1/16, source keys
  (54,12,9,2), (55,11,9,1), (55,10,10,2),
  (56,10,9,0), (56,9,10,1), (57,8,10,0)

size 3, determinant 1/8, source keys
  (54,11,10,2), (55,10,10,1), (56,9,10,0)
```

All keys have `z=2625`. These blocks show explicitly that curvature-cap
feedback at `s=9,10` is load-bearing. It is handled inside unit SCCs rather
than discarded as a higher-order effect.

The component-key hash is

```text
029bf517d20ad27b260552760aef580fc6bba4390dae9b15de6f63f5f7b3b0ec.
```

All 534 dependencies induced by the unprescribed higher jets go to a
different SCC and strictly increase row contact weight `i+3a`. Ordinary
selected-column dependencies never decrease it. Thus equal-weight SCC
solves plus increasing contact weight give the required well-founded local
order.

The raw 154-row cokernel 51 is harmless for this interface: `B_75` has the
same rank 103 as all 231 raw coordinates, and the complete incoming tail lies
in that raw module. After tensoring the scalar minor across all nodes, the
actual block has rank `103*262144=27000832` and cokernel zero in its intended
raw target module.

## Outgoing order and size

For the 66 physical section polynomials, the exact occurrence census is

```text
same-filtration full contact       880
strictly later, u0-free        7203724
strictly later, positive-u0  251470241
```

The same-filtration rows equal the complete 154-row universe. Every nonfull
contact has either

```text
(z, J-(f+r+s)) > (z, J-A)
```

or, for the positive-`u0` mate,

```text
(z+y-f, J-(f+r+s)) > (z, J-A).
```

These counts are recorded only to audit orientation. The script never
materializes the 258-million-occurrence outgoing tail.

## Candidate induction theorem

Let `V_A` be the span of all raw contact columns at fixed `(z,A)=(2625,A)`.
The exact next theorem should be:

> For every `0<=A<=77`, the initial-jet staircase `B_A` spans `V_A`.
> With rows ordered by contact weight, every equal-weight diagonal block is
> a unit Pascal/curvature minor, all higher coefficient jets move to greater
> contact weight, and every nonfull contact moves to greater
> `(outer Z,J-active)`.

The descending recurrence is unusually small. A physical channel transfers
as

```text
(y,r,s) at A  ->  (y-1,r,s) at A-1,
```

so `d` increases by one and

```text
qmax(y-1,s)-qmax(y,s) in {0,1}.
```

All target channels with `y<=58` have such a predecessor. The only channels
without one are the top `y=59` boundary channels, and the formula assigns
them only `q=0`; these are the separate boundary seeds. This is the smallest
recurrence suggested by all three exact blocks: transfer each existing
prefix, add at most one new jet, and seed only top-boundary values.

The proof should use the literal contact polynomial

```text
T = E + X*R - (1/2)*X^2*S,
raw(y,r,s,q) = X^q R^r S^s T^y
```

in the weight-`<60` truncation. After factorial normalization, the collision
matrices are Pascal/finite-difference matrices. The `3q` interior boundary
and `2q` curvature boundary in `qmax` should arise as the standard-monomial
frontier for this three-term expansion. That symbolic straightening identity,
including truncated `r+s=21` and `s=10` boundaries, is the missing algebraic
proof—not another large enumeration.

Exact arithmetic hypotheses needed by that proof are:

1. `2` is invertible, for the curvature coefficient `-1/2`;
2. the characteristic is greater than 60, so the factorials and ordinary
   Pascal pivots through degree 59 are units;
3. every equal-weight determinant reduces symbolically to such unit Pascal
   factors (this reduction remains to prove globally);
4. `(qmax+1)N<=width`, already checked for every Full187 shape;
5. `A<=77`, so the fixed outer-Z band retains positive `u0` and the descent
   is oriented by the declared lexicographic order.

The current prime `2130706433` meets the explicit field conditions, and the
three computed determinants are `1/4`, `55/64`, and `-1/512`.

## Relation to the robust three physical groups

The exact small-chamber connector receipt found that nonmatched-error packets
can require all three first-shell groups `{(0,0),(1,0),(0,1)}`. The present
raw contact expansion has exactly the corresponding three terms

```text
E, X*R, -(1/2)*X^2*S.
```

Thus the same central/slope/curvature trichotomy is literally responsible
for these diagonal collisions, and the active-75 size-3/size-6 SCCs verify
that the `S` branch cannot simply be ignored. This is a structural alignment,
not a connecting-map theorem: this receipt neither identifies the F101
quotient with `V_A` nor proves that `B_A` maps onto the four `F0..F3` packets.

## Rejected shortcuts and remaining uncertainty

- The earlier isolated-`q` antiderivative model was invalid because an
  antiderivative does not force omitted lower Hasse jets to vanish. `B_A`
  prescribes literal initial prefixes and retains every induced higher jet.
- A perfect support matching is not a coefficient certificate. At active 75
  its naive minor has rank 42. Independent target rows must be chosen before
  matching.
- Three consecutive GREEN matrices and global capacity do not prove
  `span(B_A)=V_A` for all `A`. The symbolic straightening/minor identity is
  still load-bearing.
- Passive-band transport and the eventual `F0..F3` connecting map are outside
  this gate.

## Replay

```text
python3 .experiments/full187_active75_parametric_initial_jet_staircase_gate_6900.py
```

Frozen receipt at note time:

```text
script SHA256    db1725a1bb483e60f0b5e649aaa801d2090a2c14591a92e76b8c4a34e909035a
canonical SHA256 4ad2e329e4aeb879534e1adfdd1f8fc7cedd98f77b13d3a683fb29f63dde1cf0
peak RSS         about 25 MiB
runtime          about 2 seconds
```

The script and note make no production or submission changes.
