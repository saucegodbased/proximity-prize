# k=0 m47 weighted-shape capacity frontier

Date: 2026-09-14 UTC. Scope: exact-G lower 6900 at the worst stratum
`g=180413`, with

```text
(m,U,L,D)=(47,64,3757,47g),
0 <= S <= sCap,       R+2S <= BCap,
0 <= BCap <= 16,      0 <= sCap <= min(8,floor(BCap/2)).
```

This is exact source/consumer arithmetic. It is not a conormal-rank theorem,
candidate, or submission change.

## Verdict

Among all **81 nested legal weighted-shape envelopes**, exactly one has
nonnegative source-dimension margin against its own published blockwise
contact-rank bound:

```text
(BCap,sCap)=(16,8):
  columns                         65,061,789,117,960
  one-node contact-rank bound             248,191,020
  columns - 262144*rank                      2,371,080
```

Every proper nested envelope is negative. The closest miss is obtained by
deleting only the top curvature layer:

```text
(BCap,sCap)=(16,7):
  columns                         64,261,883,128,438
  one-node contact-rank bound             245,142,304
  margin                                     -701,011,338.
```

Thus the existing dimension certificate is genuinely load-bearing in both
weighted-slope cap 16 and curvature depth 8. There is no smaller nested
raw-shape source to which the current rank bound can be mechanically
restricted while preserving even source nonnegativity.

The existing 52-chart consumer remains green if its full `J=64,L=3757`
box is retained:

```text
one exact-stratum chart cost           1,546,270,015,488
81,732 exact strata total            126,379,740,905,865,216
MCA allowance                        254,684,620,614,660,120
consumer slack                       128,304,879,708,794,904.
```

That consumer slack does not compensate a negative source margin: the two
inequalities serve different stages. Hence only `(16,8)` passes both current
gates. A smaller envelope could become viable only with a sharper rank bound
or a direct source theorem that bypasses this dimension estimate.

## 1. Exact nested frontier near the boundary

At full weighted slope cap 16, increasing the curvature depth gives:

| `sCap` | source columns | local rank | global source margin |
|---:|---:|---:|---:|
| 0 | 13,700,183,385,814 | 53,358,376 | -287,394,732,330 |
| 1 | 25,768,620,846,554 | 99,749,601 | -380,138,557,990 |
| 2 | 36,212,797,593,571 | 139,486,584 | -352,773,482,525 |
| 3 | 45,039,200,696,913 | 172,822,700 | -265,233,171,887 |
| 4 | 52,253,319,085,317 | 199,951,790 | -162,842,952,443 |
| 5 | 57,859,643,546,201 | 221,008,161 | -76,319,810,983 |
| 6 | 61,861,666,725,656 | 236,066,586 | -21,772,394,728 |
| 7 | 64,261,883,128,438 | 245,142,304 | -701,011,338 |
| 8 | 65,061,789,117,960 | 248,191,020 | **+2,371,080** |

Lowering the weighted slope cap also fails. The largest legal envelope at
`BCap=15` is `(15,7)` and has margin

```text
-108,395,787,462.
```

The small constant-T chamber identifies raw shapes `{1,R,S}` as its unique
inclusion-minimal rank-four family. The smallest nested target envelope which
contains those shapes is `(BCap,sCap)=(2,1)` (it also includes `R^2`), but its
target source ledger is far red:

```text
columns                          8,801,286,669,304
one-node contact-rank bound              34,984,662
global margin                         -369,732,566,024.
```

So the low raw shapes can be semantically sufficient in a small chamber
without being dimensionally self-supporting at target scale. The higher
shape layers are capacity/scaffolding for the full-source kernel, even if a
final four-boundary certificate can be represented by low boundary shapes.

## 2. Why deleting apparently negative layers is invalid

For reference, the full `(16,8)` blockwise decomposition is:

| exact `S` exponent | `Rmax=16-2S` | columns | local-rank slice | slice margin |
|---:|---:|---:|---:|---:|
| 0 | 16 | 13,700,183,385,814 | 44,566,684 | +2,017,294,575,318 |
| 1 | 14 | 12,068,437,460,740 | 41,600,054 | +1,163,232,904,964 |
| 2 | 12 | 10,444,176,747,017 | 38,218,593 | +425,401,903,625 |
| 3 | 10 | 8,826,403,103,342 | 34,332,839 | -173,744,643,474 |
| 4 | 8 | 7,214,118,388,404 | 29,853,390 | -611,768,679,756 |
| 5 | 6 | 5,606,324,460,884 | 24,690,904 | -866,247,877,292 |
| 6 | 4 | 4,002,023,179,455 | 18,756,099 | -914,775,636,801 |
| 7 | 2 | 2,400,216,402,782 | 11,959,753 | -734,961,087,650 |
| 8 | 0 | 799,905,989,522 | 4,212,704 | -304,429,087,854 |

These slice margins sum to `2,371,080`, but they are **not independent
ablation prices**. The kernel subtraction in the rank formula uses

```text
q=max(ceil((m-r)/2), m-r-(sCap-S)),
```

so changing the ambient top curvature depth changes the rank calculation in
earlier layers too. In particular, the raw `S=8` slice has a negative slice
margin, while adding it to the `sCap=7` envelope improves the recomputed total
margin by

```text
2,371,080 - (-701,011,338) = 703,382,418.
```

Greedily deleting the negative-looking top slices would destroy precisely
the cross-layer kernel relations credited by the published bound. Any
non-nested pruning needs a new rank theorem for the punctured shape set; the
current formula cannot certify it.

## 3. Relation to the constant-T collapse

The constant-T scalar trace STOP says the anchor-centered osculating traces
with positive companion exponent vanish after projecting all full-centered
contact variables to zero: `T'=T''=0`. It does **not** say raw `R` and `S`
source shapes are absent from, or useless in, the complete contact module.

The exact two-error constant-T shape ablation in
`.experiments/k0_constant_t_carrier_subset_gate_6900.py` makes the distinction
visible. In its faithful small chamber:

```text
raw {1,R}:       four-boundary gain 3,
raw {1,R,S}:     four-boundary gain 4,
```

and `{1,R,S}` is the unique inclusion-minimal gain-four shape set among all
64 subsets. Appending the boundary rows in either order shows each of
`Y,R,S,Z` adds one rank; raw `S` kills the final compatible covector rather
than contributing a scalar `T''` trace.

Therefore the target lesson is two-sided:

1. do not revive the collapsed anchor packet by merely counting its many
   scalar seed copies; and
2. do not prune the complete source down to scalar-visible shapes. The raw
   non-scalar `R/S` channels are exactly where the small full-source chamber
   recovers the fourth direction, and the target dimension certificate needs
   the entire `(16,8)` nested envelope.

This does not prove that every high target shape is semantically required by
the eventual rank-four theorem. It proves that every proper nested pruning
loses the **current** source-dimension certificate, while the only exact
constant-T mechanism test points toward retaining—not deleting—the
non-scalar curvature channel.

## 4. Reproduction and scope

`.experiments/k0_m47_weighted_shape_frontier_6900.cpp` imports the frozen
integer formulas from
`.experiments/promoted_second_jet_target_profile_search_6900.cpp`, enumerates
the 81 nested envelopes deterministically, and hard-checks the published
full-source and consumer totals. It uses signed 128-bit integers and performs
no field matrices, random sampling, `decide`, or `native_decide`.

Reproduction:

```text
g++ -O2 -std=c++17 \
  .experiments/k0_m47_weighted_shape_frontier_6900.cpp \
  -o /tmp/k0_m47_weighted_shape_frontier_6900
/tmp/k0_m47_weighted_shape_frontier_6900
```

The run is sub-second after compilation and uses negligible memory. The
conclusion is only about nested weighted-shape envelopes under the existing
rank formula. It does not justify arbitrary hole-punching, prove the
full-source dual-zero theorem, or create a 6900 candidate.

