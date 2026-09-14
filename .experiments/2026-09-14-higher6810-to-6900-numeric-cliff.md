# Higher*6810 -> 6900: exact interpolation-cliff audit

This note audits the accepted lower-track commit `09d8a2a` (score 6810) at
the proposed 6900 coordinates

```
agreement = 180413
errors    = 81731
gap       = 49342
```

The accompanying checker is
`.experiments/higher6810_to_6900_numeric_retarget.py`.  It is a direct,
stdlib-only integer transcription of the imported Lean definitions
`RCN100.coefficientCount`, `RCN119.localRankBound`, and their seedless
`RCN279`/`RCN285` counterparts.  Its accepted-profile assertions reproduce
every nullity literal in `HigherKernels80850.lean`, so the arithmetic is tied
to the actual accepted proof rather than an approximate model.

## Main result: literal retargeting is impossible

At agreement 180413, the signed dimensions `coefficientCount - 262144 *
localRankBound` of all accepted kernels are negative:

| kernel | signed dimension at 180413 | first positive agreement |
|---|---:|---:|
| global A | -76,612,802,872,130 | 181294 |
| global B | -22,658,732,083,671 | 181294 |
| terminal T | -32,756,551,753,835 | 181294 |
| Source00 | -220,090,056,863,886,727,062,784 | 180997 |
| Source01 | -20,726,846,964,163,996,398,886 | 180940 |
| Source02 | -18,980,938,035,806,229,038,886 | 180950 |
| Source03 | -930,640,210,049,624,524,047 | 180986 |
| Source04 | -58,495,105,198,091,600,080 | 180989 |
| Source05 | -19,550,893,759,173,647 | 180999 |
| Source06 | -1,775,385,389,804,909,385,811 | 180891 |

Lean's natural-number subtraction therefore gives nullity zero for every one
of them.  In particular, A/B/T are deliberately sitting on a one-point cliff:
all three are nonpositive at 181293 and first become positive at the accepted
agreement 181294.  Increasing each multiplicity to the largest value permitted
by its existing middle-cap shape inequality does not repair the target; the
checker prints the still-negative exact values.

The mandatory scalar-list interpolant fails independently.  Its accepted
profile `(m,L,s)=(113,156,34)` changes from signed nullity `+3,464,475` at
181294 to `-482,231,575` at 180413.  Its first positive agreement is 181288.
Thus regenerated phase and ledger tables cannot possibly make the accepted
proof work at 6900: construction of the starting polynomials already fails.

## Bounded escape search

Running the checker with `--search` exhausts 4,714,130 minimal-shape seedless
profiles in the same nontruncated support regime:

```
1 <= m <= 5000
L = ceil((m * 180413 + s) / 131071) - 1
L >= m - 1 + s
```

No profile has positive signed dimension.  The least-negative result is only
`-32,389`, at the degenerate `(m,L,s)=(1,1,0)` profile.  This is an exact finite
search, not a global impossibility theorem: it does not cover truncated
triangular supports (`s > L-m+1`), a different monomial body, or a different
interpolation/rank argument.  It does, however, cover the accepted profile and
its natural multiplicity-scaled neighborhood, so simply making multiplicities
large is not an escape.

## Ledger headroom is not the immediate issue

With the accepted scalar list formula, the target list budget is
`7,332,669,231`.  The resulting MCA budget is `274,980,720,778,725,856`, leaving
`244,304,501,834,296` above the accepted tight ledger bound
`274,736,416,276,891,560`.  That small headroom would require a new ledger
optimization later, but it is currently secondary: no accepted interpolation
kernel exists at the target agreement.

For process calibration, the accepted 6808 -> 6810 transition increased the
tight ledger bound by `15,945,165,982,517,811` to buy only 20 more errors while
also expanding the wide caps from `(35,156,8121)` to `(37,164,8865)`.  Linear
extrapolation is not a proof, but it reinforces the exact nullity result: an
881-error move is not a mechanical extension of this certificate.

## Correct pivot

Any credible 6900 route must change at least the scalar interpolation support
or its local-rank bound, and must replace/rebalance the A/B/T kernels.  Phase
table regeneration should be postponed until a target-agreement kernel has a
strictly positive signed dimension.  The fastest go/no-go test for every new
proposal is therefore the exact dimension calculation in this checker.
