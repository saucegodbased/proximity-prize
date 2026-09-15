# Seedless scalar truncated-support audit at lower 6900

## Verdict

**STOP for the saturated/minimal-shape retarget of the exact
`RCN279`/`RCN285` scalar source.**  Truncating the local support does not rescue
the source.  There is no positive dimension gate among the 12,497,599
truncated profiles with `m <= 5000`, and an analytic monotonicity reduction plus
the protocol capacity cutoff reduces *every scalar-budget-viable saturated
profile* to 617,276 first-frontier checks.  All are negative.  The best is the
tiny profile

```text
(m,L,s) = (2,2,2)
coefficientCount = 1,116,392
localRankBound   = 6
coefficientCount - 262144*localRankBound = -456,472.
```

This is not a 6900 candidate and it does not alter a submission.

There is one important scope qualification.  The scalar consumer itself does
not require the saturation inequality.  I therefore also audited arbitrary
clipped truncated boxes, not only the earlier search chamber.  An exact scan of
12,410,311 such profiles through `m <= 300` finds no positive gate; its best is
still negative, `-163,462` at `(m,L,s)=(2,0,0)`.  The companion algebra also
rules out the whole subchamber `L<m`.  A machine-checked theorem for all
unsaturated boxes with `L>=m` is **not** claimed here.  Thus the scoped result is:

* saturated/minimal-shape truncated escape: closed;
* arbitrary clipped truncated escape through `m=300`: exact finite STOP;
* arbitrary clipped `L<m`: paper-algebra STOP;
* unbounded unsaturated `L>=m`: still outside the certified scope, although
  the finite scan and asymptotic margins are negative.

## Literal formulas

The audit uses

```text
n = 262144, w = 131071, A = 180413, gap = A-w = 49342,
D = m*A.
```

No randomized rank model is used.  The program is a direct integer evaluation
of

```text
RCN279.coefficientCount D w L s
RCN285.localRankBound m L s.
```

For `q=L-s`, the local input dimension is

```text
I(M,L,s) = sum_{i=0}^M min(s+1,L+1-i).
```

The rank is evaluated in closed form from

```text
sum_{r=0}^{m-1} I(min(r,L),L,s)
  - sum_{h=1}^{min(floor(m/2),L,s)}
      I(min(m-2h,L-h),L-h,s-h).
```

The key simplification is that `(L-h)-(s-h)=q` is invariant in the kernel
sum.  Its pieces are only linear or quadratic in `h`.  The script tests this
closed form against the direct definition on every small shape before doing
the large scan.  Coefficients are likewise summed by residue intervals of
`floor((D-1+j)/w)`, using `O(1+s/w)` memory and time per profile rather than a
large Lean evaluation.

## Why only the first saturated truncated slope matters

For a saturated box,

```text
D+s <= w*(L+1).
```

The coefficient count is independent of any further increase in `L`, while
the rank bound is nondecreasing in `L`.  The latter is literal: increasing `L`
adds `max(0,M-(L-s))` inputs to a contact block and at most
`max(0,M-h-(L-s))` inputs to its embedded kernel.

Use the least saturated cap

```text
L(s) = floor((D+s-1)/w).
```

Truncation is `L<m-1+s`, or `q=L-s<=m-2`.  Its first occurrence is

```text
s0 = ceil((m*(A-w)+w)/(w-1)),
L0 = m+s0-2,
q0 = m-2.
```

After that first slope, signed nullity strictly decreases.  If the next slope
also increments `L`, the rank increment is at least

```text
m=2k:   k*(k+1)
m=2k+1: (k+1)^2.
```

The new coefficient slice is at most

```text
w*(q+1)*(q+2)/2 <= w*m*(m-1)/2,
```

which is strictly below `n` times that rank increment because
`n=2*(w+1)`.

If `L` does not increment, the new `q` is at most `m-3`.  Summing
`min(m-2h+1,q+1)` over contact kernels and checking the four parities gives

```text
4 * rankIncrement >= (q+1)*(q+2).
```

Again `n=2*(w+1)` makes the charged rank strictly larger than the new
coefficient slice.  This proves the monotonic reduction; the 617,276 checks
below are not standing in for billions of omitted later slopes.

## Scalar-budget viability cutoff

The standard scalar consumer budget for caps `(L,s)` is

```text
capY      = 1 + 2*w*L
capR      = w*(2*s-1)
regular   = (n-w)*(capY*s + capR*L)
singular  = (2*s-1)*L
budget    = floor((regular + singular*gap)/gap) + 1.
```

It is increasing in the relevant positive caps.  At the first truncated
frontier it crosses the entire protocol capacity

```text
2130706433^6 / 2^128 = 274,980,728,111,395,087
```

between consecutive multiplicities:

```text
m=617277, (L,s)=(849654,232379):
  budget = 274,980,714,544,786,041  (still below capacity)
  signed nullity = -71,775,483,191,503,588,622

m=617278, (L,s)=(849655,232379):
  budget = 274,981,038,183,248,926  (already above capacity).
```

Every later truncated slope has at least that first-frontier budget.  Hence no
`m>=617278` saturated profile can fit even before assigning one unit to the MCA
ledger.  Exact first-frontier evaluation for every `2<=m<=617277` has maximum
`-456472` at `m=2`.

## Unsaturated qualification and low-total-cap algebra

Write `q=L-s` and `t=m-q`.  Truncation means `t>=2`.  If `L<m`, every admitted
coefficient has positive weighted width.  Expanding the exact formulas by the
three rank cells (`2s<t`; `2s>=t` with `s<=floor(m/2)`; and
`s>floor(m/2)`) gives

```text
262144*localRankBound - coefficientCount >= m*(262144-180413)
                                               = 81731*m.
```

For example, in the first cell put `t=2s+1+u` and `m=t+v`.  Six times the
difference from `81731*m` is

```text
228239*s^3 + 245193*s^2*u + 439524*s^2*v + 929910*s^2
+ 490386*s*u*v + 735579*s*u + 97167*s*v^2 + 1027077*s*v
+ 211285*s + 490386*u*v + 97167*v^2 + 97167*v,
```

which is nonnegative.  Splitting `t` and `m` by parity in the other two cells
produces respectively 19- and 20-term polynomials with positive coefficients.
This is a paper algebra check, not exported as a generic Lean theorem.

For the remaining unsaturated `L>=m` chamber, the exact clipped scan uses
`q=0,...,m-2` and all slopes through the final positive weighted slice.  The
receipt through `m=300` is:

```text
profiles checked = 12,410,311
positive gates   = 0
best gate        = -163,462 at (2,0,0).
```

This explicit qualification matters: saturation is a search normalization,
not a premise of `RCN279.exists_nonzero_kernel_array` or of the scalar-list
consumer.

## Reproduction and formal checks

```bash
python3 .experiments/scalar_seedless_truncated_support_audit_6900.py \
  --max-m 5000 --general-max-m 300

lake env lean -j1 -s8192 -M4096 \
  .experiments/ScalarSeedlessTruncatedSupportArithmetic6900.lean
```

The combined Python run checked 24,907,910 explicitly enumerated profiles plus
617,276 analytically sufficient viable frontiers in about 102 seconds, with
13.6 MiB maximum RSS.  The Lean file builds in about four seconds.  Its printed
axioms are only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`native_decide`, `sorry`, or added axiom.

## Process conclusion

Do not spend more time retuning the accepted 6811 scalar profile inside the
saturated RCN279/RCN285 shape: the entire viable truncated continuation is now
negative.  If this scalar arm is revisited, the only honest remaining target is
a proof of the unsaturated `L>=m` inequality (or a genuinely sharper local-rank
theorem), not another nearby `(m,L,s)` grid search.
