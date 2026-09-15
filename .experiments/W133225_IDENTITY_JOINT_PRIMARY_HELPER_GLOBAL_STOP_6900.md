# W=133225 identity helper: joint primary/helper global STOP

## Result

Jointly changing the primary weighted source, the helper weighted source, and
the terminal rectangular cut does **not** close the W=133225 identity-node
architecture at `N=262143`.  The same conclusion holds a fortiori at
`N=262144`.

This strengthens the fixed `J211/D55` result: it covers every admissible
primary and helper profile in the current finite-prefix weighted source
family and every rectangular terminal split `(J,D,T=floor(D/2))`, while
carrying the complete cheap and primary-cleanup list costs.  Helper-exit costs
are nonnegative, so the final rejection may safely omit them whenever cheap
plus cleanup already exceeds the retained floor.

## Minimum possible primary cleanup

The full source scan at `N=262143` has two chambers.

* In `m>=8k-1`, all source-positive profiles are enumerated with the exact
  finite-prefix rank and conservative certified source columns.  Among
  1,900,713 positive profiles, the least cleanup is

  ```text
  k=61, m=547, M=740, D=244, T=122
  cleanup = 15,522,723,255,702,274.
  ```

* In `m<8k-1`, the adaptive exact-rank certificate leaves 25,142 potentially
  source-positive singleton profiles, all with `k>=588`.  Since every cleanup
  coordinate is monotone in `(M,D,T)` and source feasibility gives
  `M+1>=4k`, these are strictly more expensive than the `k=61` primary.

The primary flag at the minimum is `(496,122,122)`.  No helper-exit cost has
yet been charged in this lower bound.

At `N=262144`, the same profile remains source-positive and has cleanup
`15,522,843,663,263,141`; larger node count only shrinks every source kernel
and increases every count numerator.

## Exact ledger-feasible cap region

At one exception, the core floor is

```text
263,611,557,201,785,349.
```

Subtracting the global minimum primary cleanup leaves at most

```text
248,088,833,946,083,075
```

for the cheap regular family, even before helper exits.  Exact evaluation of
the actual `flagMixed` and `honestReducedAgreementFlag` formulas reduces all
rectangular caps to three gates:

1. `D<=54` (any `J`);
2. `D=55` and `J<=211`;
3. `56<=D<=110` and `J<=203`.

For `D>=111`, the coordinatewise-monotone minimum `(J,D)=(111,111)` already
costs

```text
cheap(111,111) + minimum cleanup
 = 266,107,998,669,189,501
```

and is red by `2,496,441,467,404,152`.

For `56<=D<=110`, exact evaluation of the 55 boundary values at `J=204`
has its minimum at `D=56`.  That boundary is already

```text
cheap(204,56) + minimum cleanup
 = 264,040,652,368,261,583
```

and is red by `429,095,166,476,234`.  Hence ledger feasibility forces
`J<=203` throughout that range.

At `D=55`, the first excluded J value is

```text
cheap(212,55) + minimum cleanup
 = 264,254,749,490,380,629
```

red by `643,192,288,595,280`, so feasibility forces `J<=211`.

At `N=262144`, the same three gates remain exact.  The corresponding three
deficits increase to `2,499,153,517,568,416`, `431,785,835,405,145`, and
`645,885,171,793,253`.

## Exhaustive helper rejection

Every ledger-feasible case is rejected by a necessary band inequality:

```text
cap gate                 unclipped result       clipped result
-----------------------------------------------------------------
D54 (J unrestricted)    0 necessary survivors  implied by D55 STOP
J211 and D55            0 joint survivors      0 D55 survivors
J203 and D110           0 joint survivors      0 D110 survivors
```

The unclipped enumerations cover all 8,712,828 admissible profiles.  The
clipped adaptive enumeration covers all 14,896,352 remaining profiles.  The
rejection bounds are the certified source-column upper bound and termwise
product-band lower bounds described in
`W133225_IDENTITY_ONE_EXCEPTION_FIXED_CAP_EXHAUSTIVE_STOP_6900.md`; no
best-observed-profile pruning is used.

This partition is exhaustive:

* a putative cap with `D<=54` would pass the easier D54 test;
* at `D=55`, list feasibility forces `J<=211`, so it would pass the easier
  J211/D55 test;
* at `56<=D<=110`, feasibility forces `J<=203`, so it would pass the easier
  J203/D110 test; and
* no `D>=111` cap reaches the helper stage because its list lower bound is
  already above the core floor.

Therefore there is no jointly legal primary/helper/cut row in this family.

## The tempting J212/D55 helper is real but irrelevant

The one-node shortening really does cross the algebraic helper boundary.  For

```text
k=1312, m=11803, B=2129414639, M=15983, D=5248, T=2624
```

the conservative source kernel is `133,514,624,140,607,984`; the already
formal active-band formulas give

```text
J212 margin  +385,174,891,949,264
D55 margin       +671,050,464,644.
```

But `cheap(212,55)` plus the cheapest possible primary cleanup is already red
by 643 trillion, before this helper's exit incidence is paid.  It is therefore
not a candidate and should not be formalized as one.

## Separate J-heavy and D-heavy sources

For a possible two-helper variant, the independent exhaustive scans give the
lowest helper-exit mixed cost against the minimum primary:

```text
J-heavy, cap J212:
  (k,m,M,D,T) = (1172,10499,14217,4688,2344)
  flag         = (9529,2344,2344)
  kernel       = 83,769,136,551,706,925
  J margin     = 1,377,021,146,105
  mixed cost   = 403,968,771,465,754
  exit cap     = 699,681,872,154,479

D-heavy, cap D55:
  (k,m,M,D,T) = (1240,11216,15188,4960,2480)
  flag         = (10228,2480,2480)
  kernel       = 107,134,367,780,282,750
  D margin     = 1,750,136,233,610
  mixed cost   = 429,138,608,127,080
  exit cap     = 743,276,525,209,268.
```

No helper passes J211 even as a one-band necessary test, and no clipped helper
passes J212.  No clipped helper passes D55 either.  Splitting helpers therefore
does not restore the old J211/D55 corner: it necessarily moves the cheap
rectangle to J212/D55, whose cheap-plus-primary lower bound is already red.

The two exit caps sum to about 1.443 quadrillion if charged separately.  Any
two-helper rescue must prove a genuinely nonrectangular/shared-factor count;
it cannot use the existing complete rectangular ledger unchanged.

## Verification and artifacts

* `weighted_helper_n262143_joint_filter_6900.cpp` performs the complete
  necessary-band enumerations and evaluates formal active-band survivors.
* `weighted_joint_primary_helper_n262143_6900.cpp` recomputes N-dependent
  source and ledger terms and exhausts the primary source-positive chamber.
* `WeightedIdentityOneExceptionLedgerW1332256900.lean` certifies the exact
  ledger boundaries, deficits, separate helper flags, mixed costs, and exit
  caps.  It builds under a 6 GiB allocator cap and prints only `propext`,
  `Classical.choice`, and `Quot.sound` for the relevant roots.

Reproduction:

```text
OMP_NUM_THREADS=16 weighted_helper_n262143_joint_filter_6900 \
  8000 12000000 1000000 54
OMP_NUM_THREADS=16 weighted_helper_n262143_joint_filter_6900 \
  8000 12000000 211 55
OMP_NUM_THREADS=16 weighted_helper_n262143_joint_filter_6900 \
  8000 12000000 203 110
OMP_NUM_THREADS=16 weighted_helper_n262143_joint_filter_6900 adaptive 203 110

weighted_joint_primary_helper_n262143_6900 \
  primary 1312 11803 212 55 68763
```

## Decision

**Global numeric STOP** for the present single weighted-helper architecture at
W=133225, including joint primary/helper retuning, at both N=262143 and
N=262144.  The remaining possible variation is nonrectangular branch sharing,
not another rectangular profile search.
