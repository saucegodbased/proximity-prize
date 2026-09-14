# Accepted Higher* 6810 -> 6900 second-jet retarget audit

## Decision

**STOP a literal/mechanical retarget.**  The accepted certificate at commit
`09d8a2a` does not merely need new `decide` receipts: every one of its four
load-bearing relaxed second-jet sources fails at target agreement `180413`.
Three also lose the premise that identifies the closed rank formula.  The
scalar-list source fails independently.

**GO only for a source/consumer pivot.**  The generic second-jet library is
reusable and target-positive lower-derivative profiles exist, but none has yet
been connected through all accepted root geometry, phase cases, and the finite
ledger.  More importantly, the accepted seedless scalar family is on the wrong
side of its interpolation threshold and needs a stronger support/rank idea.

This audit used the public accepted submission
`1852e895-c0db-46ad-8705-e0c92d638224`, its detailed note, and a detached
read-only clone of accepted commit `09d8a2a`.  The exact cheap checker is
`.experiments/higher6810_secondjet_retarget_exact.py`.  It complements
`.experiments/higher6810_to_6900_numeric_retarget.py`, which audits A/B/T,
the legacy sources, the scalar source, and the MCA arithmetic.

## Exact target and accepted profile data

The requested claim is

```
ProtocolClaim 6900 10461695 33554432
errors     = floor(10461695 / 128) = 81731
agreement  = 262144 - 81731       = 180413
gap        = 180413 - 131071       = 49342
gap + 2    = 49344
```

The accepted cutoff in `HigherRootInterpolation6810.lean` is

```
m * 181294 - reserve(k,n0,h) * 50225
```

and its honest target substitution is

```
m * 180413 - reserve(k,n0,h) * 49344.
```

Keeping the four accepted profiles gives these exact signed certificate
dimensions, `coefficientCount - 262144 * relaxedRankBound`:

| profile `(m,B,s,U,L,k,n0)` | accepted margin | target margin | target closed-cap slack |
|---|---:|---:|---:|
| P0 `(132,54,24,180,1800,5,7)` | +394,716,012,196 | **-22,425,433,492,499** | **-1**, first bad `h=5` |
| P1 `(134,56,25,180,2749,6,8)` | +4,523,000,772 | **-38,371,960,126,026** | +1 |
| P2 `(136,56,25,185,2526,6,8)` | +4,095,347,555 | **-36,795,509,129,843** | **-1**, first bad `h=6` |
| P3 `(116,46,21,158,2695,5,7)` | +675,718,382 | **-19,989,964,001,229** | **-1**, first bad `h=5` |

The accepted values are reproduced exactly, including coefficient counts and
rank bounds, before target values are accepted by the checker.

### First theorem gate, not merely the first changed literal

After mechanically regenerating P0's changed `coefficient_count` numeral, the
first substantive theorem that cannot be replayed in source order is
`HigherRootSources6810.P0.cutoff_caps`: at `h=5`, the right-hand cap is `179`
but `U=180`.  Consequently `rankBound_eq_closed` cannot be invoked as in the
accepted proof.  P2 and P3 have the same failure at `h=6` and `h=5`.

This is not only a one-unit cap nuisance.  Lowering `U` by one to restore the
premise leaves exact target margins

```
P0 U=179: -22,466,434,429,446
P2 U=184: -36,895,959,573,145
P3 U=157: -20,050,645,248,807
```

P1 already satisfies the closed-cap premise, so its next theorem
`dimension_gap` fails outright by `38,371,960,126,026`.

For every fixed accepted shape, the target margin is affine in `L` in this
chamber and has a negative slope:

```
P0 -4,142,133,645 per additional L
P1 -8,109,345,493 per additional L
P2 -7,782,234,760 per additional L
P3 -4,624,047,187 per additional L
```

Thus increasing `L` cannot repair a profile.  Even after restoring the cap and
lowering `L` to the basic admissible boundary `m+B+s`, all four margins remain
negative (between -8.37e12 and -18.83e12).

The scalar source is a smaller but independent exact stop:

```
(m,L,s)=(113,156,34)
accepted margin = +3,464,475
target margin   =   -482,231,575
```

The companion checker's exact 4,714,130-profile bounded seedless scan found no
positive alternative in its natural nontruncated family through `m=5000`.
That is finite evidence, not a global impossibility theorem, but it makes new
scalar mathematics the honest critical path.

## Reconstructed profile search and the derivative-strength wall

The existing optimizer
`.experiments/promoted_second_jet_target_profile_search_6900.cpp` implements
the same closed second-jet source formulas and a top-cell consumer proxy.  I
replayed it with deterministic seed `6900`, adding the four newly accepted
profiles and widening the sampled domain to

```
s <= 30, B <= 70, m+s <= U <= 200, L <= 8000,
all reserve k and n0 admitted by the budget-flag shape,
200000 sampled shapes.
```

Results by derivative reserve were:

| k | source-positive hits | first positive profile |
|---:|---:|---|
| 2 | 34,818 | `(146,67,30,200,1498,2,3)`, margin +2,215,217,464 |
| 3 | 10,511 | `(148,66,30,200,2380,3,4)`, margin +12,046,424,677 |
| 4 | 382 | `(148,66,30,200,5360,4,5)`, margin +5,559,679,537 |
| 5--10 | 0 | none in this bounded seeded sample |

The best k=4 top-cell candidate in that run was

```
(m,B,s,U,L,k,n0) = (148,64,30,200,5465,4,5)
exact source margin = +3,553,593,355
closed-cap slack    = +2
```

This is the best nearby **source-only** lead, not a 6900 proof.  The accepted
P0/P3 consumers require divisibility through derivative 5 and P1/P2 through
derivative 6.  Their `HigherRootRegularData*`, `HigherRootSourceStage*`,
asymmetric count, arithmetic, carrier, and phase modules hardcode those
orders and the resulting budget flags.  At the exact accepted shapes, scanning
all admissible reserve patterns shows the strongest source-positive order is
only `k=2`; `k>=3` is already negative.  Therefore the found k=4 profile still
requires a new consumer integration and a full finite-ledger replay.

The zero k>=5 result is explicitly a bounded-search observation, not a theorem.
It is nevertheless a fast discriminator: another search over the same body is
unlikely to produce the accepted derivative strength without expanding caps
or improving the rank argument.

## Mechanical fraction and remaining uncertainty

There are two different percentages, and conflating them caused earlier
confidence to be too high:

* By module/code volume, roughly **70--80%** of the generic field, geometry,
  counting, and protocol skeleton can probably be reused.
* By remaining load-bearing proof work, the point estimate is only **20%
  mechanical / 80% new mathematics or newly validated integration**, with
  about ±10 percentage points of uncertainty.

The exact arithmetic-stop confidence is above 99%.  End-to-end feasibility of
the k<=4 root pivot plus a new scalar source remains only about 15--25%, i.e.
75--85% route uncertainty.  No phase/ledger build should start merely because
a source margin turns green; first demand both (1) a target-positive scalar
source and (2) a theorem-level caller from the proposed root profile into the
accepted counting interface.

## <=30 minute falsifier

Run:

```
prlimit --as=1073741824 --cpu=30 \
  python3 .experiments/higher6810_secondjet_retarget_exact.py
```

It reproduces accepted P0--P3 receipts, calculates target margins and the
first failed cap level, proves by exact finite arithmetic that changing only
`L` moves every margin in the wrong direction, checks the nearby green source
profiles, and rechecks the scalar deficit.  It uses no Lean `decide` or
`native_decide`; measured runtime is well below one second and memory is under
the 1 GiB process cap.
