# W133233 staircase win and absolute source ceiling

Date: 2026-09-15 UTC. Scope: the existing order-two weighted source engine at
the full identity core `n = 262144`. This is an exact arithmetic audit, not a
`ProtocolClaim 6900` and not a submission.

## Reproducer

The executable source is `weighted_staircase_dp_6900.cpp`. It reuses the
cross-checked finite-rank, column, relaxed-band, flag-incidence and cleanup
formulas from `weighted_w133226_cutoff34_full_audit_6900.cpp`, while computing
the shortened-Johnson value from the requested `W`.

```text
g++ -std=c++17 -O3 -fopenmp \
  .experiments/weighted_staircase_dp_6900.cpp -o /tmp/wstair
/tmp/wstair 133233 1 8 audit233
/tmp/wstair 133381 1 8 source
/tmp/wstair 133382 1 8 source
```

The exhaustive source scan uses exactly

```text
1 <= k <= floor(11810/8) = 1476
max(1,8k-1) <= m <= min(11810,12k).
```

No `decide`, `native_decide`, large matrix, random sampling, or floating point
arithmetic occurs.

## Strongest local result: W133233

The least uniform shortened-Johnson cap is `v = 68808`; its strict margin is
`31,449,812,047`.

Primary source:

```text
(k,m,B,M,D,T) = (64,575,103737475,778,256,128)
rank             = 1,804,560,903
columns          = 473,055,821,845,162
kernel           = 1,008,489,130
flag             = (522,128,128)
```

Helper source:

```text
(k,m,B,M,D,T) = (1312,11810,2130677530,15992,5248,2624)
rank             = 314,478,378,574,100
columns          = 82,565,146,391,030,259,161
kernel           = 126,526,318,101,388,761
flag             = (10744,2624,2624)
```

Use skinny endpoints `J <= 63` and `D <= 10`, and only two terminal
rectangles:

```text
(J,D,T) = (208,55,27)
(J,D,T) = (212,14,7).
```

The three complement gates are the start `(64,56)`, transition `(209,15)`,
and end `(213,11)`. Their exact relaxed-band margins below the helper kernel
are respectively

```text
1,520,809,194,541,479
1,654,244,064,685,837
  542,004,585,684,093.
```

The complete branch totals, each including the corrected nonactive cleanup,
are

```text
rectangle (208,55,27)       262,780,745,638,709,656
rectangle (212,14,7)         36,862,890,276,845,811
jet skinny J<=63             73,833,186,778,392,523
derivative skinny D<=10     228,139,953,809,003,299
core floor                  263,611,557,201,523,206
```

Thus the worst branch is the first rectangle and the exact headroom is
`830,811,562,813,550`.

All four terminal agreement flags pass the small-family, curve absorption,
surface absorption and characteristic projection gates. The tight projection
is the jet-skinny branch at `2,090,026,071 < 2,130,706,433`, leaving
`40,680,362`. The primary/helper projection is `1,343,488`, leaving
`2,129,362,945`. The shared helper exit is `865,750,425,908,974`; corrected
cleanup is `18,858,596,479,335,803`.

## Absolute source ceiling

An exhaustive scan over the domain above gives:

```text
W=133381: 19,953 positive sources
  best (k,m,M,D) = (1316,11808,15971,5264)
  best kernel    = 755,968,274,628,821

W=133382: zero positive sources
  best (k,m,M,D) = (1,7,9,4)
  best kernel    = -5,804,586
```

Higher canaries `133500`, `135000`, `140000`, and the required high window
`149485` also have zero positive sources. At `149485`, the best source in this
entire domain has kernel `-10,573,004`.

## Verdict

The monotone staircase fixes the previously reported W133233 local terminal
failure and is substantially stronger than the fixed two-arm partition.
However, no retuning or larger staircase can take this source engine past
W133381: at W133382 the source-positive premise is false for every allowed
profile, long before W149485. This route is therefore a useful local adapter
and a decisive **STOP** for the 6900 high-window objective. A genuinely new
high-window source is required.
