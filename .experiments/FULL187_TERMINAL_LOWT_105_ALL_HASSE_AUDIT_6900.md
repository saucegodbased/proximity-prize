# Full187 terminal low-T 105/103-shape all-Hasse audit

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production and the
submission root are unchanged.

## Result

The 105 zero columns of the exact `q=0` low-`T` corner matrix are **not an
accidental 105-dimensional kernel**: every one is individually zero. Their
terminal shapes `(r,s)` have the exact compact description

```text
0 <= s <= 8,
r + s + max(0, 3s - 17) <= 16.
```

Equivalently, their row lengths for `s=0,...,10` are

```text
17, 16, 15, 14, 13, 12, 10, 6, 2, 0, 0,
```

which sum to 105.

That 105 count uses agreement-Hermite capacity only. It is too optimistic for
the affine CRT which must also retain arbitrary values at all 81,731 error
nodes. Repeating the entire local-pivot/corner classification with the sharp
strong threshold

```text
width >= g*depth + 81731
```

leaves **103**, not 105, safe shapes. The two losses are exactly `(5,7)` and
`(1,8)`. The 103 shapes are characterized by the preceding inequality plus

```text
s <= 6  or  r + 4s <= 32.
```

Their row lengths are `17,16,15,14,13,12,10,5,1,0,0`. Every surviving
coefficient-Hasse order from these 103 shapes is locally licensed by either
the strong arbitrary-error CRT or the sharp order-two leading pivot.

Each lost shape has exactly one `q=0` strong obstruction:

| `(r,s)` | `(f,aE,cS)` | passive `h` | Hermite margin | row `(T,E,R,S,h)` |
|---|---|---:|---:|---|
| `(1,8)` | `(3,3,0)` | 70 | 50,882 | `(0,3,1,8,70)` |
| `(5,7)` | `(4,4,0)` | 66 | 67,839 | `(0,4,5,7,66)` |

Both margins are nonnegative, explaining why the agreement-only audit called
them safe, but both are below 81,731. Their local pivot threshold is 2 while
`T=0`. The passive factors are recorded, not cancelled.

## Why `q=0` is genuinely worst

Fix `(r,s;f,aE,cS)` and write `b=f+2aE+cS`. At Hasse order `q`, survival is

```text
q+b < 60.
```

Thus every positive-`q` origin is already present at `q=0`. Its Hermite
margin changes by

```text
margin(q) = margin(0) + g*q.
```

Consequently, failure of either the agreement threshold `0` or the strong
affine threshold `81731` at positive `q` implies failure at zero. In the
local-pivot inequality, only the contact coordinate
changes:

```text
T(q) = T(0) + q.
```

All other indices, including the passive `u1^h` tag, and the pivot threshold
are fixed. The audit retains `h` in every row key and never divides by
`u1^h`. A pivot failure
`T(q)<threshold` therefore implies `T(0)<threshold`. So an obstruction at any
surviving `q>0` would force a `q=0` obstruction. Since the 103 strong columns
have no such `q=0` origin, none can appear later. The Lean file proves these
monotonicity implications without `decide` or `native_decide`.

## Exact all-Hasse receipt

Across the 103 strong shapes:

| Hasse class | surviving origins | capacity | sharp pivot | obstruction |
|---|---:|---:|---:|---:|
| `q=0` | 697,825 | 676,776 | 21,049 | 0 |
| `q>0` | 10,547,200 | 10,498,193 | 49,007 | 0 |

The maximum surviving Hasse order is 59.

This is a complete **local licensing** theorem for the 103 strong coordinate
channels, but it is not a closed global terminal subspace. Positive Hasse
tails produce 290,985 distinct contact-row keys, of which 104,880 do not
occur in the `q=0` row set. Even among structured rows, positive `q` produces
31 new pivot-row keys. Every one is locally licensed, but their pivot
remainders and simultaneous interpolation tails still need a global
triangular/confluence proof. Nothing here proves the four target packets or
THREE-RHS containment.

## Reproduction

```text
prlimit --as=1073741824 --cpu=60 -- \
  python3 -B .experiments/full187_terminal_lowT_hasse_closure_audit_6900.py

.experiments/run_lean_4g_capped.sh \
  .experiments/Full187TerminalLowTHasseMonotonicity6900.lean
```

The executable asserts all displayed counts, the compact inequality, and
the absence of every all-`q` local obstruction before printing its hashes.
