# Full187 terminal positive-Hasse collision blocks

## Result

The exact target-parameter audit in
`full187_terminal_hasse_collision_blocks_6900.py` enumerates every one of the
72,850 agreement-Hermite-structured `q = 0` terminal origins from the Full187
source.  Every origin lies in a finite same-output-row family obtained by:

1. moving from source stream `(r,s)` to `(r-j,s+j)`,
2. replacing `j` curvature choices by slope choices, and
3. taking coefficient-Hasse order `q = j`.

For every enumerated member the script checks the output row literally, the
finite-field scalar, and the strict half-open coefficient window.  All checks
pass at the target parameters

```text
p = 2130706433, N = 262144, w = 131071, g = 180413
m = 60, D = 10824780, J = 82, slope cap = 21, curvature cap = 10.
```

This exposes a real sparse, upper-unitriangular operator inside the terminal
map.  It does **not** prove packet containment, confluence, or the 6900 claim.
The same physical source stream participates in many other output families,
and the isolated charge-13 principal block is independently known to be
injective.  Therefore the remaining kernel must use cross-origin and/or
multi-grade quotient cancellation at the final shell.

## Exact row identity

For a terminal source stream `(r,s)`, write

```text
y = J-r-s,  h = y-f.
```

Choose `(f,aE,cS)` with contact weight

```text
f + 2*aE + cS < m
```

and with negative agreement-Hermite margin, exactly as in the preceding
Full187 terminal-contact audit.  Its `q = 0` row is

```text
(T,E,R,S,h)
  = (f-aE+cS, aE, f-aE-cS+r, s+cS, J-r-s-f).
```

For every legal `0 <= j <= cS`, the source stream `(r-j,s+j)`, local choice
`(f,aE,cS-j)`, and coefficient-Hasse order `j` produce exactly the same row:

```text
(j+f-aE+(cS-j),
 aE,
 f-aE-(cS-j)+(r-j),
 (s+j)+(cS-j),
 J-(r-j)-(s+j)-f)
  = (T,E,R,S,h).
```

The local scalar before coefficient-Hasse differentiation is

```text
sigma(f,aE,cS)
  = multinomial(f; aE,cS,f-aE-cS) * (-1/2)^cS  (mod p).
```

Thus the relative coefficient on the `j`th collision is

```text
sigma(f,aE,cS-j) / sigma(f,aE,cS)  (mod p).
```

All denominators and diagonal scalars are nonzero modulo the target prime.

## Exact taper

The source widths obey

```text
width(r-j,s+j) = width(r,s) + j.
```

Coefficient-Hasse order `j` lowers the polynomial degree bound by exactly
`j`, so

```text
width(r-j,s+j) - j = width(r,s).
```

There is no hidden endpoint truncation: every collision lands in precisely
the same strict half-open target window as its `q = 0` diagonal.  Ordered
along a constant-`r+s` line, the blocks are triangular with diagonal one
after normalizing by `sigma`.

## Complete target enumeration

The structured-origin count by extra charge `2*aE+cS` is:

| charge | origins | transition types `(f,aE,cS)` |
|---:|---:|---:|
| 0 | 6,397 | 56 |
| 1 | 5,536 | 52 |
| 2 | 9,555 | 95 |
| 3 | 7,928 | 85 |
| 4 | 9,846 | 117 |
| 5 | 7,716 | 102 |
| 6 | 8,019 | 118 |
| 7 | 5,808 | 102 |
| 8 | 5,148 | 105 |
| 9 | 3,223 | 80 |
| 10 | 2,299 | 75 |
| 11 | 990 | 45 |
| 12 | 352 | 21 |
| 13 | 33 | 3 |

The global collision-family length histogram is

```text
length:  1      2      3      4     5     6     7    8    9   10  11
count: 23739  17174  12049  8141  5250  3192  1805  921  405  143  31
```

This is a complete enumeration of the stated q=0 structured-origin scope,
not a sample.

## Charge 13: the exact A/B/C operators

The final charge consists of 33 origins, all on `r+s=21`, with 11 copies of
each transition type:

```text
A: (f,aE,cS) = (7,6,1)
B: (f,aE,cS) = (8,5,3)
C: (f,aE,cS) = (8,6,1).
```

Their principal scalars modulo `p` are

```text
kappa_A = 603758703
kappa_B = 693269975
kappa_C = 642373467.
```

After division by these scalars, their exact tapered operators are

```text
A_s/kappa_A = c_s - 2 Hasse_1(c_{s+1})

B_s/kappa_B = c_s - 6 Hasse_1(c_{s+1})
                        + 12 Hasse_2(c_{s+2})
                        -  8 Hasse_3(c_{s+3})

C_s/kappa_C = c_s - Hasse_1(c_{s+1}).
```

The B operator is a Hasse-binomial operator with coefficients
`(1,-6,12,-8)`.  It must **not** be described as the ordinary composition
cube of `1-2 Hasse_1`, because `Hasse_1 o Hasse_1 = 2 Hasse_2`.

The A equations recursively recover all 11 tapered source polynomials:

```text
c_10 = A_10/kappa_A,
c_s  = A_s/kappa_A + 2 Hasse_1(c_{s+1}).
```

Consequently the isolated principal charge-13 map is injective.  The useful
objects are instead its compatibility/cokernel expressions

```text
I_B = B/kappa_B - T_B T_A^{-1}(A/kappa_A),
I_C = C/kappa_C - T_C T_A^{-1}(A/kappa_A),
```

and their dual adjoints after the lower-charge and cross-origin rows are
included.  This sharply rules out a local charge-13 kernel argument.

## What this changes

Green conclusions:

- The terminal map contains an exact sparse same-row Hasse-collision graph,
  at all charges, not merely the three charge-13 transition types.
- The strict-window arithmetic is perfectly aligned; endpoint loss is not the
  blocker for these blocks.
- The charge-13 principal operator can be inverted explicitly from A, so B
  and C become exact compatibility equations.

Hard stop / remaining theorem:

- Do not search more small one-shell packet grids.  A target-scaled `q:t=2:1`
  control is injective even after the genuine unsafe deletion.
- Do not claim the A/B/C block itself supplies a kernel.  It is injective.
- The next object must be the induced compatibility operator after quotienting
  the lower-charge rows, using the **exact fourth boundary polynomial**
  `F3 = B(Y-P-(Z-gamma)q_H)`, not a pure `Z1` surrogate.
- A 6900 proof still needs a cross-origin/multi-grade cancellation or a dual
  annihilator for that induced final-grade operator.

## Reproduction

```bash
prlimit --as=1073741824 -- \
  python3 .experiments/full187_terminal_hasse_collision_blocks_6900.py
```

Observed resource use was about 141 MiB peak RSS and two seconds wall time.
Stable-output digest:

```text
f7e2e7022ec6c2aabc569a254714feefe7b9bcc937d0c91aa0e48ad1625cda76
```

Script digest:

```text
9e0d83183c73e65f378e3efbe23fae4ebf50b076b7d610b7e4671888f8efdbb8
```
