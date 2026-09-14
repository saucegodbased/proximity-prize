### Lower 6900: coupled k17--k19 GREEN; symbolic Pascal theorem and exact A57 window frontier

Status first: the live verified score is still **68.10**. There is no 69.00
candidate, build, comparator run, or submission. These results replace two
large uncertainties by exact gates; they do not make the remaining work
mechanical.

#### 1. Three coupled pure-face Euler rows are exactly covered

Commit `94d7bcc` extends the corrected `k=17,18` gate from `7edc5cc` by a
third coupled row at `k=19`. The retained legal lanes are

```text
A2, A29, A71, A72.
```

The restricted primal has 4,436,009 variables against 4,413,474 rows. After
the exact residue-pairing elimination, its dual is a compact
76,149-to-98,684 polynomial map. A `5 x 2` shifted PM-basis computation gives

```text
final shifts  (86238,86238,86238,86238,86238)
threshold     81730
minimum gap    4508
leading determinant -1 mod 2130706433.
```

An independent verifier checks all ten basis-times-series products and the
exact determinant/shift gain 303,637. Peak PM-basis RSS was 1,417,268 KiB;
the verifier used about 62 MiB. Therefore the dual is injective, equivalently
the four lanes are surjective on the three coupled `k17,k18,k19` projections.
This is still a restricted projection, not membership of the fixed full
60-row F3 residue.

Receipts:

```text
input sha256  6f4f43aa939bdb833c8fdf3f9b68b554327dcde4557c424acbe04f2e9bff8dbd
basis sha256  05ddafb3e2fe90d08abeb962bd60faa35c4a5554d37f9ff361d0edc264f90e0c
```

#### 2. Exact symbolic contact rank theorem

Commit `227e4de` proves the fixed-outer-Z raw contact ranks without another
large active-degree matrix. At fixed

```text
n = y+q-s,  K=60-n,
```

put `t=u-v/2`. Raw columns become `v^s(1+t)^y`. At homogeneous degree
`H=s+j`, the target dimension is

```text
d=min(H+1,K-H).
```

If `m(A,n,s)` is the number of legal consecutive `y` exponents, finite
differences supply exactly `j=0,...,m-1`. Thus

```text
Jraw={H-s : 0<=s<=10 and 0<=H-s<m(A,n,s)},
rank(A,n,H)=min(|Jraw|,d).
```

The corresponding minor has the explicit binomial-Vandermonde determinant

```text
(-1/2)^(sum(j)-k(k-1)/2)
* product_(c<e)(j_e-j_c) / product_(a=0)^(k-1) a!,
```

so it is a unit in the target field. This covers the literal `s=10` and
`r+s=21` faces rather than invoking generic position. The formula reproduces
the independent dense ranks 56, 79, and 103 at active 77, 76, and 75.

The old closed staircase from the preceding comment is now definitively
superseded: it first misses one direction at active 68. A corrected minimal
prefix recurrence is exact and window-legal for every active degree 77 down
through 58.

#### 3. First real window obstruction: A57, but only 54,108 node dimensions

At active 57 the maximal legal all-node initial-prefix family has rank 1,341
against raw rank 1,342. The sole missing stratum is

```text
n=38, H=21, K=22, Jraw={11}, Jlegal={}.
```

Its omitted coordinate is

```text
(y,r,s,q,z)=(36,11,10,12,2625),
```

at the simultaneous slope/curvature boundary. Producing the eleventh finite
difference requires twelve consecutive `y` exponents. The first polynomial
would need thirteen complete jets, but its exact window is

```text
3,353,764 = 12*262144 + 208,036.
```

So this is not a missing 262,144-dimensional channel. A partial thirteenth
jet of degree below 208,036 remains, and the actual global node quotient has
dimension only

```text
262144-208036 = 54108.
```

A direct literal `(A,n)=(57,38)` matrix, independent of the symbolic rank
formula, has 87 raw columns, 86 legal columns, 132 rows, and ranks 87/86.
Its normalized row dual annihilates all 86 legal columns and evaluates to one
on the omitted coordinate.

```text
omitted-column sha256
  707ed944ad4eda2740da7470292017ad43aad3b46d2bc0c4830a0c28f38456dc
dual sha256
  ee4106cbef0fd9ae18a82d00f1692554c59aa0cbca9cae7aee0e12abfaa80be5
canonical replay sha256
  3312744f422d6f12ef581cf046c9a25f8e3cf831b60eb7fa134e7d268dda41de
```

This RED is for arbitrary raw all-node surjectivity, which is stronger than
the construction needs. There are 87 literal `z=2624`, active-58 predecessor
tails reaching the missing row. The current decisive gate is to apply the
A57 row dual to the *actual* incoming operator, retain the degree-208,036
fringe and every predecessor/kernel adjustment, and reduce the result to a
small polynomial-ring quotient. We are explicitly testing for a q26-style
Toeplitz/Hankel rescue; reachability alone will not be counted as a GREEN.

In parallel, the ratio-faithful F193 complete `{pure,R,S}` first-shell packet
gate is in its final exact elimination under a hard 3 GiB cap. Its earlier
`{pure,R}` ablation was RED. We will report the full-shell result only after
the exact quotient ranks finish.

