# K0 raw positive-Z face: the finite Y7 repair and its target mismatch

Date: 2026-09-15 UTC. Scope: exact lower-6900 mechanism discriminator. This
changes no production candidate or submission.

## Exact finite result

On the corrected formal-contact `F_101` m6 control, the complete cap-L8
source has contact rank/nullity `4719/45` and boundary gain three. Append
only the 252 new raw (`R=S=0`) positive-Z columns at cap L9, ordered by
increasing Y exponent:

```text
through Y   columns added   contact increment   total nullity   boundary gain
base                    0                   0              45               3
0                      48                  48              45               3
1                      91                  91              45               3
2                     129                 129              45               3
3                     162                 162              45               3
4                     190                 190              45               3
5                     213                 213              45               3
6                     231                 231              45               3
7                     244                 231              58               4
8                     252                 231              66               4
```

The first fourth normal appears at the very first Y7 column

```text
X^0 Y^7 Z^2.
```

Its exact relation uses 4,549 old columns and 210 new face columns, with new
Y support `0..7`. Its boundary normal in `(Y,R,S,Z)` order is
`(48,22,8,91)` and pairs to `3 != 0` with the complete-image annihilator
`(1,74,26,77)`. Thus this is the missing class, not merely another relation.

The exact source receipt is frozen by SHA-256
`a5cbe957f07763dc4ab9c9d67ec11357ad1a6f9604e0544191febd69e3c72788`.

## Why Y7 is not an unexplained coincidence

For this small profile `(n,w,g,m)=(11,5,8,6)`, the number of raw face
columns with `0 <= y <= m` is

```text
sum_(y=0)^6 (m*g-w*y) = 231.
```

The universal bivariate Hermite cap is also

```text
n*m*(m+1)/2 = 231.
```

Equivalently, the profile was chosen on the exact ratio wall

```text
2*g-w=n.       (16-5=11)
```

Every one of the first 231 columns raises contact rank. The next column,
Y7Z2, is therefore precisely the first associated Hermite dependency. The
complete-old-cap strictness happens to lift this dependency and its boundary
normal escapes the old rank-three image.

## Decisive target mismatch

At target

```text
(n,w,g,m,U)=(262144,131071,180413,47,64),
2*g-w=229755 < 262144=n.
```

The raw face never reaches the universal Hermite cap, even after using every
allowed Y degree through U=64:

```text
raw face columns             278,534,035
bivariate Hermite row cap    295,698,432
deficit                       17,164,397
```

Therefore the finite Y7 event does **not** scale as a dimension-forced
target recurrence. A target-uniform raw-only theorem would need additional
special interpolation structure of the actual `(x_i,u1_i)` data, plus the
filtered strictness theorem which is already false generically in small
controls. The finite L9 repair remains a useful mechanism witness but is not
evidence that raw columns alone close target 6900.

## Reproduction

```text
python3 .experiments/k0_raw_passive_face_minimal_y_attribution_6900.py
```

uses literal rows `(epsilon,S,T,R,Z)` under
`Y=u0+u1Z+epsilon R-epsilon^2 S+epsilon^3 T` and the accepted graph boundary
`S=HasseDeriv 2 P`.

```text
canonical SHA-256  7afb09f05b45f2649523f51d5fb7206c3ed673f7e1a4f10700759a1e287ae5ec
script SHA-256     3d53285d6a193e43a9f77d9db7860f91404cdbf29ef502649166e77c8bd28009
runtime / peak RSS 35.570 s / 732,240 KiB
address-space cap  4.2 GB
```

