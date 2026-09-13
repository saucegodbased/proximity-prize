# F101 `n=10` arbitrary-error-direction grade-seven countergate

This is the single predeclared chamber with error-direction offsets
`(3,5,7)` at nodes `7,8,9`, from
`f101_o2_arbitrary_error_offset_shell_gate_6900.py`.  It retains the literal
all-node contact map and the first three polynomial-normal RHS; it is not a
new chamber search.  The exact calculation is implemented in
`f101_n10_error_offset_grade7_centered_falsifier_6900.py` and was run under
`prlimit --as=4294967296`.

The output canonical SHA-256 is
`07cc6d7e3a8cb7e50a0b6f4ec96acb9c29c03cfc166d5d8b6a84c8af4a186aa3`; the
script SHA-256 at that run is
`ac396db84f0c12c9c37ea308c429998c60b1ef08100de8b2cad60bd9e39405fd`.

## Exact bordered gate

For the fixed parameters `(n,w,g,m,D,s,t,J,L)=(10,4,7,4,28,1,1,6,10)`, the
source cap `grade <= J+1=7` has 1649 columns.  Its all-node contact matrix
has rank/nullity `(1590,59)`, and the exact `J` image on that kernel has rank
12.  Each of `F0,F1,F2` is solved exactly at this cap.  Their source supports
and hashes are:

| RHS | support | SHA-256 |
|---|---:|---|
| `F0` | 1383 | `c768dac5462f4071a9694d5550afe57ca88747ac54e05af7eef016b801709098` |
| `F1` | 1398 | `165dfb6453e9054720dbb03679567e2d1f8ecdad3d5775c0fc5e2aeb42865182` |
| `F2` | 1417 | `4f712ae115eafb272e11b911c3fbd96fd1e5bd591ad06ce183054435a408ff55` |

All three sources have precisely the familiar eight raw grade-seven shapes:
`Z^7, RZ^6, YZ^6, YRZ^5, Y^2Z^5, Y^2RZ^4, Y^3Z^4, Y^4Z^3`.  Thus the failure
below is not caused by a new raw `S` shape or a source-cap mismatch.

## Centered failure localized exactly

Let `V=Y-QZ`, `V1=R-Q'Z`, and `V2=S-Q''Z`, with the same `Q=Xi^2` and
`Lambda` as the matched chamber.  Write the grade-seven `R` part as

```text
T0 R Z^6 + T1 R V Z^5 + T2 R V^2 Z^4
```

and the pure part as `sum(Hk V^k Z^(7-k), k=0..4)`.  The two partial
congruences do survive:

```text
T2 = A Lambda Xi,
H3 + A Xi Lambda' = Lambda C.
```

For `F0`, for example,

```text
A = 64 (X+47)^2 (X+75)^2,
C = 29 (X+47)(X+75)(X+100)
    *(X^4+55X^3+83X^2+16X+46).
```

But the required three-carrier zeroes are all nonzero for every one of
`F0,F1,F2`:

```text
T0 != 0,  T1 != 0,  H0 != 0,  H1 != 0,
H2 + 2 A Lambda Xi^2 Xi' != 0.
```

Their factor cores are common across the three RHS (only the leading scalar
changes).  For `F0` those scalars are respectively `64,27,83,29,94`, and the
five factor cores are

```text
T0: (X+92)(X+93)(X+94)(X+69)^2 X^3 product_{a=95..100}(X+a)^3
T1: (X+47)(X+69)(X+75)(X+92)(X+93)(X+94) X^2 product_{a=95..100}(X+a)^2
H0: (X+74)(X+69)^2 X^3 product_{a=95..100}(X+a)^3
    *(X^8+98X^7+35X^6+26X^5+37X^4+90X^3+5X^2+77X+96)
H1: (X+69)(X+87) X^2 product_{a=95..100}(X+a)^2
    *(X^10+67X^9+41X^7+14X^6+17X^5+57X^4+66X^3+14X^2+63X+61)
H2 residual: X(X+78) product_{a=95..100}(X+a)
    *(X^4+17X^3+49X^2+8X+69)
    *(X^8+15X^7+28X^6+11X^5+12X^4+58X^3+66X^2+94X+8).
```

Finally, setting `c=H4`, `B=H3`, and
`B0=B-cQ+2A Lambda Xi'` does **not** restore the old boundary relation:

```text
Z^7 coefficient - B0(-Q)^3 != 0.
```

For `F0` its nonzero remainder has degree 32 and begins with the factor core

```text
X(X+9) product_{a=95..100}(X+a)(X^2+98X+4)
*(X^5+23X^4+75X^3+72X^2+76X+92)
```

times the degree-17 factor recorded verbatim by the executable receipt.
This falsifies the centered three-carrier / `B0` form in the prescribed
non-Q error-direction chamber, while preserving the narrower `Lambda`
divisibilities above.
