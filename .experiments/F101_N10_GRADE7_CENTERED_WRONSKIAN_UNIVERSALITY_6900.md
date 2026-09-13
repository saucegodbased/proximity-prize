# F101 matched `n=10` grade-seven centered-shell replay

Scope: the two predeclared `n=10` cases in
`f101_o2_bordered_filtration_mechanism_6900.py`, with no parameter search.
For each literal case the calculation retains precisely source monomials of
boundary grade at most `J+1=7`, takes the all-node contact kernel, and solves
the first three actual `J` right hand sides.  The fourth normal of the
`L=J+m` case is deliberately out of scope.

The executable receipt is
`f101_n10_grade7_centered_wronskian_universality_6900.py`.  It was run under
`prlimit --as=4294967296`; its output's canonical SHA-256 is
`b982270e2b4dff7307bcb27c710618f2caa8fd853b624d443dd11cd79f60d6c5`, and
the script SHA-256 at that run is
`52a7c7eb64a4ff4fd1ab922d859b774a7964df4e27cc430b6649401bd0ecf350`.

## Literal restricted solve

Both chambers have the same first-three-RHS data:

| chamber | source columns of grade `<=7` | contact rank, nullity | `J` rank on contact kernel |
|---|---:|---:|---:|
| `L=J+m-1=9` | 1649 | `(1590,59)` | 12 |
| `L=J+m=10` | 1649 | `(1590,59)` | 12 |

Here

```text
Xi = 1 + 90 X + 77 X^2 + X^3,
Q = Xi^2 = 1 + 79 X + 73 X^2 + 25 X^3 + 49 X^4 + 53 X^5 + X^6,
Lambda = 13 X + 54 X^2 + 8 X^3 + 73 X^4 + 74 X^5 + 80 X^6 + X^7.
```

Put `V=Y-QZ`, `V1=R-Q'Z`, and `V2=S-Q''Z`.  For every one of the six
solves, exact triangular reconstruction finds no `V2` term at all and gives

```text
V^2 Z^3 ( c V^2 + C Lambda V Z + A Xi (Lambda V1-Lambda' V) Z ).
```

Thus the only centered carriers are `V^4Z^3`, `V^3Z^4`, and `V^2V1Z^4`.
In this matched `n=10` replay the first one degenerates: `c=0`; it is not a
missing fourth carrier.  In raw coordinates the only nonzero shapes are
`Z^7, RZ^6, YZ^6, YRZ^5, Y^2Z^5, Y^2RZ^4, Y^3Z^4`.  In particular there is
no raw `S` shape and no `Y^4Z^3` shape.

The Wronskian test is an exact identity in every solve:

```text
B + A Xi Lambda' = Lambda C,
B0 = B - c Q + 2 A Lambda Xi',
[Z^7] = B0 (-Q)^(m-1), with m=4.
```

## Exact coefficient receipt over `F_101`

The coefficient degrees are uniform versus `e=deg Xi=3`:
`deg A=0`, `deg C=2`, `c=0`, and `deg B0=9=3e`.  The common irreducible
quadratic factor of `C` is `X^2+85X+30`; the displayed constants distinguish
the three literal RHS.

| RHS | `A` | `C` | restricted source support | source SHA-256 |
|---|---:|---|---:|---|
| `F0` | `90` | `33(X^2+85X+30)` | 1351 | `04536fb92144296f2a8e828f02f2d9cba99cb94233eeaad8aee83ad7a4e73cba` |
| `F1` | `35` | `97(X^2+85X+30)` | 1371 | `82f8ea56d7e1644e3ca0858c67a56ed8d80e19d926da538b02bd4c834285d6da` |
| `F2` | `68` | `99(X^2+85X+30)` | 1388 | `8f05fa316b6d4aae09177f015bcd6bb31271581f2bfebf15be589645b1034f8c` |

For a compact factor cross-check, the three `B` polynomials are respectively
`9`, `54`, and `27` times

```text
(X+34)(X+46)(X+58)(X^2+92X+29)
*(X^4+83X^3+47X^2+3X+36),
```

and the three `B0` polynomials are respectively `44`, `62`, and `31` times

```text
(X+4)(X+17)(X+78)
*(X^6+32X^5+44X^4+97X^3+70X^2+90X+19).
```

This is a bounded exact universality receipt only.  It does not assert that
these degree bounds or the factor pattern extend beyond the two fixed
chambers.
