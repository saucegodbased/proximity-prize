# K0 formal-Hasse boundary correction and exact head/tail attribution

Date: 2026-09-15 UTC. Scope: finite exact `F_101` mechanism controls for
lower-6900. This is not a target-uniform theorem, candidate, or submission.

## Bottom line

The accepted second-jet specialization uses

```text
(Y,R,S,Z) = (P, P', Hasse_2(P), gamma) = (P, P', P''/2, gamma).
```

With this correction, the complete `m=6,L=8` source has boundary gain **3**,
not 4. The apparent fourth normal and `R^2` seam obtained with `S=P''` were
artifacts. The exact corrected result agrees with the old compressed-oracle
gain after its `V2=2*S` change of variables.

There is nevertheless a clean, useful projected-head result. Keeping formal
epsilon orders at least 3 makes the boundary map on the contact kernel
surjective (gain 4). Adding epsilon orders 2 and 1 preserves gain 4. Only
adding epsilon order 0 reduces it to the complete gain 3. Thus the unique
head-to-complete connecting obstruction is supported at ordinary epsilon
order zero; a three-coordinate terminal producer is more than this finite
chamber needs.

## Formal contact and boundary conventions

Both new scripts use literal rows in order `(eps,S,T,R,Z)` and substitute

```text
Y = u0 + u1*Z + eps*R - eps^2*S + eps^3*T  (mod eps^m).
```

Boundary vectors are reported in order `(Y,R,S,Z)`. Primitive assertions
check that raw `Y,R,S,Z` map to the expected contact rows and boundary axes.
No compressed `E` oracle is used.

## Complete-contact `R^2` attribution

Script: `k0_literal_r2_first_dependency_6900.py`.

Frozen profile and source-family order:

```text
(n,w,g,m,B,s,U,L,k,n0) = (11,5,8,6,2,1,8,8,0,1)
raw / R / S / R^2 columns = 1560 / 1164 / 1200 / 840
```

The raw+R+S prefix is contact-injective. Adding `R^2` gives:

```text
complete contact rank / nullity / boundary gain = 4719 / 45 / 3
R^2 relative rank / kernel                     = 795 / 45
```

The first dependency occurs at `R^2` column 739, monomial
`X^23 Y^3 R^2 Z^3`, and gives normal `(13,27,26,32)`. Its candidate-graph
specialization is identically zero, and the independent chain-rule check is

```text
partial-X 61 + boundary-gradient dot graph-tangent 40 = 0 mod 101.
```

By completed `R^2` Y-degree the `(rank,nullity,gain)` evolution is:

```text
Y<=0  (4204, 0, 0)     Y<=1  (4414, 0, 0)
Y<=2  (4564, 0, 0)     Y<=3  (4663, 1, 1)
Y<=4  (4697,27, 3)     Y<=5  (4719,35, 3)
Y<=6  (4719,45, 3)
```

Replay receipt:

```text
canonical SHA256  2a642ab694fdf7d3726b687e2bf5b421d447ba6519b3da98e2b6b7d518452c08
script SHA256     d0f09bc6aa62fe21e434bdd82a787dc775b477e93cbc0b80112fdb278d84d72c
runtime           33.112 s
peak RSS          681268 KiB
address cap       4200000000 bytes
```

## Nested head/tail and family attribution

Script: `k0_literal_hasse_head_family_attribution_6900.py`. It uses the same
profile and source order, then projects to rows of epsilon order at least
`q_min`:

```text
q_min   rows   contact rank   nullity   boundary gain
  3     4455       3663         1101          4
  2     5148       4015          749          4
  1     5643       4367          397          4
  0     5995       4719           45          3
```

At `q_min=3`, cumulative family stages are:

```text
family prefix   columns   rank   nullity   gain
raw               1560    1397      163      2
+R                2724    2266      458      3
+S                3924    3179      745      4
+R^2              4764    3663     1101      4
```

The fourth head direction is introduced by the raw `S` monomial itself. Its
epsilon-at-least-3 trace is zero, its boundary is the pure S axis
`(0,0,1,0)`, and its discarded trace consists of exactly one epsilon-zero row
at each of the 11 nodes. This explains the mechanism without pretending it
is already a complete-contact solution.

An exact basis for the complete kernel's boundary image is

```text
(1,72,2,18), (0,1,8,37), (0,0,1,60),
```

and an annihilating covector is

```text
ell = (1,74,26,77).
```

This isolates a one-dimensional quotient between the four-dimensional head
image and the three-dimensional complete image. The nested ranks prove that
epsilon orders 1 and 2 do not impose this quotient condition; epsilon order
0 does.

Replay receipt:

```text
canonical SHA256  be990937c4b0ec3e82d3dcef40e58e7cf67e582b888798b4290c7a422e9dd7c9
script SHA256     becf26417d3016075bb0ca2c77d5d154d49f9730ad70b0054cf1fa8d6b1a91e5
runtime           67.888 s
peak RSS          810744 KiB
address cap       4200000000 bytes
```

## Withdrawn result and retained theorem

The numerical detector in commit `11e1c94` is withdrawn. It selected the
compressed outer exponent `q` as epsilon order, although the formal row
correspondence sends `(q,E^b,...)` to epsilon order `q+3*b`. It also used the
ordinary boundary point `S=P''`. Its claimed last-three numerical detector
must not be cited.

The abstract Lean file `K0TerminalDualDetection6900.lean` remains sound and
useful. It proves basis-free implications from a stated head-kernel
surjectivity hypothesis and does not depend on the bad numerical oracle.

## Process lesson and next gate

Every contact-rank experiment must audit the pair `(contact,boundary)`, not
contact alone. A row isomorphism does not transfer boundary gains unless the
source scaling and boundary specialization commute. Primitive-axis checks,
candidate specialization, and the full chain rule are now mandatory guards.

The exact L9 repair reported independently uses only the 252 newly legal raw
positive-Z columns on top of L8 and raises complete gain from 3 to 4. The next
high-value task is therefore the minimal raw-face epsilon-zero recurrence,
not further tuning of the RED centered/C3 carrier family.
