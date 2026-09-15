# k0 literal flattened strong-cap replay: Hasse-boundary correction

Date: 2026-09-15 UTC. Scope: exact finite discriminator for the lower-6900
k0 route. This changes no production candidate, score, or submission.

## Verdict

This note supersedes the first version committed in `ae57cb7`. That version
incorrectly evaluated the formal `S` graph coordinate at the ordinary second
derivative `P''`. The accepted second-jet specialization uses the second
Hasse derivative `HasseDeriv 2 P = P''/2`. Replaying the frozen receipt with
that coordinate gives:

```text
profile                                  contact rank/nullity   boundary gain
L=7 complete (margin -88)                     3905 / 0               0
L=7 eps>=3 head                              3069 / 836               4
L=8 complete (margin +45)                    4719 / 45                3
L=8 eps>=3 head                              3663 / 1101              4
```

Thus the correctly weighted head has all four boundary directions already at
`L=7`, but those relations do not lift through terminal epsilon orders
`0,1,2`. At the first positive-margin cap `L=8`, the complete contact kernel
appears with only three boundary directions. This agrees with the old
compressed complete-map calculation. The surviving useful signal is the
rank-four head together with a one-dimensional loss while lifting through the
terminal rows; it is not yet a mechanism that repairs that loss.

This is evidence for where a fourth direction is lost, not evidence that the
complete target map has rank four. It does not prove the target-uniform
theorem.

## 1. Literal map used

The source monomials are `(X,Y,R,S,Z)` and the local rows are
`(epsilon,S,T,R,Z)`. At every node the exact substitution is

```text
X -> x + epsilon
Y -> u0 + u1*Z + epsilon*R - epsilon^2*S + epsilon^3*T
R -> R
S -> S
Z -> Z
```

followed by truncation modulo `epsilon^m`. This is the formula proved in
`K0MinimalRawContactFormula6900.lean` and used by the typed accepted-source
map in `K0WeightedRawAdjointRecurrence6900.lean`. The driver imports the
literal expander committed in `500c732`; it does not call
`translated_column(k=2)`.

The boundary rows evaluate the four raw partial derivatives at
`(Y,R,S,Z)=(P,P',HasseDeriv 2 P,gamma)` and `X=n`, in script order
`(Y,R,S,Z)`.

## 2. Why the corrected complete augmented rank agrees with the old oracle

The older compressed oracle is not arbitrary. Its row

```text
(outer=q, E-power=b, R-power=r, Sdiv-power=s, Z-power=z)
```

embeds into the formal flattened row

```text
(outer=q+3*b, S-power=s, T-power=b, R-power=r, Z-power=z).
```

The compressed truncation `q+3*b<m` is exactly the formal outer truncation.
The coordinate transport is `E -> epsilon^3*T` and `Sdiv -> 2*S`; every raw
source column is then scaled by the nonzero factor `2^(S power)`. At the
correct formal graph point `S=P''/2`, the boundary rows transport under the
same invertible scaling (the `S` gradient row differs by one global nonzero
factor). Consequently both the complete contact rank `4719` and augmented
rank `4722` agree with the compressed oracle.

Likewise, a projected-head test in compressed coordinates must select rows by
the formal order `q+3*b`, not by `q` alone. The present replay avoids this
ambiguity by materializing the formal flattened rows and selecting their
literal epsilon exponent.

## 3. Exact receipt

The frozen data are

```text
F_101
(n,w,g,m,B,s,U)=(11,5,8,6,2,1,8)
agreement set={0,2,3,5,6,7,8,9}
candidate degree=2
agreement-direction interpolant degree=6>w
```

The dense exact matrices were reduced in place by FLINT under an external
4 GiB address-space cap. The combined `L=7,8`, complete/head run reports:

```text
canonical SHA-256  e8ceacd8af5b615cdfcce000e9f7ce80a3afa7f3e354f5a7b5a238f7b833fdff
script SHA-256     aec4717ee855f72a9462c99f51e1de5807c48268509ad15a10825da065b5b812
runtime            85.856 s
peak RSS           1,032,652 KiB
```

The complete `L=8` contact matrix has `5995 x 4764` entries and exact rank
`4719`; appending the four boundary rows raises rank to `4722`. The head
matrix has `4455 x 4764` entries and ranks `3663/3667` before/after the same
boundary rows.

## 4. Consequence for the live proof search

The corrected finite architecture is now:

```text
head boundary directions exist before the first full kernel
  -> terminal orders prevent those relations from lifting at L=7
  -> the first positive complete cap L=8 has a 45-dimensional kernel
  -> its complete boundary image still has rank only three.
```

The old complete-map rank-three obstruction survives this control. The useful
questions are now sharper:

1. whether the corrected literal result is robust across all prior data
   families and target-ratio controls;
2. which small raw family produces the fourth head direction;
3. exactly which terminal row kills it, and whether another legal source
   layer can repair that connecting obstruction; and
4. whether such a mechanism admits a target-uniform proof at the first
   positive cap `L=3757` (or the conservative `L=3758` profile).

Until those are proved, this replay is evidence and a process correction,
not a 6900 candidate.
