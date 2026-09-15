# k0 literal flattened strong-cap replay: the first kernel is already rank four

Date: 2026-09-15 UTC. Scope: exact finite discriminator for the lower-6900
k0 route. This changes no production candidate, score, or submission.

## Verdict

The former `L=8` rank-three / `L=9` rank-four passive-repair story was an
artifact of pairing the compressed second-jet contact matrix with the wrong
curvature normalization in the boundary map. Replaying the same frozen
receipt against the literal formal contact and literal graph boundary gives:

```text
profile                                  contact rank/nullity   boundary gain
L=7 complete (margin -88)                     3905 / 0               0
L=7 eps>=3 head                              3069 / 836               4
L=8 complete (margin +45)                    4719 / 45                4
L=8 eps>=3 head                              3663 / 1101              4
```

Thus the head already has all four boundary directions at `L=7`, but its
relations do not lift through the terminal ordinary epsilon orders `0,1,2`.
At the first positive-margin cap `L=8`, the complete contact kernel appears
and its boundary image is immediately rank four. There is no rank-three
complete kernel for a later passive layer to repair in this receipt.

This is positive evidence for the desired rank-four conclusion and negative
evidence for the claimed one-spare-layer mechanism. It does not prove the
target-uniform theorem.

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
`(Y,R,S,Z)=(P,P',P'',gamma)` and `X=n`, in script order `(Y,R,S,Z)`.

## 2. Why complete contact rank survived but boundary gain did not

The older compressed oracle is not arbitrary. Its row

```text
(outer=q, E-power=b, R-power=r, Sdiv-power=s, Z-power=z)
```

embeds into the formal flattened row

```text
(outer=q+3*b, S-power=s, T-power=b, R-power=r, Z-power=z).
```

The compressed truncation `q+3*b<m` is exactly the formal outer truncation,
and the divided-power curvature difference is an invertible row/source
scaling over `F_101`. This explains why the complete contact rank remains
`4719` in both calculations.

That scaling does **not** preserve the joint `(contact,boundary)` matrix used
in the old receipt. The old boundary evaluator fixes the raw curvature value
at `P''`; transporting the contact coordinate by `Sdiv=2*S` would also have
to transport the graph point and the raw source coordinates. Merely reusing
the old gradient rows is not a conjugacy. On the identical receipt the old
calculation reported gain three, while the literal paired calculation gives
gain four.

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
canonical SHA-256  bb78efe7098d6536dd934d0a89d4dca7fe142da1c0a03243c85369040cf27f9a
script SHA-256     af6733bbd3519546a0f13a393de2865be04d7c5481eb3ee754fddacace34ae57
runtime            87.107 s
peak RSS           1,032,652 KiB
```

The complete `L=8` contact matrix has `5995 x 4764` entries and exact rank
`4719`; appending the four boundary rows raises rank to `4723`. The head
matrix has `4455 x 4764` entries and ranks `3663/3667` before/after the same
boundary rows.

## 4. Consequence for the live proof search

The corrected finite architecture is now:

```text
head boundary directions exist before the first full kernel
  -> terminal orders prevent those relations from lifting at L=7
  -> the first positive complete cap L=8 has a 45-dimensional kernel
  -> its complete boundary image is already rank four.
```

The old `L+1` passive connecting-map producer is therefore not supported by
this control. The useful surviving questions are:

1. whether the corrected literal result is robust across all prior data
   families and target-ratio controls;
2. which small raw family produces the head Y direction;
3. which terminal lifting recurrence converts it into the first complete
   kernel; and
4. whether those two mechanisms admit a target-uniform proof at the first
   positive cap `L=3757` (or the conservative `L=3758` profile).

Until those are proved, this replay is evidence and a process correction,
not a 6900 candidate.
