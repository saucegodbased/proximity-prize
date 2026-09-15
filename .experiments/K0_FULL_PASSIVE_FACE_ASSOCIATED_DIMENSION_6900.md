# k0 complete successor face: associated surplus and the strictness gap

Date: 2026-09-15 UTC. Scope: lower 6900, exact arithmetic and literal formal
contact. This changes no production candidate, score, or claim.

## Verdict

The **complete** target cap-3757 face over cap 3756 has a target-scale associated
dimension surplus:

```text
new face source coefficients             17,434,693,359
one-node associated/local rank cap               66,420
all-node associated/local rank cap        17,411,604,480
associated dimension surplus                  23,088,879
```

This reverses the raw-only verdict. The raw `S=R=0` face has 278,534,035
columns and is short of its bivariate-Hermite cap by 17,164,397. The other
derivative shapes are therefore genuinely load-bearing.

The result is **GREEN as exact associated-grade arithmetic, conditional on
the filtration-compatible local rank-cap theorem; OPEN as a complete-contact
producer**. Separate full-rank bounds at cap 3756 and cap 3757 do not imply a
bound on their rank increment. Even after that nesting theorem is supplied,
an associated relation only kills the top passive grade. It still has to be
corrected through every lower passive grade by the old source, and its
boundary must escape the old rank-three normal image.

## Literal associated identity

Use the actual formal flattened contact

```text
Y -> u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

For a complete face monomial

```text
X^a S^s Y^y R^r Z^z,        s+y+r+z = 3757,
```

the unique top-passive-degree contact term is

```text
(x+epsilon)^a S^s
  (u1 Z + epsilon R - epsilon^2 S + epsilon^3 T)^y
  R^r Z^z.
```

Every term containing at least one `u0` has smaller passive degree. This
identity is proved, with the `T` term present and the accepted Hasse `S`
normalization unchanged, in
`K0FullPassiveFaceAssociatedDimension6900.lean`.

The same file proves source legality on the cap-3757 face, the exact ledger
subtractions, and the rank-nullity implication

```text
rank(associated face) <= 17,411,604,480
  ==> dim ker(associated face) >= 23,088,879.
```

The rank premise is intentionally explicit rather than silently inferred
from two unrelated upper bounds.

## Direct source and local-cap enumeration

The global face count is the direct sum over every legal raw `(S,R,Y)` shape:

```text
sum_{s=0}^8 sum_{r=0}^{16-2s} sum_{y=0}^{64-s-r}
  [47*180413 - (131071-2)s - (131071-1)r - 131071y].
```

Split by raw `S` exponent, its exact values are:

```text
s      global face columns
0       3,671,014,323
1       3,233,888,380
2       2,798,728,244
3       2,365,271,777
4       1,933,256,841
5       1,502,421,298
6       1,072,503,010
7         643,239,839
8         214,369,647
total  17,434,693,359
```

Independently enumerating the new passive-coordinate slope in the accepted
relaxed local source and in its explicit `U/J/V` weighted-kernel family gives:

```text
h      local source slope   known-kernel slope   local rank cap
0                  19,176                7,252           11,924
1                  16,920                5,789           11,131
2                  14,664                4,437           10,227
3                  12,408                3,220            9,188
4                  10,152                2,162            7,990
5                   7,896                1,287            6,609
6                   5,640                  619            5,021
7                   3,384                  182            3,202
8                   1,128                    0            1,128
total              91,368               24,948           66,420
```

These totals independently equal the differences of the accepted closed
source/rank formulas at 3757 and 3756.

The structural reason the local-cap bridge should be true is stronger than
mere subtraction: each weighted `U/J/V` generator is homogeneous in total
passive degree, and multiplication by its passive `Z` parameter advances it
one layer. What is still needed for a theorem-grade use of 66,420 is the
literal associated-face restriction/injectivity proof for those 24,948 new
generators. Until that is compiled, 66,420 is not being advertised as an
unconditional rank-increment theorem.

## Exact corrected control

For the formal-contact `F_101` m6 control with

```text
(n,g,m,w,B,s,U,Lold,Lnew)=(11,8,6,5,2,1,8,8,9),
```

the analogous numbers are:

```text
complete face columns                 859
one-node associated cap                66
all-node associated cap               726
associated surplus                    133

observed complete contact rank     4719 -> 5445   (+726)
observed complete kernel dim         45 -> 178     (+133)
```

Thus the small corrected formal model saturates the associated cap and every
dimension-forced associated relation does lift to a complete attached
relation there. This is excellent mechanism evidence, but it is not a
target-uniform strictness theorem. The earlier minimal attribution further
shows that the fourth boundary direction first appears already when the raw
`Y^7 Z^2` column is attached; the full face has much more kernel than is
needed to create that one boundary direction.

## Exact remaining logical chain

To turn this into the 6900 producer, three statements must stay separate:

1. **Associated cap:** prove the complete new-face associated map has rank at
   most `262144*66420` using the homogeneous nested weighted-kernel family.
2. **Strictness/liftability:** show that some associated-kernel class can be
   corrected by cap-3756 columns through all lower passive grades, i.e. lies
   in the `liftableFace` space for complete contact.
3. **Boundary separation:** show one such lift pairs nontrivially with the
   one-dimensional annihilator of the old rank-three normal image.

Dimension settles only item 1 after its filtration-compatible identification.
It cannot settle items 2 or 3: a 23-million-dimensional space may map to zero
under four boundary coordinates.

## Reproduction

```bash
python3 .experiments/k0_full_passive_face_associated_dimension_6900.py
.experiments/run_lean_4g_capped.sh \
  /absolute/path/.experiments/K0FullPassiveFaceAssociatedDimension6900.lean
```

The Python gate uses exact integers and no finite-field matrix. The Lean file
compiles at `-j1 -M3500`; printed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `decide`, `native_decide`,
`sorry`, or `admit`.

```text
canonical result SHA-256  2d56ebdf44c09e8c38ccb9ae33342939fb17dd7fc1059fd2084eddb6a40a0028
script SHA-256            9130c031475c920f2688d01c3dace9ad8a32414202b0c941306e048d159bfc97
```
