# k=0 degree-four truncated-cap process critic

Date: 2026-09-14 UTC. Scope: lower-6900 finite mechanism audit only. This
note changes no production source, score, claim, or submission.

## Correct verdict

The new degree-four gain-three result is a genuine exact function-field
result, but it is **not a target-faithful counterexample** to the current k=0
full-source theorem. The tested profile silently truncates the active source
before the target's terminal face:

```text
profile                         n  w  g  m  B  s   U    L  effective active cap
previous full-source GREEN      8  3  5  8  3  1  12   16        12
new degree-four RED             9  3  6  8  3  1  12   10        10
target, original curvature      -  -  - 47 16  8  64 3757        64
target, reduced curvature       -  -  - 47 16  6  64 5107        64
```

The literal source inequalities include both

```text
y + r + h <= U,
y + r + h + z <= L.
```

Since `z >= 0`, their effective active cap is `min(U,L)`. Thus the RED
profile does not merely have fewer passive shifts. It removes every active
shape of total degree 11 or 12, despite displaying `U=12` in its parameter
tuple. Positive source margin does not restore a missing graded face.

The exact RED remains useful. For

```text
(n,w,g,m,B,s,U,L) = (9,3,6,8,3,1,12,10),
P degree 3, Q=X^4, exact maximal agreement 6,
```

the full source has 11,178 columns, published local bound 1,207, and margin
`11178-9*1207=315`, but contact rank is 10,861, nullity is 317, and boundary
gain is only three. The unique compatible boundary line at `X=9` is the
tangent jet `(Q,Q',Q'',1)`. Independent replay at `X=9,10,11` still has gain
three, and every one of the 317 exact tangent-contraction polynomials is
identically zero. This is not an unlucky boundary specialization.

What it falsifies is the weaker claim

> positive aggregate source margin plus a bad tangent is enough for four
> boundary normals, independently of which support facets are populated.

That claim is false. It does not falsify a theorem specialized to the actual
target box.

## The omitted target face

The target-style arithmetic deliberately sets

```text
U - B = m + 1,
```

so `U=B+m+1`. On the simultaneous active and derivative faces, for curvature
exponent `h`, the terminal shapes are

```text
r = B - 2h,
y = m + 1 + h,
h + r + y = B + m + 1 = U.
```

For the m8 control these include

```text
(y,r,h,z) = (9,3,0,0), (10,1,1,0).
```

They have 15 legal X coefficients each. Both are absent at `L=10` and
`L=11`, and first become legal at `L=12`. More generally the whole active
degree-12 face is absent at `L<12`: it has 83 columns at `L=12`, including
the 30-column simultaneous top shell above. The formal target artifact
`K0TopShellAdjointSeed6900.lean` isolates exactly the analogous m47 shell.
The controlled cap ladder below shows that this face is target-faithful but
not necessary for the finite receipt: `L=11` already restores rank four.

The previous GREEN control has `L=16>=U=12`, so it contains the complete
active box. Both target profiles have `L` thousands larger than `U=64` and
contain the shell with a large passive window. The new RED therefore changed
two mathematically material axes at once: it increased the agreement-Newton
dimension from `g-w-1=1` to 2, and it cut the effective active cap from 12 to
10. Receipt data also changed. Those confounds prevent attributing the lost
normal to the extra Newton slot.

## Resolved cap ladder and route decision

**PIVOT away from interpreting the L=10 result as a RED for target k=0.** Do
not use it to reject the full-source route, and do not label the profile
target-gated merely because its dimension margin and the displayed equality
`U-B=m+1` are positive.

**GO conditionally on the passive-layer/full-source route, not specifically
on the terminal shell.** The same frozen degree-four receipt gives:

```text
L    columns   contact rank/nullity   boundary gain
10    11,178       10,861 / 317             3
11    13,139       12,321 / 818             4
12    15,183       13,779 / 1,404           4
```

The L11 source still omits the complete active-12 face, yet it already reaches
four: gains 1--3 first arise in the `R^2` stage and gain 4 in `R^3`; the final
`S R` group is unnecessary. At L12, gains 1--2 arise in raw `R` and gains
3--4 in raw `S`, before `R^2`. Thus one additional passive layer repairs the
L10 obstruction, while the terminal top shell is not the causal minimum.

A disjoint ablation resolves the cause more sharply. Adding only the 101 new
active-11, seed-zero columns to L10 leaves gain three, while adding only the
other 1,860 passive-reach columns gives rank 12,321 and gain four, exactly the
full L11 contact rank and normal gain. The new active face is neither
sufficient nor necessary; passive reach is sufficient.

The degree-five replay at L10 also reaches gain four. Together the results
show that both tangent degree and passive support matter, but falsify a naive
need for passive seed depth `deg Q`: degree-four badness closes already at
L11 with first normal-producing passive seeds at most two.

This remains a route decision, not the universal m47 confluence theorem. The
target proof must construct rank-adaptive relative repairs from its literal
tapered passive connection. Do not promote any first pivot in the explicit
finite ordering to a standalone four-monomial identity.

## Permanent process gate

Never call a finite profile "target-faithful" from a parameter tuple and a
positive dimension margin alone. Before promoting a finite GREEN or RED,
audit every intersecting inequality facet on the actual index set, including:

1. effective caps induced by other nonnegative coordinates, especially
   `active <= min(U,L)`;
2. nonemptiness and widths of the exact terminal/critical faces used by the
   proposed recurrence;
3. target equalities such as `U-B=m+1` after all other caps are applied;
4. exact maximal agreement and retained badness;
5. function-field, rather than single-specialization, boundary rank; and
6. characteristic-sensitive identities when transporting from a toy field.

A margin proves existence of some contact kernel. It says nothing about
whether that kernel reaches the graded boundary coordinate needed by the
consumer.
