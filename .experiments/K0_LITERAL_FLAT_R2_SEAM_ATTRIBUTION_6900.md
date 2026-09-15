# k0 literal flattened derivative attribution: every first kernel is born at R²

Date: 2026-09-15 UTC. Scope: exact finite mechanism discriminator for the
lower-6900 k0 route. This changes no production candidate or submission.

## Verdict

On the corrected formal-contact `F_101` m6, L8 receipt, the complete raw
source was ordered by derivative shape

```text
(R power,S power) = (0,0), (1,0), (0,1), (2,0).
```

The first three groups together are injective. Appending the `R²` group
creates all 45 kernel dimensions and all four boundary directions at once:

```text
admitted groups       columns   contact rank   nullity   augmented   gain
raw                       1560           1560         0        1560      0
raw + R                   2724           2724         0        2724      0
raw + R + S               3924           3924         0        3924      0
raw + R + S + R²          4764           4719        45        4723      4
```

Equivalently, the 840-column `R²` block has contact quotient rank 795 modulo
the complete `{raw,R,S}` prefix, relative kernel dimension 45, and relative
boundary gain four. In this corrected control the causal attachment is the
`R²` osculating seam, not an extra passive-Z layer and not a raw centered-Y
witness.

## Exact semantics and receipt

The contact rows are literal `(epsilon,S,T,R,Z)` monomials under

```text
Y -> u0 + u1*Z + epsilon*R - epsilon^2*S + epsilon^3*T
```

modulo `epsilon^6`. The four appended graph-boundary rows are evaluated at
`(Y,R,S,Z)=(P,P',P'',gamma)`, in script order `(Y,R,S,Z)`. Thus the result
uses the same curvature normalization on both sides of the augmented map.

Frozen data:

```text
field F_101
(n,w,g,m,B,s,U,L,k,n0)=(11,5,8,6,2,1,8,8,0,1)
agreement={0,2,3,5,6,7,8,9}
candidate degree=2
agreement-direction interpolant degree=6>w
full contact matrix=5995 x 4764
```

Exact replay under a 4 GiB address-space cap:

```text
canonical SHA-256  78a4187c57c99260cef6fce987b5d0d8f720e7d7861fb3328a47491d402f9202
script SHA-256     e3d5e28d17419482389acbf2d870c483d936fa680101774e65d9031eabea39c9
runtime            44.963 s
peak RSS           1,031,744 KiB
```

The driver performs one exact contact RREF and one augmented RREF. Prefix
ranks are obtained by counting pivot columns in the declared group order, so
there is no separately rounded or randomized rank estimate.

## What this proves and what it does not

Because the entire `{raw,R,S}` union is injective, every complete contact
relation in this receipt necessarily has nonzero `R²` support. This makes a
specific target theorem falsifiable: understand the quotient contact map of
the first quadratic-slope block and its boundary connecting map.

The result does not say that `R²` alone spans the correction or that this
particular four-group order is canonical. It also does not transport the
finite ranks to `(m,B,s,U,L)=(47,16,8,64,3757)`. At target scale there are
many higher derivative shapes, and a proof must show either that they are
capacity scaffolding for this low seam or extend the same recurrence through
them.

The immediately relevant symbolic object is the locator/value/slope second
covariant. With formal curvature convention `-epsilon²*S`, the correct
curvature residual begins with

```text
2*S - P'' - (Z-gamma)Q'',
```

not `S-P''-(Z-gamma)Q''`. The axiom-clean identities in
`K0OsculatingHeadCompanion6900.lean` show that the first covariant starts in
epsilon order two and the corrected second covariant in order three. The
next gate is to connect those identities to the literal `R²` quotient while
respecting every target X window.
