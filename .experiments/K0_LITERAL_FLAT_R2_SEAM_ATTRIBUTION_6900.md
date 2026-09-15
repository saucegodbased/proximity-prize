# k0 literal flattened derivative attribution: R² creates the kernel, not rank four

Date: 2026-09-15 UTC. Scope: exact finite mechanism discriminator for the
lower-6900 k0 route. This changes no production candidate or submission.

## Verdict

This note supersedes the first version committed in `1ffa602`, whose boundary
evaluation used `S=P''` instead of the accepted formal coordinate
`S=HasseDeriv 2 P=P''/2`. On the corrected formal-contact `F_101` m6, L8
receipt, the complete raw
source was ordered by derivative shape

```text
(R power,S power) = (0,0), (1,0), (0,1), (2,0).
```

The first three groups together are injective. Appending the `R²` group
creates all 45 kernel dimensions, but their boundary image has rank only
three:

```text
admitted groups       columns   contact rank   nullity   augmented   gain
raw                       1560           1560         0        1560      0
raw + R                   2724           2724         0        2724      0
raw + R + S               3924           3924         0        3924      0
raw + R + S + R²          4764           4719        45        4722      3
```

Equivalently, the 840-column `R²` block has contact quotient rank 795 modulo
the complete `{raw,R,S}` prefix, relative kernel dimension 45, and relative
boundary gain three. So `R²` identifies where the first complete contact
kernel is born, but it does **not** supply the missing fourth boundary
direction. The earlier claim that this was the desired osculating
breakthrough is withdrawn.

## Exact semantics and receipt

The contact rows are literal `(epsilon,S,T,R,Z)` monomials under

```text
Y -> u0 + u1*Z + epsilon*R - epsilon^2*S + epsilon^3*T
```

modulo `epsilon^6`. The four appended graph-boundary rows are evaluated at
`(Y,R,S,Z)=(P,P',HasseDeriv 2 P,gamma)`, in script order `(Y,R,S,Z)`.

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
canonical SHA-256  7df8a66b42a58709c530313ee6af2bcb1b3b3e6fcd0e8c20f80e48cbca3d03ff
script SHA-256     fe873ef3b32dc0c44ec0d45eff8247b497f1fdfc6cd1915cb9ba4efb70ecfd88
runtime            44.692 s
peak RSS           1,031,228 KiB
```

The driver performs one exact contact RREF and one augmented RREF. Prefix
ranks are obtained by counting pivot columns in the declared group order, so
there is no separately rounded or randomized rank estimate.

## What this proves and what it does not

Because the entire `{raw,R,S}` union is injective, every complete contact
relation in this receipt necessarily has nonzero `R²` support. But its
boundary image is only three-dimensional, so understanding this quotient
alone cannot establish the required rank four. The next discriminator must
compare it with the rank-four weighted head and isolate the terminal-row
connecting obstruction.

The result does not say that `R²` alone spans the correction or that this
particular four-group order is canonical. It also does not transport the
finite ranks to `(m,B,s,U,L)=(47,16,8,64,3757)`. At target scale there are
many higher derivative shapes, and a proof must show either that they are
capacity scaffolding for this low seam or extend the same recurrence through
them.

The locator/value/slope second covariant remains structurally relevant. With
formal curvature convention `-epsilon²*S`, the correct curvature residual
begins with

```text
S - HasseDeriv 2 P - (Z-gamma) * HasseDeriv 2 Q,
```

equivalently twice this expression may be written with ordinary second
derivatives. Any concrete specialization of the axiom-clean identities in
`K0OsculatingHeadCompanion6900.lean` must respect this divided-power
normalization. The immediate gate is not to prove an `R²` rank-four claim;
it is to identify the fourth head direction and the exact terminal row that
prevents it from lifting while respecting every target X window.
