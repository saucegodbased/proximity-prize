# Guruswami multiplicity lattice versus the literal K0 taper: RED

Date: 2026-09-14 UTC.  This is a binary audit of the explicit global
multiplicity-interpolation lattice in ECCC TR23-185 rev.3, Section 10,
against the preferred lower-6900 profile.  It is not an impossibility result
for the full K0 source.

## Explicit construction and exact map

Work over `F(Z)`.  Let

```text
n = 262144,  m = 47,  w = 131071,  a = 180413,
G(X) = product_i (X-x_i),
A(X,Z) = A0(X)+Z*A1(X),  deg_X(A0),deg_X(A1)<n,
H = Y-A(X,Z).
```

Here `A0(x_i)=u0_i` and `A1(x_i)=u1_i`.  Under literal K0 contact at node
`i`, both `G` and `H` have epsilon order at least one:

```text
G(x_i+eps) = eps*G'(x_i)+O(eps^2),
H(contact_i) = eps*(R-A_X(x_i,Z))+O(eps^2).
```

Therefore the Section-10 generators

```text
B_j = H^j G^(m-j),  0<=j<=m;
B_j = H^j,           m<j<=u
```

generate an explicit `F(Z)[X]` lattice contained in the order-47 K0 contact
kernel.  This is a genuine global construction: it uses one locator and one
received interpolant and no nodewise CRT coefficients.  It is, however, the
strong subideal `(G,H)^47`; it does not use the extra raw `R,S` directions
that make the full K0 dimension count positive.

## Exact failed inequality

After the Section-10 shift `Y -> Y*X^w`, the generator matrix is triangular
and has determinant degree

```text
Delta(u) = n*m*(m+1)/2 + w*u*(u+1)/2.
```

Minkowski/approximant reduction gives weighted degree

```text
D_GS(u) = Delta(u)/(u+1)
        = (n*m*(m+1)/(u+1) + w*u)/2.
```

Literal K0 support needs strict weighted degree

```text
D < m*a = 47*180413 = 8,479,411.
```

The active cap requires `u<=64`: `B_u` has the pure term `Y^u`, while K0
requires `S+Y+R<=64`.  For every legal `47<=u<=64`, the required inequality
fails.  The best legal endpoint is

```text
u=64:
D_GS = 568,326,112 / 65
     = 8,743,478.646...
D_GS - m*a = 17,164,397 / 65 = 264,067.646... > 0.
```

Even discarding the active cap does not repair the theorem.  The integer
minimum is `u=66` (the finite difference changes sign between 65 and 66), and

```text
D_GS(66) = 585,496,413 / 67 = 8,738,752.432...
D_GS(66)-m*a = 17,375,876 / 67 = 259,341.432... > 0.
```

Thus the paper's explicit short-vector guarantee lies beyond the root/taper
threshold.  More strongly, for legal `u`,

```text
Delta(u) > (u+1)*(m*a).
```

The determinant degree is invariant under a polynomial unimodular basis
change.  If every row of some basis were target-legal, its shifted row degree
would be `<m*a`, forcing the opposite determinant inequality.  Hence this
lattice has **no full target-legal polynomial basis**, not merely no legal
standard basis.  This statement remains valid after passing from `F[Z]` to
the larger coefficient field `F(Z)`.

## Tangent enlargement does not change the slope

The primitive linear order-two correction is explicit.  Put

```text
D1 = R-A_X(X,Z),
K  = G'(X)*H-G(X)*D1.
```

Then `K(contact_i)=O(eps^2)`.  In fact a general expression `pH+qD1` has
order at least two at every node only if

```text
G divides q,  and  G divides p+q'.
```

Writing `q=Gc` gives

```text
pH+qD1 = -c*K + G*(d-c')*H
```

for some `d`; hence `K` and `G*H` generate the linear tangent-separator
module.  For generic received interpolation data of degree `n-1`, the pure-X
Wronskian term `G*A_X-G'*A` in `K` has exact degree `2n-2` (its leading
coefficient is minus the leading coefficient of `A`).  Consequently

```text
weighted_degree(K) = 2n-2 = 524,286
2*a                         = 360,826.
```

Any individual order-47 product made from `G`, `H`, and `K` therefore has
generic degree at least

```text
47*(n-1) = 12,320,721 > 8,479,411
```

(the excess is `3,841,310`).  Higher osculating corrections have the same
global interpolation slope: clearing a new all-node jet spends another
approximately `n` units of X degree per contact order.  Individual global
factor generators cannot enter the K0 taper.

## Verdict and useful pivot

**RED** for a direct Guruswami/approximant basis or an individually legal
tangent-factor basis.  The exact failed gate is

```text
min_{47<=u<=64} D_GS(u) = D_GS(64) > 47*180413.
```

This does not contradict the positive full-K0 dimension certificate.  It
pinpoints why: the Section-10 lattice imposes the stronger `(G,H)^47`
conditions and omits the high raw `R/S` carrier layers.  Cross-generator
cancellation could still pull an element into the taper, but a complete legal
basis is determinant-forbidden; allowing arbitrary overflow cancellations is
the existing full coupled Schur/filtered-CRT problem, not a lattice shortcut.

The only structurally distinct next gate is therefore a **module with the
full raw K0 staircase already present**, followed by a global approximant
basis computation/proof that preserves the multitaper.  Repeating the
rank-`u+1` `(G,H)` lattice, adding more `H` rows, or multiplying the primitive
tangent separator cannot update target confidence.

## Formal receipt

`K0GuruswamiLatticeTaperRed6900.lean` checks the legal interval inequality,
both endpoint gaps, and the tangent-slope inequalities without `decide` or
`native_decide`.
