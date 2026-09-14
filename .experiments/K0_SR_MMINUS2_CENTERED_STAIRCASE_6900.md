# K0 SR seam: the `Y^(m-2)` centered staircase

Date: 2026-09-14 UTC.  Scope: lower-6900 exact-G research only.  This note
changes no production source, claim, score, or submission.

## Verdict

The ordered full-source attribution now has a concrete symbolic candidate
for the first kernel-producing SR band:

```text
epsilon^2 * S*R * (V - anchor)^(m-2).
```

Under the literal contact substitution

```text
V - anchor = epsilon * (R - epsilon*S + epsilon^2*T),
```

this packet is divisible by `epsilon^m` and therefore disappears in the
order-m local contact quotient.  Its leading raw cell is
`S*R*Y^(m-2)`, whose active degree is exactly m.  This explains why the
count-level first candidate in the m8 attribution is `S*R*Y^6`, and predicts
the target m47 seam `S*R*Y^45`.

This is a real local contact-zero mechanism with fully checked target
source legality.  It does **not** by itself explain the global kernel: the
causal centered triangle is much smaller than the contact-row capacity, so
the high-passive-degree SR scaffold remains load-bearing.  It is not yet the global four-boundary theorem: the
centered packet must still be assembled across all agreement nodes with a
single legal global coefficient system, and four independent boundary
images must be proved.

## 1. Exact attribution being explained

On the capacity-positive F101 receipt, the ordered stages are

```text
selected low + remaining S + R^2 + R^3    15,057 columns, kernel 0
+ all remaining SR                         17,679 columns, kernel 268, gain 4
```

Within SR ordered by Y-degree, the prefix through `Y<=5` has 17,322
columns, still below the 17,432 summed local-rank bound.  Thus `Y=6=m-2`
is the first SR band that can cross capacity in this ordering.  This count
does not by itself localize the first exact pivot loss or gain to that band;
the factorization below makes it the first algebraically natural candidate.

There is an important scope guard.  The centered triangle
`Y^y Z^z`, `y+z<=6`, has only 868 SR columns, so adjoining it to the 15,057
injective prefix gives 15,925 columns, still far below 17,432.  The full
`Y<=6` SR prefix has 2,436 columns because it includes high passive shifts.
Therefore the small centered triangle can seed a relation but cannot, by
dimension alone, create the observed global kernel.  Any successful
assembly must couple it to those high-Z columns or an equivalent full-source
confluence.  No claim below removes that requirement.

## 2. Literal centered factorization

Write

```text
anchor = u0 + u1*Z
slope  = R - epsilon*S + epsilon^2*T
V      = anchor + epsilon*slope.
```

Then for every q,

```text
epsilon^2*S*R*(V-anchor)^q
  = epsilon^(q+2)*S*R*slope^q.
```

The compiled specializations are

```text
q=6:   epsilon^2*S*R*(V-anchor)^6  is a multiple of epsilon^8
q=45:  epsilon^2*S*R*(V-anchor)^45 is a multiple of epsilon^47.
```

The second local-X factor is exactly a three-point finite difference:

```text
epsilon^2*(x+epsilon)^a
  = (x+epsilon)^(a+2)
    - 2*x*(x+epsilon)^(a+1)
    + x^2*(x+epsilon)^a.
```

So this is not merely ideal-membership notation.  After expanding the
centered power, it is a literal linear combination of raw source columns
using three consecutive X shifts.

## 3. Target source-cap check

For m47, w=131071 and g=180413, the leading cell has exact X width

```text
47*g - (45*w + (w-1) + (w-2)) = 2,319,077.
```

Hence shifts `a,a+1,a+2` all fit for `a < 2,319,075`.

More importantly, the compiled lemma checks the entire centered expansion,
not only its leading cell.  If a companion contains `Y^y Z^z` with
`y+z<=45`, replacing the other `45-y` Y factors by a degree-at-most-w
anchor contributes X degree at most `(45-y)*w`.  Adding any finite-difference
shift at most two still satisfies all five literal raw caps:

```text
2*S+R <= 16,
S <= 8,
S+Y+R <= 64,
S+Y+R+Z <= 3757,
X + w*Y + (w-1)*R + (w-2)*S < 47*g.
```

This closes the previously uncertain source-legality seam for this packet.

## 4. Two complementary connection identities

The existing complete-contact connection

```text
delta = partial_epsilon + 2*S*partial_R + 3*T*partial_S
```

has the newly compiled edge

```text
delta C[a+1,0,y+1,2,z]
  = (a+1) C[a,0,y+1,2,z]
    + (y+1) C[a+1,0,y,3,z]
    + 4 C[a+1,1,y+1,1,z].
```

At m8, `y=5`, this is exactly

```text
Y^6*R^2  ->  6*Y^5*R^3 + 4*S*Y^6*R
```

plus the ordinary X-lowering term.  Thus the candidate first SR band closes
the adjacent R2/R3 Spencer recurrence; it is not an unrelated padding
family.  A parametric lemma proves that all three shapes preserve every
source cap whenever `w>=3`, `B>=3`, and one S layer is available.

A second derivation is even more triangular:

```text
E = partial_S + epsilon*partial_R,       E(V)=0,

E C[a,1,y,1,z]
  = C[a,0,y,1,z] + C[a+1,1,y,0,z] - x*C[a,1,y,0,z].
```

It sends every SR column into the already-certified R/S prefix via one legal
X shift.  The corresponding source-legality and dual-transpose equations
are compiled.  This is a promising way to propagate compatible-dual
constraints from the injective prefix into the new SR staircase.

## 5. Boundary semantics

For a boundary tangent `(lambdaS,lambdaY,lambdaR,lambdaZ)`, the SR row obeys
the exact inclusion--exclusion identity

```text
b(SR) = S0*b(R) + R0*b(S) - S0*R0*b(1),
```

with the same Y and Z exponents in all four terms.  The identity remains true
after attaching any X-polynomial evaluation factor.

Therefore SR does not create a new fifth pointwise boundary coordinate.  Its
role is to create contact-kernel relations whose images span the existing
four boundary directions.  This matches the exact rank attribution:
boundary gain changes only after the contact kernel appears.

## 6. Remaining hard gate

The local packet vanishes at one centered agreement node.  To finish the
target theorem one must construct a single global raw polynomial (or a
triangular family of them) whose nodewise centers are the actual agreement
anchors while retaining the source caps.  The coefficient-aware legality
lemma shows degree-w anchor substitutions and the three X shifts fit, but it
does not prove the required all-node cancellation/confluence.

The next falsifiable object should therefore be the global locator-adic
assembly of these `SR*Y^45` packets, followed immediately by the rank of
their four boundary images.  Failure modes are now precise:

1. a node-dependent center cannot be represented by the permitted global
   degree-w anchor data;
2. clearing other nodes requires a locator carry outside the 2,319,077 X
   window;
3. the assembled packet kernel exists but its boundary image has rank below
   four.

## 7. Formal artifact

The proof was deliberately split after an RSS audit showed that a monolithic
experimental module was needlessly memory-heavy:

```text
K0SRTinyContactCore6900.lean       literal standalone definitions
K0SRCenteredStaircase6900.lean     factorization, X shifts, target legality
K0SRVerticalKoszul6900.lean        triangular SR -> R/S connection and dual
K0SRR2R3SymbolicSeam6900.lean      R2/R3/SR recurrence and boundary identity
```

Each module compiles independently through the capped Lean runner.  Measured
peak RSS values were respectively 2,016,328, 2,039,904, 2,044,580 and
2,058,688 KiB; the maximum is 1.964 GiB, below the requested 2 GiB ceiling.
Printed axioms are only the accepted `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry`, `decide`, `native_decide`, or unsafe
oracle.  The four Lean sources total only 16,738 bytes.

Source SHA-256 values:

```text
tiny core     6c05d929eb03fa1e9f84451f044fea763f01c31e82825359f7acd6fc6b5cd90f
centered      ed7e6ba3127e2db3ffd2c97495ff1452b5aeb2672a5866cecd757b9856b6023e
vertical      fdf716295d598d3aa9c877d22691089ea1717acec0cae66c7e04e6e55b4114b6
R2/R3/SR      f2d127cbf57776481fac010d6404b82387875c7f8ba0936518d8e16e2f840633
```
