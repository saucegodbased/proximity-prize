# Three-shape local/Toeplitz connector and arbitrary-`Q` width STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Verdict

There is a small universal identity behind the stable arbitrary-error
`{pure,R,S}` controls in commits `71f233a` and `98ffdd9`.  Over any
commutative coefficient ring, for an arbitrary local factor `P(R,S)`, project

```text
P^m,  P^m R,  P^m S
```

to the coefficients of `1,R,S`.  The resulting matrix is lower triangular:

```text
                  columns
             P^m       P^m R     P^m S
rows  1       a^m         0         0
      R        *         a^m        0
      S        *          0        a^m

a = coeff_(R^0 S^0)(P).
```

Its determinant is `(a^m)^3`.  Thus arbitrary direction mismatch can change
the starred entries but cannot change the diagonal pivot.  The accompanying
Lean file proves this identity, its field-valued surjectivity, and a
conditional three-channel causal block-Toeplitz theorem.

This does **not** yield a theorem for all agreement interpolants satisfying
only `deg Q < g`.  The pure centered carrier is universally source-legal
under that bound, as already proved in `HrsCenteredShellUnit6900`, but the
centered `R` and `S` companions are not.  At the permitted endpoint
`deg Q=g-1`, their literal raw branches violate the strict target width.
Hence the correct target statement must retain the tapered raw legal groups,
or assume the much stronger target-specific degree margin enjoyed by
`Q=Xi_E^2`.

## 1. Formal universal block

Artifact:

```text
.experiments/ThreeShapeLocalConnector6900.lean
```

For `LocalRS A = MvPolynomial (Fin 2) A`, it defines

```text
connectorMatrix P m i j =
  coeff (rowExponent i) (P^m * columnFactor j),

rowExponent = [0, R, S],
columnFactor = [1, R, S].
```

The proved statements are:

```text
connectorMatrix_diagonal:
  M i i = constantCoeff(P)^m

connectorMatrix_above_zero:
  i < j -> M i j = 0

connectorMatrix_det:
  det M = (constantCoeff(P)^m)^3

connectorMatrix_mulVec_surjective:
  over a field, constantCoeff(P) != 0 -> Surjective M.mulVec
```

These are polynomial identities.  They impose no restriction on the
coefficients of `P`, so an arbitrary agreement interpolant and arbitrary
error-direction mismatch may be placed in the coefficient ring.

The same file then takes the passive-seed coefficients of this polynomial
matrix.  If all three carriers have been normalized to a common delay and
these three coordinates form the complete state, the finite causal matrix

```text
T[(time,row),(shift,column)] =
  block[time-shift][row,column]  when shift <= time
```

is lower triangular in lexicographic `(time,channel)` order.  Its determinant
is the product of its diagonal pivot, and it is onto for every finite seed
length when the leading pivot is nonzero.  This is formalized as

```text
causalBlockToeplitz_det
causalBlockToeplitz_mulVec_surjective
polynomialConnectorCausal_surjective
```

The file builds in about 3.4 seconds.  Every printed theorem is free of
`sorryAx` and uses only standard logical axioms (`propext`, `Quot.sound`, and,
for matrix results, `Classical.choice`).  There is no `decide` or
`native_decide`.

## 2. Specialization to the centered-shell identity

`HrsCenteredShellUnit6900` proves the exact local contact formula

```text
(delta + epsilon*tau)^m * tau^(J+1-m),
```

where

```text
delta   = u0 + gamma*u1 - P_agreement(x),
epsilon = u1 - Q(x).
```

It also proves that the lowest centered-seed coefficient is `delta^m`, is
independent of `epsilon`, and that every lower coefficient is zero.  Put all
passive-seed and remaining local variables in the coefficient ring of the
universal block above.  Then its diagonal series has leading coefficient
`delta^m`; at an error with `delta != 0`, the conditional Toeplitz pivot is
nonzero.  This explains why the same three raw shapes remained sufficient in
the nonmatched F101 controls through `m=8`.

It is essential that this is a **local normalized-state statement**.  It
does not prove that the physical complete contact quotient is exactly these
three channels.  In particular, the earlier selected-row overlap STOP shows
that independently shifted carriers can leak to unselected rows.  The
Toeplitz theorem is applicable only after an exact complete-state recurrence
or quotient theorem has established closure.

## 3. Raw legal groups are not centered carriers

At first shell grade `J+1`, the three raw groups are the spans of literal
source monomials

```text
G00: X^a Y^y       Z^z,  y+z=J+1,
G10: X^a Y^y R     Z^z,  y+1+z=J+1,
G01: X^a Y^y S     Z^z,  y+1+z=J+1,
```

subject term-by-term to

```text
a + w*y + (w-1)*r + (w-2)*s < D
```

and the other literal caps.  These groups are legal by construction and do
not mention `Q`.

The convenient centered representatives are specific linear combinations:

```text
C00 = (Y-QZ)^m Z^(J+1-m),
C10 = R (Y-QZ)^m Z^(J-m),
C01 = S (Y-QZ)^m Z^(J-m).
```

Fully centered derivative representatives replace `R,S` by
`R-Q'Z,S-Q''Z`; their correction terms lie in different raw shape groups.
They cannot cancel an illegal `R` or `S` monomial because those monomials
have different derivative exponents.

The local triangular identity applies to the three *formal* columns.  Source
legality of each expanded representative is a separate global width theorem.

## 4. Decisive arbitrary-degree counterexample

Let `D=m*g` and choose a monic interpolant of the allowed degree `g-1`.
The `Y`-degree-zero term of `C10` is

```text
Q^m R Z^J
```

and has weighted cost

```text
m*(g-1) + (w-1).
```

Writing `w=m+excess+1`, the Lean theorem
`penultimateDegree_R_topCost` proves this equals

```text
m*g + excess.
```

Strict width requires the cost to be `<m*g`, so it fails even at
`excess=0`.  Similarly, writing `w=m+excess+2`, the `S` cost is
`m*g+excess`, proved by `penultimateDegree_S_topCost`.

For Full187,

```text
(g,w,m,D) = (180413,131071,60,10824780).

R cost = 60*(180413-1)+(131071-1)
       = D + 131010 = 10955790.

S cost = 60*(180413-1)+(131071-2)
       = D + 131009 = 10955789.
```

Thus the `R` branch exceeds the largest legal integer cost `D-1` by 131011,
and the `S` branch by 131010.  These exact equalities are also proved in
Lean.  This is a decisive STOP for a centered `{C00,C10,C01}` theorem under
the hypothesis `deg Q<g` alone.

More generally, for a raw derivative weight `h` and `deg Q >= w`, the worst
expansion layer is `Y`-degree zero and legality requires

```text
m * (g - deg Q) > h.
```

For `C10`, `h=w-1`; for `C01`, `h=w-2`.  If `deg Q<=w`, the corresponding
endpoint condition is `m*(g-w)>h`.  The uniform concise condition is
`m*(g-max(deg Q,w))>h`.

The actual target direction `Q=Xi_E^2` has degree 163462, not `g-1`.
Commit `98ffdd9` checked every expansion layer and found positive minimum
gaps:

```text
C00 raw branch: 1017060
C10 raw branch:  885990
C01 raw branch:  885991
R-Q'Z full representative worst strict slack: 853598
S-Q''Z full representative worst strict slack: 853599
```

So the target-specific representatives are legal; the universal
`deg Q<g` formulation is what is false.

## 5. Relation to the accepted boundary-tail proof

The accepted `BoundaryTailRecurrence` uses the same proof architecture at a
larger state:

1. `refined_monomial_step` proves the complete three-band recurrence into
   indices `i,i+1,i+2`.
2. `refinedCoefficients_support` proves no state leaks beyond the asserted
   band.
3. `refinedCoefficients_zero_recurrence` identifies the diagonal factor
   `-(2*m+1)`.
4. `signedOddScalar_ne_zero` proves the accumulated pivot is nonzero under
   the characteristic bound.

Only the analogue of steps 3--4 is supplied here for `{pure,R,S}`.  A target
proof still needs the analogues of steps 1--2 for the **complete** agreement,
error-contact, and normal state modulo the literal lower-grade source, plus
endpoint closure inside the tapered coefficient windows.  A local
determinant or selected-row recurrence cannot replace those obligations.

## 6. Exact conclusion

Green and reusable:

```text
universal local 3x3 pivot;
conditional complete-three-state block Toeplitz inversion;
arbitrary mismatch independence of the diagonal;
target Xi_E^2 source legality from commit 98ffdd9.
```

Red / not established:

```text
centered R/S legality from only deg Q<g;
identification of the complete global quotient with three local channels;
confluence of physical shifted raw groups;
finite top-end closure in safe103/Full187.
```

Therefore the next legitimate connector theorem must be stated for the
literal tapered groups `G00,G10,G01` and must prove a complete-state
recurrence.  It may use the triangular block proved here as its local pivot,
but it cannot replace the raw groups by universally centered carriers.
