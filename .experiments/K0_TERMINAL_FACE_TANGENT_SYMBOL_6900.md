# K0 terminal-face tangent symbol and cap-transition STOP

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G`, raw k0 source. This note
derives a target-scalable principal-symbol identity and then records why it
does **not** explain the exact L10-to-L11 rank transition. It is not a target
rank theorem or a submission candidate.

## 1. The scalar that a degree-`w+1` tangent can expose

Let `F` be a global raw source polynomial in the kernel of all contact rows,
let `G` be the exact agreement set, and let `Lambda_G` be its monic locator.
For a degree-`w+1` agreement tangent `Q`, write

```text
H_F(X) = <(Q,Q',Q'',1), gradient F(X,P,P',P'',gamma)>.
```

The usual agreement-contact argument gives
`Lambda_G^m | H_F`. The strict weighted X cutoff gives
`degree H_F <= m*|G|`. Therefore

```text
H_F = c_F * Lambda_G^m
```

for a scalar `c_F`; because the locator is monic, `c_F` is exactly the
coefficient of `X^(m*|G|)` in `H_F`. This is a linear functional `tau` on
the raw source, restricted in the rank problem to the contact kernel.

For a monomial on the last legal X coefficient,

```text
X^a Y^y R^r S^s Z^z,
a = m*g - (w*y + (w-1)*r + (w-2)*s) - 1,
```

assume `P` has exact degree `w`, leading coefficient `p`, and `Q` has exact
degree `w+1`, leading coefficient `q`. Its top tangent coefficient is

```text
q * gamma^z * p^(y+r+s-1) * W_w(y,r,s),

W_w(y,r,s) =
    y * w^r * (w*(w-1))^s
  + r * (w+1) * w^(r-1) * (w*(w-1))^s
  + s * w*(w+1) * w^r * (w*(w-1))^(s-1).
```

The formula is written without division, so it remains valid in finite
characteristic. It is only the value of `tau` on an individual source
column. It says nothing by itself about `tau(ker contact)`.

## 2. The complete m8 active-total-12 face

For `(m,w,g,B,s,U)=(8,3,6,3,1,12)`, the `z=0`, active-total-12 shapes allowed
by `2s+r<=3` are exactly:

| `(y,r,s)` | last X exponent | integer `W_3` | modulo 101 |
|---|---:|---:|---:|
| `(12,0,0)` | 11 | 12  | 12 |
| `(11,1,0)` | 12 | 37  | 37 |
| `(10,2,0)` | 13 | 114 | 13 |
| `(9,3,0)`  | 14 | 351 | 48 |
| `(11,0,1)` | 13 | 78  | 78 |
| `(10,1,1)` | 14 | 240 | 38 |

Thus every one of the six shape types can contribute a nonzero
`Lambda_G^8` scalar in the exact audit chart (`p,q != 0` in F_101). There
are 83 source columns on this face when every legal X coefficient is counted.
None exists at `L=10` or `L=11`; all first exist at `L=12`.

The cleanest two-term symbol is

```text
X^12 Y^11 R - 3 X^11 Y^12.
```

At the cubic candidate leading jet `(Y,R)=(p,3p)`, its value symbol is zero.
At the quartic tangent leading jet `(lambdaY,lambdaR)=(q,4q)`, its tangent
symbol is exactly

```text
q * p^11 * X^48.
```

Equivalently, `R-3Y` vanishes in the candidate leading direction while
`lambdaR-3*lambdaY=q`. This is an Euler defect, not an experimental fit.

## 3. Exact target scaling

The same identity works at the target with

```text
w=131071, U=64, m*g=47*180413=8479411.
```

The literal source pair is

```text
X^90867 Y^63 R - 131071 X^90866 Y^64.
```

Both coordinates are source-legal at `(L,B,s,U)=(3757,16,8,64)` and use
their last X coefficient. If `P` has leading coefficient `p` in exact degree
`w` and the first-excess tangent has leading coefficient `q` in degree
`w+1`, the candidate symbols cancel and the tangent symbol is exactly

```text
q * p^63 * X^(47*180413).
```

The general identity is now compiled as `terminal_euler_defect`; the m8 and
target instances, exact source legality, the six-weight table, and the L10
absence theorem are in `K0TerminalFaceTangentSymbol6900.lean`.

## 4. Full-degree chart guard and a stronger non-sufficiency witness

The terminal-pair scalar contains `p^(U-1)`. It vanishes when the selected
candidate has degree below `w`, including the valid case `P=0`. Therefore it
cannot be promoted as a universal normal-rank pivot without either a graph
translation automorphism or a separate degree stratum. No such contact-map
automorphism is proved here.

More importantly, an alternate source chart shows that a nonzero principal
symbol was never the missing ingredient. The single column

```text
X^(m*g-w-1) Y
```

has tangent top coefficient `q`, independently of `P`. It is already legal
in the L10 audit (`X^44 Y`) and at the target (`X^8348339 Y`). Yet the exact
L10 computation proves `tau` vanishes on all 317 contact-kernel relations.
Thus the source contains columns seen by `tau`, but its *contact kernel* does
not reach them. A successful theorem must construct the global correction
terms that keep contact zero while preserving this top scalar.

This also supplies the safe treatment of `degree P<w`: use the low-active
principal chart, not the terminal homogeneous chart. What remains unproved
is its contact-kernel completion, exactly as in the full-degree chart.

## 5. The controlled L11 result disproves terminal-face necessity

The same receipt, tangent, agreement set, and off-agreement data were rerun
with only `L` changed from 10 to 11. Exact elimination gives:

```text
L=10: source 11178, contact rank 10861, kernel 317, boundary gain 3
L=11: source 13139, contact rank 12321, kernel 818, boundary gain 4
```

L11 still omits the entire active-total-12 face. The fourth direction first
appears during the `R^3` stage, at `X^30 Y^2 R^3 Z`; gains one through three
first appear during `R^2`, at `X^(21..23) Y^5 R^2 Z^2`. These displayed
columns already fit L10. Their L11 kernel relations use the newly added
scaffold, so this is a relative statement, not a four-column identity.

Consequences:

1. The terminal Euler-defect pair is a valid target-legal activation seed.
2. It is not necessary for rank four in the controlled receipt.
3. Individual nonzero `tau` values are not sufficient; even `X^44Y` had one
   at L10.
4. The actual cap transition is a global contact-completion/confluence
   phenomenon supplied by the `active+z=11` layer.

So there is no honest symbolic explanation of L10 versus L16 that mentions
only the terminal face. The sharp tested transition is already L10 versus
L11.

## 6. Relation to the full L16 locator-Schur witness

The independent exact L16 Schur reduction has agreement kernel dimension
6784, error-on-kernel rank 6516, final nullity 268, and boundary rank four.
One `4x4` witness is indexed by four *free coordinates* in the `SR` family:

```text
(q,d,y,z) = (2,4,4,10), (2,4,5,2), (2,4,5,3), (2,4,5,4).
```

Here the X coefficient is in locator basis `Lambda_G^q X^d`, and `d=4=g-1`.
At the target, the literal residue analogue is
`Lambda_G^2 X^(g-1)`, of degree `3g-1`; the target source has ample X room
for the displayed low active shapes. But this does not transport the
witness: the local contact order changes from 8 to 47, and each free
coordinate labels a 268-dimensional Schur-kernel relation after 91-cell
agreement repair and a 6516-dimensional error elimination. It is not a raw
four-column relation.

Two of the L16 witness labels are absent at L10 (`y=4,z=10` and `y=5,z=4`),
while two survive. This confirms that passive reach participates in this
particular minor. It still does not prove those two absent labels are
necessary, because L11 obtains rank four through a different R2/R3 prefix.

Finally, the witness uses `SR` at `y=4,5`, not the centered seam
`SR*Y^(m-2)=SR*Y^6`. Therefore the centered epsilon-factor identity remains
correct but is not the causal source of this exact Schur minor. Inferring a
target `y=m-2=45` repair family from that identity is currently unjustified.

## 7. Precise remaining theorem

The principal symbol is solved. The missing statement is a relative repair:

```text
exists v in ker(all-node contact), tau(v) != 0.
```

To scale the finite evidence, one needs a locator-residue Schur/confluence
identity that constructs `v` from a bounded set of free `SR` (or R2/R3)
coordinates, supplies all agreement and error corrections within the source
taper, and factors the final scalar into certified nonzero mismatch and
Vandermonde terms. Neither the two-term Euler defect nor the numeric four-row
Schur minor proves that statement.

## Verification

`K0TerminalFaceTangentSymbol6900.lean` compiles in 3 seconds under the 4 GiB
wrapper. Printed axioms are only `propext`, `Quot.sound`, and where finite
source arithmetic uses it, `Classical.choice`. There is no `sorry`, `decide`,
or `native_decide`.

