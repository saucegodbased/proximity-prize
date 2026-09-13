# Full187 next contact family: complete quadratic STOP and cubic frontier

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
accepted-6806, claim, score, or submission file was changed.

## Verdict

The entire natural order-three quadratic completion is now closed by an
exact descent, not just the three `T2(X^j Lambda_G)` rows. The proposed
completion with `A=L*H`, `B=L*H'`, `C=L*H''/2` is identically the old row
`H*T2(L)`. More generally, quadratic-zero error contact factors `H` from the
whole same three-parameter family, after which the `SZ`, `RZ`, and `YZ`
source coefficients reproduce the forbidden `L^58 H^3` cascade. Therefore
no quadratic completion or order-four quadratic repackaging is a new route.

There is, however, one genuinely new and completely literal cubic carrier:

```text
J_L = L*(R-Z*Q') - L'*(Y-Z*Q),
C_3 = L^54 * J_L^3.
```

It has agreement-contact order at least 60 and all ten of its fixed-source
coefficients fit the exact target box. Its narrowest coefficient, the pure
`Z^3` tail, has 50,856 degrees of room. This is the smallest new
agreement-contact family found after the quadratic STOP. It does not yet
close THREE-RHS: naively forcing its cubic error top through the whole error
locator makes the pure `Z^3` tail miss by 30,875. A useful continuation must
therefore cancel that tail across a larger cubic family before error descent,
or show that the prescribed three RHS impose less than full cubic-top zero.

## 1. Complete quadratic error descent

Put

```text
T1(B)=B*W-B'*V,
T2(A)=A*W^2-A'*V*W+(A''/2)*V^2-(A/2)*V*P,
K(A,B,C)=T2(A)+V*T1(B)+C*V^2.
```

The exact product-rule identity is

```text
K(
  H*a,
  (H*a)',
  (H*a)'',
  H'*a+H*b,
  (H'*a+H*b)',
  H''*a/2+H'*b+H*c
 )
= H*K(a,b,c),
```

where the suppressed entries are the displayed first and second jets. The
left parameterization is exactly the one obtained from quadratic-zero error
contact:

```text
A=0,
B-A'=0,
C-B'+A''/2=0                    modulo H.
```

For the specific proposed row `a=L,b=c=0`, this says

```text
T2(LH)+V*T1(LH')+(LH''/2)V^2 = H*T2(L).
```

Thus it is not a fourth quadratic direction.

After writing the residual parameters as `a=L*alpha`, `b=L*beta`,
`c=L*gamma` and multiplying by `L^57`, fixed-coordinate coefficient
extraction gives successively

```text
SZ = +(1/2) L^58 H^3 alpha,
RZ =        -L^58 H^3 beta       after alpha=0,
YZ =      -2 L^58 H^3 gamma      after alpha=beta=0.
```

The common degree and loosest strict cutoff are

```text
58*180413+3*81731 = 10709147,
60*180413-(131071-2) = 10693711,
gap = 15436.
```

So source legality kills `alpha`, then `beta`, then `gamma`. The exact
descent identity, all three coefficient extractors, and the arithmetic are
Lean-checked in `Full187CompleteQuadraticDescentStop6900.lean`.

## 2. Why the tempting differentiated `T2` is not order four

The formal derivative combination

```text
A*D(T2(A))-3*A'*T2(A)
```

cancels the pure-`T` leading term if one pretends `V/A` is regular. Literal
contact also has the independent error variable `E` of weight three. At
`T=0` this expression retains

```text
3*(A')^2 * E * W,
```

so it has contact order only three, not four. The exact Taylor
classification consequently reduces every valid order-four quadratic to
products of `A`, `V`, `T1(A)`, and `T2(A)`; after the outside locator power
is adjusted, these are the same quadratic module above. No unavailable
third-jet source operation may be credited.

## 3. Exact cubic carrier and literal source ledger

At an agreement node write

```text
L=T*a,       L'=a+T*b,
V=E+T*v,     W=v+T*c.
```

Then exactly

```text
J_L = -(a+T*b)*E + T^2*(a*c-b*v).
```

Hence `J_L` belongs to the weighted ideal `(E,T^2)` and has contact order at
least two. Its cube has weights `9,8,7,6`; multiplying by `L^54` gives order
at least 60. This proof uses only the literal first two source jets.

In fixed coordinates

```text
J_L = -L'*Y + L*R + Z*(L'*Q-L*Q').
```

For `Q=H^2`, `deg L=g`, `deg H=e`, a shape `Y^y R^r Z^z` with
`y+r+z=3` has coefficient degree at most

```text
54g + y(g-1) + r*g + z(g+2e-1).
```

Against its literal strict cutoff

```text
60g-w*y-(w-1)*r,
```

the exact margin at `(g,e,w)=(180413,81731,131071)` is

```text
148029 - 32391*z.
```

Thus the four seed layers have margins

```text
z=0: 148029
z=1: 115638
z=2:  83247
z=3:  50856.
```

Every shape has `y+r<=3<=82`, `r<=3<=21`, curvature exponent zero, and
total active/seed grade three, so all non-X caps are literal as well.

## 4. The precise remaining cubic obstruction

If vanishing of the cubic error top is enforced by multiplying the whole
carrier by `H`, the pure seed degree becomes

```text
54g + 3*(g+2e-1) + e = 10855655,
```

while the `Z^3` cutoff is `60g=10824780`. This is red by 30,875. The lower
seed layers would still have post-`H` margins `66298,33907,1516`; only the
last layer fails. This sharply localizes the next experiment: use a genuinely
larger cubic contact family to annihilate its `Z^3` coefficient before the
error factor, while preserving all `z<=2` bounds. Merely taking more shifted
cubes of `J_L` is not enough: they remain binary cubics in `J_L` and `L*V`,
and their finite-difference relations are identities of the whole source,
not selective cancellations of only `Z^3`.

Lean receipt:

```text
Full187CubicFirstTransvectantCarrier6900.lean
sha256 7f64958077c7d720ba932bd072d14f0bcc562904b1484b4ca530d8c4d0fd4a94

Full187CompleteQuadraticDescentStop6900.lean
sha256 986fb0b88cbf218042c3986d84e4f19de55094e662a90cf283a2a66b6b4a1cf2
```

Both targeted overlay builds are green and print only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. Neither file contains
`sorry`, `admit`, `decide`, or `native_decide`.

## 5. Follow-up breakthrough: degree five absorbs the error locator

The cubic obstruction suggests increasing the power, and the exact general
formula makes the threshold sharp. For

```text
C_(k,a) = H^a * L^(60-2k) * J_L^k
```

and a shape `Y^y R^r Z^z`, `y+r+z=k`, the target margin is

```text
k*(g-w+1) + z*(w-2e) - a*e.
```

It is minimized at `z=k`, where it becomes

```text
k*(g-2e+1)-a*e = 16952*k-81731*a.
```

Consequently `a=1` is red for `k=3,4`, but green for the first time at
`k=5`. The explicit quintic

```text
H * L^50 * J_L^5
```

has contact order `50+5*2=60` on agreements (`H` is a unit there) and
all of its source coefficients fit. The post-error-factor margins for
`z=0,...,5` are

```text
164984, 132593, 100202, 67811, 35420, 3029.
```

Thus the pure `Z^5` term, degree 10,821,751, is strictly below the cutoff
10,824,780. All active shapes have total degree five, slope at most five,
and curvature zero. The exact local identity and complete ledger are
Lean-checked in

```text
Full187QuinticFirstTransvectantErrorCompatible6900.lean.
```

This is the smallest pure first-transvectant power compatible with one whole
error-locator factor. For reference, the smallest powers compatible with
`H^a`, `a=1,2,3,4`, are `k=5,10,15,20`; even the slope cap `k=21` cannot
carry `H^5`.

## 6. Exact local rank STOP for the pure-power family

The quintic is a real source row but does not alone settle the three RHS.
At an error node, write the weight-zero residual, slope, and curvature
variables as `(d,w,s)`, and let `L,L',L''` denote the nonzero agreement
locator jet. Then

```text
j  = L*w-L'*d,
F0 = L^59*d,
F1 = L^58*j,
F2 = L^57*(L^2*s-2LL'*w+(2(L')^2-LL'')*d).
```

Every row with `a>0` vanishes in contact weight zero. Every remaining pure
`J`-power combination is a polynomial `P(j)` with `P(0)=0`, because the
strict source cutoff excludes the `k=0` row `L^60`. This image contains
`F1`, but not `F0` or `F2`:

* at `(d,w)=(L,L')`, one has `j=0` but `F0=L^60 !=0`;
* at `(d,w,s)=(0,0,1)`, one has `j=0` but `F2=L^59 !=0`.

These two specializations are Lean-checked in
`Full187FirstTransvectantPowerLocalRankStop6900.lean`. Therefore the pure
power family has local leading rank only one on the three standard RHS. It
can contribute the `F1` channel and supplies new high-order correction rows,
but any actual THREE-RHS producer still needs a mixed curvature/`T2` family
for `F0` and `F2`. This is a rank STOP for pure powers, not for the full
187-shape source.
