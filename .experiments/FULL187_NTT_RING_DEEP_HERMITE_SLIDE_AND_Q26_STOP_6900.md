# Full187 NTT-ring audit, deep low-active Hermite slide, and exact q26 STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production, the
accepted 6806 proof, score, radius, and submission roots are unchanged.

## Verdict

The reduced NTT value ring

```text
R = F_p[X]/(X^N-1) ~= product_(x in Domain) F_p
```

is **not** an exact coefficient/Hasse quotient for Full187. Hasse
differentiation does not descend to `R`, the strict coefficient windows are
not `R`-submodules, and the frozen `U0` and `U1` are dense nonconstant
circulant multipliers. A reducer phrased as ordinary row operations over `R`
silently loses both derivative and window data.

The correct matrix-free objects are thickened Hermite rings. For all-node
depth `d`, use

```text
A_d = F_p[X]/Omega^d,                   Omega=X^N-1,
```

or, for a strong agreement-Hermite/error-value correction,

```text
A_(G,d;E) = F_p[X]/(Lambda_G^d Lambda_E).
```

In this representation, the new low-active `(y,z)=(8,2674),(7,2675)` slide
is much stronger than its first four-jet use:

```text
y=8 has 26 complete all-node jets;
y=7 has 27 complete all-node jets.
```

It cancels every top-passive `f=8` contribution through coefficient-Hasse
order 25 and every `f=7` contribution through order 26. That is 23,562
original provenance terms on 7,282 distinct row shapes, including all 80
provenance terms in the 33 charge-13 A/B/C rows.

There is also a sharp endpoint: uniform `f=8,q=26` cancellation by the `y=8`
slide is false, already for the legal input coefficient `C(X)=1`. An exact
Frobenius/NTT coefficient gives a nonzero forced term at degree `27N-1`, above
every `y=8` source window. This is a literal target-field counterexample, not
dimension heuristics.

Artifact:

```text
.experiments/full187_ntt_ring_and_deep_hermite_slide_audit_6900.py
```

## 1. Why the reduced value ring is insufficient

Let `Omega=X^N-1`, with

```text
(p,N)=(2130706433,262144),      p=1+8128*N.
```

### Hasse derivatives do not descend

In `R`, `[Omega]=0`, but

```text
H_1(Omega) = N X^(N-1) != 0 mod (Omega),
```

because `p` does not divide `N`. Thus two polynomial representatives of the
same NTT value vector can have different Hasse jets. An `R`-linear matrix
cannot encode the coefficient-Hasse edges in `ba5d126`/`d52afc7`.

### Strict windows are not R-modules

Write

```text
W_d = span(1,X,...,X^(d-1)) inside R,       0<d<N.
```

The multiplier stabilizer of `W_d` is exactly the constants. Indeed, if
`u W_d <= W_d`, then `u*1` first forces every supported exponent of `u` below
`d`. If `u_a != 0` for any `a>0`, multiply by `X^(d-a) in W_d`; the unique
coefficient `u_a` then occurs at `X^d`, outside `W_d`. Hence `u` is constant.

The target executable reconstructs the unique coefficient representatives of
the frozen value vectors by inverse NTT. Both are fully dense:

```text
nonzero coefficients of U0 = 262144/262144,
nonzero coefficients of U1 = 262144/262144.
```

Their coefficient hashes are

```text
U0 13b9184fb8c2dab045f7f22f8e4ddc08206e5f25b76a386799b02dc0aad452b7
U1 6af76cd657aea9734c561aa0146d9ec96d1ecd0e42f52723fb8d8c22ed8a128e
```

So pointwise multiplication/inversion is cheap in the NTT basis, but it does
not preserve a proper coefficient window. `R` remains useful as the order-zero
row-value component; it cannot be the whole filtered source module.

## 2. Correct jet-ring representation

The all-node Hermite CRT gives

```text
A_d ~= product_(x in Domain) F_p[epsilon]/epsilon^d.
```

An element can be stored as `d` node-value arrays. Multiplication is pointwise
truncated convolution in `epsilon`; conversion to the canonical polynomial of
degree `<dN` is a confluent CRT/Hermite transform. A coefficient window of
width at least `dN` contains that canonical representative automatically.

When a received value vector `u(x)` is meant to scale every coefficient-Hasse
order without Leibniz cross terms, use its **constant-jet lift**

```text
u_hat(x+epsilon)=u(x).
```

Then

```text
H_q(u_hat*C)(x)=u(x) H_q(C)(x),       q<d.
```

Multiplication by the ordinary dense degree-`<N` representative of `u` is not
equivalent: its positive jets introduce exactly the forbidden cross terms.

For the mixed capacity branch, the exact smaller algebra is

```text
A_(G,d;E)
  ~= product_(x in G) F_p[epsilon]/epsilon^d
       x product_(x in E) F_p,
dim = d*g+e.
```

The unique representative of degree `<d*g+e` is source-legal whenever the
strong-capacity inequality `d*g+e <= width` holds.

## 3. Deep version of the low-active slide

The physical charge-13 stream is

```text
C_s(X) Y^61 R^(21-s) S^s Z^2621,       0<=s<=10,
deg C_s < 76979+s.
```

Use the two source-legal corrections

```text
P8_s(X) Y^8 R^(21-s) S^s Z^2674,
P7_s(X) Y^7 R^(21-s) S^s Z^2675.
```

All three layers have combined grade 2703. Their minimum strict coefficient
widths are

```text
width(P8) = 7,023,742 = 26N + 207,998,
width(P7) = 7,154,813 = 27N +  76,925.
```

First set, in `A_26`,

```text
H_q(P8_s)(x) = a8*u1(x)^53*H_q(C_s)(x),     0<=q<=25,
a8 = -binom(61,8) = 1316585101 mod p.
```

For `f=8`, the original top term has `u1^53`, while the `y=8` term has
`u1^0`; the displayed jet scaling makes the node factors identical and

```text
binom(61,8)+a8=0.
```

Thus every legal local choice `(aE,cS)` at `f=8`, for every stream and every
`q<=25`, cancels coefficientwise.

Next set the first 26 jets of `P7` to

```text
H_q(P7_s)(x) = a7*u1(x)^54*H_q(C_s)(x),     0<=q<=25,
a7 = -(binom(61,7)+8*a8) = 1815287010 mod p.
```

At `f=7`, the `y=8` layer contributes one `u1` factor and the `y=7` layer
contributes none. Hence all three again share `u1^54 H_q(C_s)` and

```text
binom(61,7)+binom(8,7)*a8+a7=0.
```

After `P8` is fixed, its order-26 jet is determined. Since `P7` has a complete
27th all-node jet, prescribe `H_26(P7)` nodewise to cancel the remaining
original-plus-P8 `f=7,q=26` row. No claim about `H_26(P8)` is used.

Exact cancellation census:

```text
                         provenance terms    distinct row shapes
f=8, q=0..25                  12,870                3,870
f=7, q=0..26                  10,692                3,412
total                         23,562                7,282
```

For comparison, the A/B/C principal subset is only 80 provenance terms on 33
rows. Thus the same two corrections remove a much larger exact top-passive
frontier without adding new source layers.

Every other contact term of the three physical layers remains present with
its provenance. This is a quotient step, not a complete kernel or packet lift.

## 4. Exact first failure at f=8,q=26

The `y=8` window has only a `207998+s`-coefficient fringe above `Omega^26`,
so it cannot prescribe an arbitrary 27th full-node jet. More strongly, the
needed extension fails for `C(X)=1` in the actual frozen target instance.

Let `v(X)` be the degree-`<N` representative of the value vector `U1^53`.
Because the field has characteristic

```text
p=1+8128N,
```

the unique depth-27 constant-jet lift is

```text
v(X^p) mod Omega^27.
```

Indeed, at every domain node `x`, `(x+T)^p=x+T^p`, so all positive Hasse jets
below `p` vanish. Also

```text
X^(i*p)=X^i*(X^N)^(8128*i)=X^i*(1+Omega)^(8128*i).
```

Therefore the coefficient of `Omega^26 X^(N-1)` is

```text
v_(N-1) * binom(8128*(N-1),26).
```

The target NTT calculation gives

```text
v_(N-1)                                  = 2020367218,
binom(8128*(N-1),26) mod p               =  400901196,
after multiplying by a8                  =  625032631 != 0.
```

Hence the canonical lift has a nonzero standard term at

```text
degree 26N+(N-1) = 27N-1 = 7,077,887.
```

The largest `y=8` window allows degree only `7,023,751`. Since that window is
strictly below `27N`, no alternate representative modulo `Omega^27` can fit.
Thus:

```text
uniform y=8 f=8 q=26 slide = RED, already for C=1.       (Q26-STOP)
```

This stops only the direct low-y slide at its exact first unsupported jet. It
does not prove the q26 row survives after the sharp-pivot/strong-capacity
quotient.

## 5. Interaction with the complete mixed support cover

The new `full187_mixed_pivot_capacity_closure_6900.py` receipt covers every
one of the 70,543 sharp-pivot escape rows by a strong-capacity source:

```text
63,094 use a safe103 shape;
 7,449 use another Full187 shape with a legal lower-active witness;
     0 remain uncovered.
```

For the 7,449 extra witnesses the chosen source has `y=f` and
`z=L-(f+r+s)`. Its selected row takes all Y factors as contact factors and has
`u1` exponent zero. Therefore the pivot itself has no dense `U1` division:
the mixed algebra `A_(G,d;E)` gives a canonical matrix-free correction section
inside the certified width.

This closes the exponent-support and individual interpolation questions. It
does **not** yet close the coupled reducer. Applying a CRT correction produces
other contact and boundary rows; they must be replayed, ordered, and proved to
terminate. The support audit follows sharp-basis remainders, not the complete
tails of every newly chosen CRT polynomial.

A naive array of one N-value row for each escape already costs

```text
70543 * 262144 * 4 = 73,969,696,768 bytes,
```

so the implementation must group common depths/shapes and stream symbolic
operators. Materializing the quotient is outside both the 4 GiB research lane
and the 24 GiB verifier.

## 6. Exact four-packet scope

The fourth target remains

```text
F3 = B*(Y-P-(Z-gamma)q_H),
```

with its literal error-contact and boundary column. Pure `Z1` is not a packet.
The deep slide changes source/contact representatives only; it does not claim
that the complete reduced `F0,F1,F2,F3` columns vanish or lie in range.

## 7. Reproduction and decision

```text
prlimit --as=1073741824 --cpu=120 -- \
  python3 -B \
  .experiments/full187_ntt_ring_and_deep_hermite_slide_audit_6900.py
```

Recorded run:

```text
exit 0; elapsed 11.647 s; peak RSS 152,116 KiB
canonical sha256 51dd018d437dfb8afece1ffde506225d2f01bbcdebc1e6944612fb7cc8afce8f
script sha256    5bb02c6527481bbd43059c529a7fbb3d854828ce61285fb5f3a6fb37950d066e
```

Decision:

```text
GREEN  use A_26/A_27 jet modules for the y8/y7 slide;
GREEN  cancel all top f8/q<=25 and f7/q<=26 rows exactly;
GREEN  use A_(G,d;E) for each strong-capacity pivot section;
RED    extend the same y8 slide to f8,q=26 uniformly;
STOP   any R-linear Hasse/window reducer over values alone;
GO     orient and batch the complete CRT correction tails from q26 onward.
```
