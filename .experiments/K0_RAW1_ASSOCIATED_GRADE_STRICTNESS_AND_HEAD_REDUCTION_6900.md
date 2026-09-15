# K0 raw-1 associated grade, strictness obstruction, and scalar head reduction

Date: 2026-09-15 UTC. Scope: lower-6900 k0 last-passive-layer route. This
changes no production candidate, score, or submission.

## Verdict

Three conclusions are exact.

1. **GREEN algebra:** modulo the previous passive grade, the raw-1 last face
   is a weighted bivariate Hermite evaluation map in `(X,u1)`.
2. **RED shortcut:** raw-1 alone has no dimension-forced associated kernel at
   the target, and an associated kernel need not lift through the complete
   preceding cap. The missing property is strictness of the filtered contact
   map, equivalently a global lower-grade interpolation theorem.
3. **GREEN scalar reduction:** for the old cap projected to ordinary epsilon
   orders at least three, raw `S`, `R`, and `Z` give three boundary axes for
   free. They live in the **head-projected** contact kernel, not the full
   contact kernel. Consequently head-kernel boundary surjectivity reduces to
   one vector with nonzero `Y` boundary coordinate. Pure `Y` shows the exact
   remaining obstruction: its high-head term begins with `epsilon^3*T`.

The new target theorem is therefore not “one spare passive layer always
repairs a defect.” It must prove either the required filtered strictness plus
a nonzero relative boundary symbol, or directly construct the one missing
`Y` head-kernel witness and feed it to the existing quotient-aware terminal
dual detector.

There is nevertheless one exact structural benefit at the new proposed
`L=3758` profile. Since the active cap is `U=64 ≤ 3757`, every genuinely new
3758 column has positive `Z` exponent and is the passive successor of a legal
3757 column. This is formalized by
`target_L3758_new_layer_is_passive_successor`; it is a support theorem, not a
contact-rank theorem.

## 1. Exact associated-grade formula

Give `R,S,T,Z` passive degree one and give `epsilon` degree zero. The literal
contacted received coordinate is

```text
u0 + V,       V = u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

For a new raw-1 face monomial

```text
X^a Y^y Z^z,       y+z=L,
```

the exact contacted column is

```text
(x+epsilon)^a (u0+V)^y Z^z.
```

The binomial summand containing `j` copies of `V` has passive degree `z+j`.
Every term involving `u0` therefore has degree below `L`; the unique top term
is

```text
(x+epsilon)^a V^y Z^z.
```

For a composition

```text
iR+iS+iT+iZ=y,
d=iR+iS+iT,
q=iR+2*iS+3*iT,
```

the coefficient of

```text
R^iR S^iS T^iT Z^(L-d)
```

is

```text
multinomial(y;iR,iS,iT,iZ)
  * (-1)^iS * u1^iZ * epsilon^q * (x+epsilon)^a.
```

Taking outer epsilon coefficient `q+h` contributes

```text
choose(a,h) x^(a-h),
```

the `h`th Hasse derivative of `X^a` at `x`. The `u1` factor is the inner
Hasse derivative of `U^y`, up to the derivative-shape multinomial. Thus the
associated map factors exactly through bivariate Hermite jets in `(x,u1)`;
this is not an analogy or rank heuristic.

`.experiments/K0RawOneAssociatedFace6900.lean` formalizes the exact binomial
split, the top face, the coefficient formula over `K[epsilon]`, target source
legality, and the target counts. It compiles with only `propext`,
`Classical.choice`, and `Quot.sound`.

## 2. Target raw-1 dimension stop

At

```text
(n,w,g,m,U,L)=(262144,131071,180413,47,64,3757),
D=47*g=8,479,411,
```

the raw-1 last face has

```text
sum_{y=0}^{64} (D-w*y) = 278,534,035
```

columns. The universal bivariate order-46 Hermite target has

```text
47*48/2 = 1128 rows/node,
262144*1128 = 295,698,432 rows.
```

Hence raw-1 is short by

```text
17,164,397.
```

This does not prove injectivity, but it decisively blocks any raw-1-only
dimension proof of a top-grade relation. The other raw derivative shapes or
special structure of `(x_i,u1_i)` are load-bearing. The positive 23,088,879
margin belongs to the **complete** new face, not raw-1.

## 3. Exact finite associated and relative controls

`.experiments/k0_raw1_associated_face_gate_6900.py` builds the formula above
directly over `F_101`. Exact ranks are:

```text
case                         face cols   Hermite rank   associated nullity
m8 positive L11                   378             324                   54
target-ratio m5 L8                180             165                   15
target-ratio m6 L8                252             231                   21
```

The target-ratio cases then quotient by the contact image of the **complete**
cap-L-1 source:

```text
case       old C/A/gain    combined C/A/gain   relative rank/kernel
m5         2901/2905/4       3070/3074/4              169/11
m6         3867/3871/4       4115/4119/4              248/4
```

Thus four of the fifteen m5 associated relations and seventeen of the
twenty-one m6 associated relations do not lift through the preceding cap.
The lower-grade remainder is a real obstruction, not bookkeeping. In these
two controls the old normal is already rank four, so they test strictness,
not a 3-to-4 transition.

Final receipt:

```text
canonical SHA-256  88ab536e047246809af6919bc5db890a602d953cf399ef897b357044f78e50ba
script SHA-256     e0790e0adc0444b4814ab2e4e0e69eb43c04fd7c4f61a3535b43f5a3c00841aa
runtime / peak RSS 116.287 s / 837,416 KiB
```

The finite literal matrix uses the divided-power coordinate
`-eps^2 S / 2`, while the Lean identity below uses the invertibly rescaled
coordinate `-eps^2 S`.  The script now matches the literal convention
exactly.  Rescaling the `S` rows is invertible over `F_101`, so the ranks and
the canonical mathematical receipt are unchanged.

## 4. Exact strictness condition

Write the split contact maps as

```text
oldContact(p)  = (C_old(p), 0),
faceContact(f) = (C_lower(f), C_top(f)).
```

Then a face vector is truly old-correctable iff

```text
C_top(f)=0  and  C_lower(f) is in range(C_old).
```

Consequently

```text
liftableFace = ker(C_top)
```

iff the filtered contact map is strict at this face:

```text
for every f in ker(C_top), C_lower(f) is in range(C_old).
```

`.experiments/K0AssociatedGradeStrictness6900.lean` proves this equivalence
and an exact two-dimensional counterexample in which the associated kernel is
nonzero but the liftable face is zero. It compiles axiom-cleanly. This is the
precise global-node interpolation obligation hidden by any claim that a top
Hermite relation automatically gives a relative repair.

The lower terms contain powers of the arbitrary node values `u0_i`. Lowering
the `Y` exponent by one frees only `w=131071` units of X degree, less than the
`n=262144` coefficients needed to interpolate arbitrary values at all nodes.
Lowering by two frees `262142=n-2`, very close but still not a generic CRT
right inverse, and higher Hasse conditions consume more. This arithmetic
explains why strictness is the correct hard theorem rather than a formal
triangularity consequence.

## 5. A broad generic one-layer claim is false

The independent exact sweep

```text
.experiments/k0_first_positive_passive_universal_falsifier_6900.py
```

tests six small first-positive profiles, three qualitatively different bad
received families, and seed zero/nonzero translations. Its final receipt is:

```text
complete cap rank four       30 / 36 cases
old + new passive rank four   6 / 36 cases
complete-cap defects          6 / 36 cases
canonical SHA-256
  5f613c4ca4b9e0cc5d7cd7efbb2519615bab86a6b1957e062e7149acbac53658
script SHA-256
  62a9212cb41562a14f5706126dab0ca868418db618c61a1163fbeb532d769e0d
runtime / peak RSS             31.842 s / 62,980 KiB
```

Therefore none of the following is a valid generic theorem:

```text
retained badness + first positive source margin => rank four,
one additional passive cap => rank four,
associated top-grade kernel => old-correctable relation.
```

The new positive cap-`L=U` defect that repairs at `L+1` is valuable evidence
for the target recurrence, but it cannot promote these false universal
statements. A sound theorem must name the contact-specific strictness or
adjoint recurrence hypothesis.

## 6. High-epsilon head: three axes are free, one is hard

Project the old cap contact to ordinary epsilon orders at least three. The
raw monomials

```text
S, R, Z
```

have contacted columns exactly

```text
localS, localR, localZ,
```

so they lie in this **projected head kernel**. Their boundary gradients, in
the verified order `(S,Y,R,Z)`, are exactly

```text
e_S, e_R, e_Z.
```

All three are source-legal at target cap 3756. Therefore the head-kernel
boundary image has rank at least three without using the +477,524,385,561
dimension margin. To obtain rank four it suffices to construct one more
head-kernel vector whose `Y` boundary coordinate is nonzero.

The pure `Y` contact is

```text
u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

Its unique term of order at least three is `epsilon^3 T`. This isolates the
actual scalar producer: cancel the high `T`/adjoint channel globally while
retaining a nonzero `Y` boundary derivative.

`.experiments/K0HeadKernelThreeAxes6900.lean` proves all literal contact,
boundary, and target legality identities. It also proves a composition-safe
consumer:

```text
if vS,vR,vZ,vY lie in ker(headContact),
boundary(vS)=eS, boundary(vR)=eR, boundary(vZ)=eZ,
and boundary(vY).Y != 0,
then boundary restricted to ker(headContact) is surjective.
```

This theorem is explicitly about the head-projected kernel. It does **not**
put the pure axes in the full contact kernel. Returning to complete contact
still requires the existing terminal correction / quotient-aware dual
detection theorem. The same module now composes the two interfaces in
`fullCompatibleDual_boundary_eq_zero_of_axes_Y_and_terminal_zero`: the axes
plus one head-kernel nonzero-Y witness imply that every *complete* compatible
dual with zero terminal component has zero boundary covector. This does not
replace complete contact by a tail-only projection. The module compiles with
only standard axioms.

## 7. Honest remaining theorem

The most compressed target obligation is now one of the following equivalent
producer forms:

1. construct one cap-3756 source vector killed by epsilon orders `3..46` and
   having nonzero `Y` boundary derivative; then use terminal dual detection
   on orders `44,45,46`, or
2. prove strictness for the relevant complete cap-3757 face kernel and show
   its relative boundary connection is nonzero on the remaining conormal.

No target-uniform construction of that scalar witness is presently proved.
This is a genuine algebra/interpolation gap, not mechanical assembly.

## 8. Direct `Lambda_G^46` Y witness: exact all-node RED

The tempting source-legal expression

```text
F = Lambda_G^46 * (Y - P(X) - Q(X)*(Z-gamma))
```

does vanish to contact order 47 at each agreement: `Lambda_G^46` contributes
46 orders and the bracket contributes one. It also has the desired nonzero Y
boundary derivative away from the domain. But the complete contact and the
head split both use **all n nodes**. At every error, `Lambda_G` is a unit and
the bracket is not even constant-zero, so high contact orders survive.

Making the two interpolants match all nodes would require degree `<n` rather
than `<g`. The corresponding source term has worst X degree

```text
46*g + n - 1 = 47*g + 81,730,
```

so it violates the strict cutoff by exactly `e-1=81,730`. The agreement-only
version has 49,342 degrees of legal slack; it is the error interpolation that
breaks it. The terminal error width is 90,867, only 9,136 above `e`, explaining
why the remaining fix must use the narrow error CRT/HRS channel rather than a
full all-node interpolant.

`.experiments/k0_direct_y_witness_allnode_falsifier_6900.py` tests the exact
m8 analogue `Lambda_G^7*(Y-P-Q*(Z-gamma))`:

```text
raw terms / source legal                         112 / true
agreement contact support                              0
error contact support                                101
error contact support at outer orders >=3             65
boundary gradient (Y,R,S,Z)                  (97,0,0,85)
canonical SHA-256
  5df8fc9130cf261c01af4099d00c22efd7ef35aafc573c657e2aeb5b1fd898c9
script SHA-256
  9927757d8a6a380a3e8ac1a0d66af763da4948fcb3c68476bb45dae476dc5a2f
```

This is a precise STOP, not a rejection of the scalar reduction. The needed
new idea is an error-only correction preserving the Y boundary coordinate.
