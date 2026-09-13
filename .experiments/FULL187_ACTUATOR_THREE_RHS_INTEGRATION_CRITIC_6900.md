# Full187 actuator integration critic: both new packets miss the literal THREE-RHS map

Date: 2026-09-13 UTC. Scope: lower-6900 research only. Audited commits:

```text
602e4f8  ratio-59 relay
a71ff3f  A36/A37 J2-BZ actuators
```

No production, submission, score, radius, or claim file was changed.

## Executive verdict

The source-window arithmetic in the two commits is not the current problem.
When their rows are interpreted in the actual Full187 normal coordinates,
both families have the first two required structural properties:

```text
C_G(h)=0,                 J_YRS(h)=0.
```

Neither family satisfies the third and decisive property

```text
C_E(h)=C_E(F_i).
```

The exact outcomes are:

| family | `C_G=0` | `J_YRS=0` | literal `C_E` verdict |
|---|---|---|---|
| `R60,R59` from `602e4f8` | yes, termwise | yes | value, `E`, `TR`, and `T^2S` can match, but `T^2R^2=-1711 F0_value`; pure `T` was also never controlled |
| `A36,A37` from `a71ff3f` | yes, termwise | yes | fails already in the contact-weight-zero passive `S` coefficient |

Consequently these commits do not produce even one of the three corrections
required by `GlobalO2ExactYRSThreeRHSIffAndZSplit6900`:

```text
C_G(h_i)=0,
J_YRS(h_i)=0,
C_E(h_i)=C_E(F_i),        i=0,1,2.
```

The ratio pair remains a useful partial `F0` actuator. The A36/A37 pair, as
currently interpreted, is not a literal-contact GO.

## 1. Why both families really are in `ker C_G`

At an agreement root the established normal contact orders are

```text
ord(L)=1,  ord(V)=1,  ord(J1)=2,  ord(J2)=3.
```

An `X`-coefficient such as `q,H,U,B` has contact-order floor zero. Therefore
the ratio rows have termwise orders

```text
R60:      ord(U V^60)                 = 60,
          ord(H^3 Z V^58 J1)          = 58+2 = 60;

R59:      ord(L U V^59)               = 1+59 = 60,
          ord(L H^3 Z V^57 J1)        = 1+57+2 = 60.
```

For `A_b=q L^(60-b)V^b(J2-BZ)`, the two expanded summands have orders

```text
ord(q L^(60-b)V^b J2)  = 63,
ord(q L^(60-b)V^b BZ)  = 60.
```

Thus the pure-endpoint identities in the commits are not what establishes
`C_G=0`; the order ledger does. The commits themselves did not instantiate
this conclusion against `globalPassiveArrayConstraint`, but the literal
F101 replay below checks every agreement-contact coefficient and finds zero.

## 2. Why both families have `J_YRS=0`

The exact polynomial boundary map retains terms of total global boundary
degree one in `Y,R,S,Z` and then forgets `Z`. Each ratio-row summand is
homogeneous of degree 60 or 59. Each `A36/A37` summand is homogeneous of
degree 37 or 38. Hence no row has a linear `Y/R/S` coefficient:

```text
J_YRS(R60)=J_YRS(R59)=J_YRS(A36)=J_YRS(A37)=0.
```

This also locates both proposals in the **high boundary-degree block** of the
faithful F101 model. They are not the boundary-degree-zero/one relay which
the exact low/high minimizer found necessary. “Low” in “ratio-59 low relay”
means one lower normal degree, not the low block of the Schur decomposition.

## 3. Exact failure of the ratio-60/59 packet

At a simple error, suppress scalar `X`-coefficient Taylor terms for the
moment and write

```text
V = 1 + E + T R - T^2 S/2 + (pure T^2 terms).
```

The `H^3J1` tail begins at horizontal order three. If the effective values
of the two surviving `V` powers are `-58f` and `59f`, their first binomial
moments are

```text
sum A_n                  = 1,
sum n A_n                = 1,
sum binom(n,2) A_n       = -1711.
```

Therefore, with `f=L(x)^59 != 0`, the pair really matches these affine error
rows:

```text
1,  E,  T R,  T^2 S.
```

It cannot match `T^2R^2`: `F0=L^59V` has coefficient zero there, while the
pair has

```text
-1711 L(x)^59.
```

The target characteristic `2130706433` does not divide `1711=29*59`.
Coefficient-polynomial derivatives cannot change the `R^2` row, and the
explicit tail starts one horizontal order later. This is the first
**forced** falsifying coefficient.

There can be an earlier instance-dependent failure. Nodewise CRT values prove
only

```text
(A60+A59-f)(x)=0.
```

The pure-`T` coefficient additionally requires

```text
(A60+A59-f)'(x)=0.
```

Equivalently, at all simple error roots the aggregate difference must be
divisible by `H^2`, not merely by `H`. The target construction did not prove
this. It fails at all three error nodes in the exact F101 replay.

The smallest repair of the forced `T^2R^2` row is exactly the already-found
degree-58 block: amplitudes `(1653,-3363,1711)` on `(V^60,V^59,V^58)` make
moments `(1,1,0)`. This does not repair the longitudinal Hermite condition.
Adding degree 57 also kills the cubic intrinsic V moments, as recorded in
`d5ed0f9`, but still does not prove the full `C_E` identity.

## 4. A36/A37 fail at contact weight zero

The fatal issue is visible before any Hasse derivative. With

```text
V=Y-QZ,  W=R-Q'Z,  P=S-Q''Z,
J2=L^2P-2LL'W+(2(L')^2-LL'')V,
B=-L^2Q''+2LL'Q'-(2(L')^2-LL'')Q,
```

direct expansion gives the exact identity

```text
J2-BZ = (2(L')^2-LL'')Y - 2LL'R + L^2S.            (1)
```

At an error root, put

```text
c=2(L')^2-LL''.
```

On the horizontal-constant slice, `Y=1+E`; in particular the full passive
weight-zero slice of `J2-BZ` is

```text
c - 2LL'R + L^2S.                                  (2)
```

All A36/A37 terms share this factor. If `A` is their aggregate scalar
amplitude after setting `V=1`, matching the nonzero `F0` value would require

```text
A c = L^59.
```

But matching the target's zero `S` coefficient requires

```text
A L^2 = 0.
```

Since `L` and `L^59` are units at every error, these equations contradict
each other. This is a contact-weight-zero failure. It is not a higher-jet
issue, and adding more values of `b` with the same `J2-BZ` factor cannot
repair it.

The derivation in `a71ff3f` made two related substitutions which are invalid
for the literal contact map:

1. It set the passive variables `R,S` to zero. They have contact weight zero
   and must remain in `C_E`.
2. It identified `d0` with `-B=2L^2(H')^2`. The actual scalar constant after
   subtracting `BZ` is `c=2(L')^2-LL''`; it is not known to be a unit.

After additionally assuming `c != 0`, the two rows can match the two scalar
projections `1` and `E` in the quotient `R=S=0`. That is the exact content of
the 2-by-2 determinant. It is not a match of the literal error-contact slice.
The advertised separate `TR` matrix also omits contributions from the
weight-zero `R` term coupled to derivatives of `q L^(60-b)`.

## 5. Exact F101 replay

`full187_actuator_interface_critic_6900.py` uses the repository's primary
literal control

```text
F101, n=11, G={0,...,7}, E={8,9,10}, Q=Xi_E^2, m=4.
```

It scales `(R60,R59)` to `(R4,R3)` and `(A36,A37)` to `(A1,A2)`. The scaled
rows are intentionally outside this tiny control's source windows; the test
is of the exact contact and boundary-map semantics. Target source legality
is the independent arithmetic already checked in the audited commits.

For every scaled family, the replay verifies all literal agreement contacts
are zero and its exact polynomial Y/R/S normal is zero. It then gives:

```text
R4/R3:
  value, E, TR, T^2S residuals            0 at all errors
  pure-T residuals                         14,32,90
  T^2R^2 residuals                         93,26,18  (all nonzero)

A1/A2, after deliberately matching value and E:
  weight-zero S residuals                  38,26,86  (all nonzero)
  weight-zero R residuals                  95,100,8  (all nonzero)
  TR residuals                             74,11,54  (all nonzero)
  actual c                                 15,11,74
  incorrectly claimed -B                   94,35,66
```

The independent source-box-exact F101 result is even more global: all 1,515
boundary-degree-at-least-two columns together retain joint defect three for
the honest `F0,F1,F2` borders. Closure appears only after a broad collection
of boundary-degree-zero/one columns is restored. These two high-degree
packets therefore do not change the finite mechanism diagnosis.

## 6. Smallest honest next lemma

Freeze further searches for isolated high-degree actuators. The minimum new
statement which can materially advance THREE-RHS is a low-slice completion:

```text
For each i=0,1,2, construct h_i in ker C_G intersect ker J_YRS whose
contact-weight-zero passive polynomial equals that of F_i, and prove that
the remaining positive horizontal/contact grades lie in the high-block
image.
```

For `F0`, equation (1) shows that any proposed new family must have an error
weight-zero slice outside the one-dimensional span of

```text
c-2LL'R+L^2S.
```

The faithful finite model says this is not likely to be one more isolated
packet: the surviving mechanism is the forced boundary-one seed-zero head,
its broad positive-seed completion, and the boundary-zero passive recurrence.
That is the route which fits the literal three-RHS interface.

## Reproduction

```text
python3 -m py_compile \
  .experiments/full187_actuator_interface_critic_6900.py
prlimit --as=4294967296 --cpu=240 -- python3 -B \
  .experiments/full187_actuator_interface_critic_6900.py

.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187ActuatorInterfaceCritic6900.lean
```

Receipts:

```text
F101 canonical payload SHA256
  b4dadb7d6c87f960048e7ec332e3bc05d5fd242c680a0990c2d40aab2dab0677
Python source SHA256
  ca8fd37a7f43296230ff58e999dc3f79a8812df16f2d00515aadeb803e7c5d2c
Lean source SHA256
  a66ca36ba69834501a20c565c4f331f07316b7c3b8b1b8d94202e8f4df77dc3f
```

The Lean file proves (1), the passive-S contradiction, the `-1711` moment,
and the first pure-T derivative condition. It uses only standard axioms and
contains no `sorry`, `admit`, `decide`, or `native_decide`.
