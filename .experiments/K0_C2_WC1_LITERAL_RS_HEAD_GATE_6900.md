# K0 direct-Y head correction: C2/WC1 and naive R/S STOP

Date: 2026-09-15 UTC. Scope: lower-6900 K0 old-cap head producer. This
changes no production or submission file.

## Verdict

The smallest tempting correction is **RED**, already at a single error in
two exact controls.  With the formal flattened contact

```text
Y -> u0 + u1*Z + epsilon*R - epsilon^2*S + epsilon^3*T
```

retain the literal ordinary-epsilon orders `3,...,m-1`.  For

```text
W  = Z-gamma,
A  = Y-P-W*Q,
C1 = Lambda_G^(m-1)*A,
C2 = Lambda_G^(m-2)*A^2,
```

every source-legal `X^j W^z` shift of `C2` and `W*C1` fails to represent the
complete error-head trace of `C1`.  This remains false after asking at only
one error, so the failure is not merely simultaneous global interpolation.

The literal boundary-centered products `RG*C1` and `SG*C1` do not enlarge
the tested family: in both controls there is no source-legal shift of either
whole polynomial.  The same failure is forced at target scale by an explicit
leading monomial.  Proper locator-traded/osculating companions are therefore
necessary; multiplying `C1` by a centered raw derivative is not a legal
shortcut.

## Exact finite results

The script is

```text
.experiments/k0_c2_wc1_literal_rs_head_gate_6900.py
```

It checks every admitted correction coefficientwise against the complete
raw source support, checks zero four-boundary gradient, and checks complete
contact zero on every agreement before projecting its error contact to the
head.  It never calls the old `higher_jet_literal_matrix` contact oracle.

Over `F_101`:

```text
case                         legal C2  legal WC1  RG/SG  simultaneous  each error
m6 (11,5,8,6,2,1,8,8)             28          14    0/0       RED         RED
m8 (9,3,6,8,3,1,12,10)            36          18    0/0       RED         RED
```

More precisely:

```text
m6 all-errors rank/residual support       42 / 158
m6 one-error residual supports            37,37,37
m8 all-errors rank/residual support       54 / 1100
m8 one-error residual supports            286,290,291
```

The residual support is the support after exact sparse echelon reduction; it
can exceed the original target support because pivot subtraction fills rows.
Only its nonzeroness is used.

Receipt:

```text
canonical SHA-256  1e4316145c3796d402538e08621f278bde7bb34495b682accf4024cde31980e8
script SHA-256     66a79b26a93a6e1210f4ef1ad5dfd4721c5672df78daa69483b0bbc22b4665c4
runtime / peak RSS 84.985 s / 51,780 KiB
address-space cap  4 GiB
```

## Why the first T row looked promising

At one error put

```text
lambda = Lambda_G(e) != 0,
delta  = u0(e)+gamma*u1(e)-P(e) != 0,
eta    = u1(e)-Q(e).
```

The coefficient of `epsilon^3*T`, as a polynomial in `W`, is

```text
[epsilon^3*T] C1      = lambda^(m-1),
[epsilon^3*T] C2      = 2*lambda^(m-2)*(delta+eta*W),
[epsilon^3*T] (W*C1)  = W*lambda^(m-1).
```

Consequently, when `2*delta` is invertible,

```text
(-lambda/(2*delta))*[T]C2
  + (eta/delta)*[T](W*C1) = -[T]C1.
```

Thus the first `T` coordinate really can be canceled locally.  The exact
full-head computations show that this does not cancel the remaining
epsilon/R/S/T mixed coordinates.  A proof based only on the leading T row
would be an overclaim.

There is also a global warning hidden in the displayed coefficients: they
depend on the error through `lambda/delta` and `eta/delta`.  Even if the rest
of the head vanished, a target proof would still need to realize these
nodewise ratios by the permitted global multiplier windows.

## Target source ledger

At `(m,g,w,L)=(47,180413,131071,3757)` and strict cutoff `D=47g`, the
worst term of `C2` has X degree

```text
45g + 2(g-1) = 47g-2.
```

Therefore `C2` has exactly two target-uniform X shifts.  Its external
centered-seed shift may range from `0` through `L-2`, giving

```text
2*(L-1) = 7,512
```

uniform `C2` columns.  `W*C1` has worst X degree `47g-1`, hence one X shift,
and total external W exponent `1,...,L-1`, giving `3,756` columns.  The narrow
family has only `11,268` uniform columns before dependencies, far below the
`81,731` errors; this is only a capacity warning, not the reason for the
stronger one-error finite RED.

For the naive raw derivative products, the monic leading cells are

```text
X^(46g) * Y*R  in RG*C1,
X^(46g) * Y*S  in SG*C1.
```

Their literal weighted degrees exceed `D` by

```text
46g + w + (w-1) - 47g = 81,728,
46g + w + (w-2) - 47g = 81,727.
```

So no `X` shift of the whole products is source-legal at the target.  The
correct next family must trade locator powers for genuine osculating
covariants and prove agreement-head cancellation after that trade.

## Scope

Stopped:

```text
full head correction by C2 and W*C1                         RED
the same claim error-by-error                               RED
adjoin RG*C1 or SG*C1 as whole target source polynomials    SOURCE-ILLEGAL
infer full correction from the cancelable epsilon^3*T row   FALSE
```

Still open:

```text
locator-traded first/second osculating companions            OPEN
coupled raw R/S staircase from the complete old source       OPEN
target-uniform bounded-degree error interpolation/confluence OPEN
```

