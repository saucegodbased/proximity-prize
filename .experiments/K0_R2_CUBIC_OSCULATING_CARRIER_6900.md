# K0 R2 cubic osculating carrier and terminal obstruction

Date: 2026-09-15 UTC. Scope: lower-6900 K0 symbolic mechanism. This changes
no production candidate or submission.

## Exact result

Let `H` be the agreement locator, let

```text
A  = Y - P - (Z-gamma)Q,
RG = R - P' - (Z-gamma)Q',
SG = 2*(S - HasseDeriv 2 P - (Z-gamma)*HasseDeriv 2 Q),
```

and write `H'`, `H''` for ordinary derivatives. Define

```text
B1 = H*RG - H'*A,
B2 = H^2*SG - 2*H*H'*RG + (2*(H')^2-H*H'')*A.
```

The exact identity

```text
2*B1^2 - A*B2 = H*C3
```

holds with

```text
C3 = 2*H*RG^2 - 2*H'*A*RG - H*A*SG + H''*A^2.
```

This is not a heuristic transvectant calculation. The Lean theorem
`two_first_sq_sub_value_second_eq_locator_mul_third` proves it by a polynomial
identity. The arbitrary-tail theorem `thirdR2Companion_order_three` proves
that `C3` starts in epsilon order at least three at every simple agreement.

If `RG=R-C0`, then

```text
C3 = 2*H*R^2 + remainder,
```

where `remainder` is affine in raw `R` and otherwise uses only raw and `S`
terms. Thus `C3` is the first triangular osculating recurrence whose leading
shape is `R^2` and whose remainder lies in the exact lower prefix
`{raw,R,S}`. This matches the finite attribution that the complete contact
kernel first appears when `R^2` is adjoined, without claiming that this seam
has boundary rank four.

## Target source ledger

At `(m,g,w,L)=(47,180413,131071,3757)`, use

```text
H^(m-3)*C3 = H^44*C3 = H^43*(2*B1^2-A*B2).
```

The locator contributes order 44 and `C3` contributes order three, so the
contact vanishes through order 46 at every agreement. Its leading R2 term is

```text
2*H^45*R^2.
```

That term alone has weighted-degree margin

```text
47*g - (45*g + 2*(w-1)) = 98,686.
```

The actual uniform carrier window is narrower because the arbitrary tangent
interpolant can have degree `g-1`. The worst raw/raw term has X degree
`47*g-4`, leaving exactly four uniform X shifts. Every base term has passive
degree at most two, so external `(Z-gamma)^z` shifts have
`0 <= z <= L-2`. This gives

```text
4*(L-1) = 15,024
```

literal target-legal carrier shifts. The Lean extremal-shape ledger checks
all limiting raw, R, S, R2, YR, YS, and Y2 cases against `rawShapeLegal`.

The same carrier is boundary-zero: at the accepted graph point `A=RG=SG=0`,
every term of `C3` has at least two centered factors. It is therefore a
correction family; it does not itself create a boundary direction.

## Correct curvature normalization

The accepted formal source coordinate is

```text
S = HasseDeriv 2 P = P''/2.
```

The compressed second-jet oracle uses `V2=P''`. The formal map

```text
E -> epsilon^3*T,     V2 -> 2*S
```

is injective on rows and scales a source column of raw curvature exponent
`s` by `2^s`. At the correct graph point, the boundary map is conjugate as
well: the Y/R/Z rows agree and the S row changes by one global factor two.
This is formalized in `compressed_boundary_conjugacy`. Any replay that pairs
the formal contact with `S=P''` is misnormalized and must be rejected.

## Precise remaining obstruction

The exact corrected m6,L8 control has:

```text
eps>=3 head boundary gain = 4,
complete contact boundary gain = 3.
```

The fourth head direction is represented by pure raw `S`; its head contact
is zero, but it leaves eleven literal epsilon-order-zero `localS` rows. The
complete boundary image has annihilator, in `(Y,R,S,Z)` order,

```text
ell = (1,74,26,77).
```

Since `ell(S)=26 != 0` in `F_101`, no correction inside the complete finite
source can turn pure S into a complete-kernel vector while preserving its
boundary class. In particular the target-legal C3 carrier cannot do so on
this receipt; it is already a subfamily of that complete source and has zero
boundary. This kills a universal claim that the cubic R2 recurrence alone
always repairs the terminal obstruction.

The narrow exact discriminator

```text
.experiments/k0_r2_cubic_terminal_correction_gate_6900.py
```

constructs all three equivalent presentations (`H^44*C3`,
`H^43*B1^2`, and `H^43*A*B2`) coefficientwise in the raw source. Each has 42
legal `X^j*(Z-gamma)^z` shifts in the m6 control, is source-legal,
boundary-zero, and has zero complete contact on every agreement. Results:

```text
family                         full rank   eps0 rank   pure-S in span
C3                                  42          21          no
B1^2 plus A*B2                      84          42          no
all three (C3 is dependent)         84          42          no
```

The answer stays **no even after restricting to the three error nodes**;
the residual has one local-S row at each error. On agreements every carrier
has rank zero while pure S has eight nonzero epsilon-zero rows. Thus the
failure is simultaneously local-at-agreements and global-at-errors, not an
artifact of mixing the two node sets.

```text
canonical SHA-256  8cfd6dc4b79c070b90d32c9caafeb97bbe4c31facb4e45917aef347fa4a09d6e
script SHA-256     2ebbb2e47dc2eb006d78d238e26da6ad6fe424970c6cef434b161689722b462c
runtime / peak RSS 9.209 s / 96,960 KiB
address-space cap  4 GiB
```

What remains potentially target-specific is a larger-cap/later-layer
connecting argument: extra source shapes or the new passive face must alter
the terminal epsilon-zero class. Agreement-local order three is not enough;
the required theorem is a simultaneous all-error/full-contact lifting result.

## Formal verification

Both files compile under the bounded command

```text
env LEAN_PATH=.experiments lake env lean -j1 -M2500 FILE
```

with only `propext`, `Classical.choice`, and `Quot.sound`:

```text
.experiments/K0OsculatingHeadCompanion6900.lean
.experiments/K0CompressedFormalContactEquiv6900.lean
```
