# Exact m=8 locator/Hasse Schur audit

This is a finite mechanism audit, not a proof for the 6900 target.  It uses
the capacity-positive full-source receipt

```text
(n,w,g,m,B,s,U,L,k,n0) = (8,3,5,8,3,1,12,16,0,1)
field                         F_101
trial / seed                  811 / 19
agreement nodes               0,1,3,4,6
error nodes                   2,5,7
prescribed agreement tangent  X^4
agreement locator             X^5+87X^4+67X^3+76X^2+72X
```

The executable receipt is
`k0_m8_locator_schur_boundary_6900.py`.  It sets `RLIMIT_AS` to
4,089,446,400 bytes itself.  Reproduction commands are

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_m8_locator_schur_boundary_6900.py --mode validate
PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_m8_locator_schur_boundary_6900.py --mode structure
PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_m8_locator_schur_boundary_6900.py --mode schur
```

## Exact factorization and the 91-cell agreement seam

For every global source shape, the script changes its consecutive `X` basis
to

```text
Lambda_A(X)^q X^d,  0 <= d < 5.
```

It checks coefficientwise that localization

```text
X -> x+epsilon,
Y -> u0(x)+u1(x) Z+epsilon A
```

followed by the raw local contact substitution

```text
A -> R - epsilon S/2 + epsilon^2 T
```

is the same map as the existing literal contact-column generator.  One local
source has 2,844 coordinates; its literal contact target has 2,965 rows and
rank 2,179, so its contact kernel has dimension 665.

Familywise agreement localization has the following exact dimensions.

| family | global columns | five-node local rows | localization rank | kernel | cokernel |
|---|---:|---:|---:|---:|---:|
| `1`  | 3,692 | 2,640 | 2,640 | 1,052 | 0 |
| `R`  | 3,138 | 2,460 | 2,456 | 682 | 4 |
| `S`  | 3,264 | 2,460 | 2,459 | 805 | 1 |
| `R2` | 2,640 | 2,280 | 2,260 | 380 | 20 |
| `R3` | 2,195 | 2,100 | 2,044 | 151 | 56 |
| `SR` | 2,750 | 2,280 | 2,270 | 480 | 10 |

Thus localization has kernel 3,550 and cokernel 91.  The canonical leading
cokernel cells `(A,Z,q,d)` are:

```text
R:   A=0, Z=0..1, q=7, d=3..4                                  (4)
S:   A=0, Z=0,    q=7, d=4                                     (1)
R2:  A=0, Z=0..3, q=7, d=1..4; A=1, Z=0..1, q=6, d=3..4       (20)
R3:  A=0, Z=0..5, (q=6,d=4 or q=7,d=0..4);
     A=1, Z=0..3, q=6,d=1..4; A=2, Z=0..1,q=5,d=3..4          (56)
SR:  A=0, Z=0..2, q=7,d=2..4; A=1,Z=0,q=6,d=4                (10)
```

Projecting the product of the five 665-dimensional local contact kernels to
these 91 cokernel coordinates gives an exact `91 x 3325` matrix of rank 91.
Consequently its kernel has dimension `3325-91=3234`, and the agreement
contact kernel and rank are

```text
ker(C_A) = 3550 + 3234 = 6784,
rank(C_A) = 17679 - 6784 = 10895 = 5 * 2179.
```

This is an important correction to the tempting four-cell picture: before
the error equations, the locator/Hasse seam has 91 cells, including four
`R` cells.  The local contact kernels repair all 91.

## Staged error and boundary Schur complement

The full-source columns are ordered by the already audited filtration:

```text
selected low / remaining S / R2 / R3 / remaining SR
9964         / 258         / 2640 / 2195 / 2622
```

The script row-reduces agreement contact first.  In its exact RREF
`[I A]`, the implicit matrix

```text
K = (-A; I)
```

has shape `17679 x 6784`, rank 6,784, and satisfies `C_A K = 0`.  This
identity and the rank are fixed before any error elimination.  `K` is kept
implicit to stay below 4 GiB.

The three error blocks then give

```text
C_error K : 6537 x 6784, rank 6516, nullity 268.
```

After this elimination the boundary quotient is literally `4 x 268` and has
rank four.  Every one of its 268 columns is nonzero.  Every free coordinate
is in the `SR` family, with locator/residue distribution

```text
(q,d) = (0,4): 90
        (1,3): 63
        (1,4): 97
        (2,4): 18.
```

The script emits all 268 exact labels and all exact support labels.  Their
SHA-256 is

```text
af81cab8a779873c1d64e2006e9700bb4b6d4ed365d6d7d96683f6751516635a.
```

All 268 are in the support, so that is also the complete support set.  The
first four pivot columns of the `4 x 268` block already give this witness:

| family | q | d | y | z | X-window width |
|---|---:|---:|---:|---:|---:|
| `SR` | 2 | 4 | 4 | 10 | 25 |
| `SR` | 2 | 4 | 5 | 2  | 22 |
| `SR` | 2 | 4 | 5 | 3  | 22 |
| `SR` | 2 | 4 | 5 | 4  | 22 |

The corresponding minor over `F_101` is

```text
43   4   1   4
42  81  36  29
100 93  18  65
10  98  85  44
```

and its determinant is 72.  The SHA-256 of the complete `4 x 268` entry
array is

```text
7a62e7e7c8c3770ed56232de845fe2f05ae3045753f2579576d4c09cd2894f44.
```

So the four boundary directions arise only after the full 91-cell agreement
repair and the 6,516-dimensional error elimination.  In the resulting
quotient they are witnessed entirely by `SR`, not by a standalone critical
`S`, `R2`, or `R3` packet.

## Passive-Z fidelity and the remaining target gap

The finite block does **not** use passive `Z` shifts bounded by the tangent
degree four: one witness has source `z=10`, and the other three have
`z=2,3,4`.  This is not a degree mismatch.  In the exact localization formula
`Y^y Z^z` produces local exponents `Z^(z+t)` with `0 <= t <= y-A`; the degree
of the polynomial `u1(X)` changes coefficients in the `X`/locator module, not
the number of passive `Z` shifts.  Therefore target `deg(Q) <= 180412` does
not require `L >= 180412`; `L=3757` is not the obstruction.

Moreover `4=g-1` in this receipt, just as `180412=g-1` at the target.  The
finite tangent is therefore the correct top-residue chamber after changing
to the locator basis.  What is **not** compressed by this computation is the
whole residual algebra: it has dimension 5 here and 180,413 at the target.

Accordingly, there is a bounded four-row *output* and a four-column finite
witness, but no verified factorization through a target-uniform bounded
symbolic module.  Both witness selection and its entries currently depend on
the preceding full agreement and error eliminations.  The smallest missing
target theorem is a uniform locator-residue Schur identity for the full raw
weighted source: after eliminating the agreement and error blocks, it must
identify four `SR` top-residue coordinates and express their `4 x 4`
determinant by the error-mismatch data.  The finite determinant 72 is evidence
for that identity, not its proof.

## Reproducibility receipt

The green `--mode schur` run took 445.992 seconds and peaked at 3,801,516 KiB
RSS under the hard address-space cap above.  Hashes from that run were

```text
canonical JSON  b54ee89b1b20556999c22f1ed1182137b0cc6bff921d2260e31e5c4a7fe1dfa0
script          2b7dfdd8c635b6e5cf3890a44cb7e9aa9f6b0309964333caacb3f62fd5e79156
```

The quick factorization validation also passed independently in 7.137
seconds at 270,628 KiB RSS.  No production submission file is read or
modified by this audit.
