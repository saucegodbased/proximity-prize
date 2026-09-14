# M5/M6 affine-fibre phase change and load-bearing second jet

Date: 2026-09-14

Status: exact finite-field discovery receipt, **not** a uniform target theorem.
All matrix computations below are over `F_101`, in the fixed `n=10`,
`w=4`, seven-agreement chamber with error-direction offsets `(3,5,7)`.
Every expensive command was run under `prlimit --as=4294967296`; no
production or submission file was edited.

## Executive result

The attractive `m=5` twelve-shape affine lift does not extend to `m=6`.
At `m=5`, all centered `V2` top-shell terms can be removed while retaining
all three exact locator right-hand sides.  At `m=6`, removing all `V2` terms
misses every one of the three right-hand sides, even when the extra visible
noncanonical `V1*V^7*Z` shape is admitted.  Inside the canonical 23-shape
support, removing `V2` annihilates the contact-cycle space completely.

This is a filtered, mixed lower/top phenomenon.  The lower-grade contact map
is injective in both cases.  A legal top shell has a unique lower-grade tail
which cancels its contact image.  The top shell by itself need not be an
agreement cycle, and the correct object is the Schur-complement extension

```
K = { (ell,t) : C_< ell + C_top t = 0 },
T(t) = J ell,  ell = the unique solution of C_< ell = -C_top t.
```

The `m=6` `V2` block is load-bearing for the target subspace of this
extension.  This replaces the disproved scalar-Toeplitz/standalone-cycle
interpretation.

## Exact m=5 receipt

Parameters are `(n,w,A,m,D,s,t,J,L)=(10,4,7,5,35,1,1,7,11)`.

- Grades `<=J` have 2296 source columns and contact rank 2296: the lower
  contact map is injective.
- Adding the 455 grade-eight columns gives 2751 columns, rank 2680 and
  contact-kernel dimension 71.
- The centered grade-eight projection has 22 visible shapes.
- The canonical 17-shape family has constrained kernel dimension 22,
  vertical image rank 12, contains `F0,F1,F2`, and has affine lift fibre
  dimension 10.
- Exhaustive ablation across the six individually optional canonical shapes
  has one maximally pruned green family.  It removes all five `V2` shapes,
  keeps `V1*V^4*Z^3`, and consists of exactly twelve shapes:

```
Z^2 * P_6(V,Z) + V1 * Z^3 * Q_4(V,Z).
```

  This twelve-shape family has constrained kernel dimension 17, vertical
  image rank 12, and affine fibre dimension 5.  Every one of its twelve
  shapes is necessary relative to that canonical family; the eleven-shape
  family obtained by also deleting `V1*V^4*Z^3` has joint defect one.
- On the unrestricted 71-dimensional contact kernel, the full `V2`
  coordinate projection has rank 27 and kernel dimension 44.  Thus a large
  no-`V2` mixed-cycle space genuinely exists at `m=5`.

Reproducer:
`python3 .experiments/f101_m5_top_centered_affine_fibre_6900.py`.
Canonical-output SHA256:
`630978e46b7ad96a554072473a6abe5e6b2c33def7af85039b115c6663699591`.
Script SHA256:
`a46ffb6d59f7fd43e934ca077db362c4eeca35b25ec22241c31b2cecd11b0608`.

## Exact m=6 receipt

Parameters are `(10,4,7,6,42,1,1,8,12)`.

- Grades `<=J` have 3582 source columns and contact rank 3582: again the
  lower contact map is injective.
- Adding 642 grade-nine columns gives 4224 columns, rank 4180 and
  contact-kernel dimension 44.  The top shell contributes 598 new contact
  directions.
- There are 25 visible centered top shapes.  The canonical family contains
  23 of them:

```
Z  * P_8(V,Z)
+ V1 * Z^2 * Q_6(V,Z)
+ V2 * Z^2 * R_6(V,Z).
```

- The canonical 23-shape constraint leaves kernel dimension 21 and vertical
  image rank 12.  It contains all three right-hand sides and has affine fibre
  dimension 9.
- The canonical no-`V2` sixteen-shape family has kernel dimension zero.
- Even allowing the 17th non-`V2` visible shape `V1*V^7*Z` only gives kernel
  dimension/image rank `6/6`; every `Fi` still has defect one and the joint
  defect is three.
- On the unrestricted 44-dimensional contact kernel, the `V2` projection
  has rank 38 and kernel dimension 6.  Thus `V2` does not detect every cycle,
  but its kernel maps to a vertical six-space disjoint from all three exact
  target directions.  “`V2` is target-load-bearing” is the accurate claim.
- Setting the entire top shell to zero gives kernel and vertical-image
  dimension zero.  Adding the canonical top support enables twelve vertical
  directions and closes all three targets.
- Every one-coordinate ablation of the canonical 23 shapes loses joint
  target containment.  Twenty-two removals give joint defect three; removing
  only terminal `V^8*Z` leaves dimension/image rank `11/11` and joint defect
  one.  Hence canonical23 is inclusion-minimal **among its own subsets**;
  this does not rule out replacement by shapes outside canonical23.

Reproducer:
`python3 .experiments/f101_m6_top_centered_affine_fibre_6900.py --table`.
Canonical-output SHA256:
`8ba52189959a9ff2fbefb6d080a4b3d2864641a495c6d2a48da729a6b18dcab0`.
Script SHA256:
`17c9c603ac200e683f3333461bd33c0805d9dcb29f6f76f3836035755587a3f7`.

## The exact three-parameter m=6 operator

Write

```
V  = Y - QZ,
V1 = R - Q'Z,
V2 = S - Q''Z,
Lambda = product_{a=0}^6 (X-a),
Xi = product_{e=7}^9 (X-e),
Q = Xi^2.
```

The script deterministically extracts sources `S0,S1,S2` satisfying
`C(Si)=0` and `J(Si)=Fi`.  Therefore, for a parameter triple
`f=(f0,f1,f2)`,

```
S(f) = f0*S0 + f1*S1 + f2*S2
```

is one exact F101-linear right inverse on the target three-space.  Its top
shell has the single shared form

```
sum_y C_y(f;X) V^y Z^(9-y)
+ V1 * sum_y B_y(f;X) V^y Z^(8-y)
+ V2 * sum_y A_y(f;X) V^y Z^(8-y),
```

where each coefficient polynomial is the same linear combination of the
three basis polynomials printed by `--dump-lifts`.  All three basis RHS have
identical degree and common-`Lambda` divisibility profiles:

| family | `(y, degree, common Lambda valuation)` |
|---|---|
| pure `V` | `(0,55,6),(1,49,3),(2,43,2),(3,37,1),(4,31,0),(5,25,0),(6,19,0),(7,13,0),(8,0,0)` |
| `V1` | `(0,50,4),(1,44,3),(2,38,2),(3,32,1),(4,26,1),(5,20,1),(6,14,0)` |
| `V2` | `(0,51,5),(1,45,4),(2,39,3),(3,33,2),(4,27,2),(5,21,1),(6,15,0)` |

Thus the degree recurrences are exactly `-6` per `V` step until the terminal
pure coefficient; no common `Xi` divisor occurs.  The terminal `V^8*Z`
coefficients for `(F0,F1,F2)` are `(64,100,96)`.  The complete coefficient
arrays, factor profiles, and stable hashes are emitted by the script.

The deterministic raw lifts are dense because the chosen FLINT gauge is not
optimized:

- `F0`: 3941 nonzero raw terms,
  SHA256 `5ff2d843f8e29e0605eed314b534b6362b93ff2bc34d004a3ee0571f5930e556`;
- `F1`: 3982 terms,
  SHA256 `6ecfd282ede194d0745f8afdd43a47487c3b0773675d63a2c5cbe68360676c65`;
- `F2`: 4006 terms,
  SHA256 `b1aa9afc58987d536be17af89ceda4a1febf380fe701994ae8aadffc59c9741f`.

This proves one exact linear operator in this fixed chamber.  It does **not**
yet give a symbolic formula uniform in nodes, offsets or `m`; consistency of
factor profiles is evidence for such a formula, not the formula itself.

## Phase change and route verdict

The exact progression in this fixed chamber is:

| multiplicity | first-shell full kernel | no-`V2` kernel | target status |
|---:|---:|---:|---|
| 5 | 71 | 44 unrestricted; 17 in canonical no-`V2` core | green |
| 6 | 44 | 6 unrestricted; 0 in canonical no-`V2` family | red without `V2`, green with canonical23 |
| 7 | 0 | 0 | first shell red |

The independent `m=7` receipt has 5260 grade-`<=J` columns/rank 5260 and
6119 grade-`<=J+1` columns/rank 6119, so the first shell has no contact cycle
at all (individual defects `(1,1,1)`, joint defect three; receipt hash prefix
`a65d2dbd`).  Do not extrapolate the m5 or m6 shape formulas toward the target
multiplicity.  At the active fixed cap this route dies already at m7.

The necessary pivot is therefore not “formalize canonical23”.  A scalable
argument must change the filtration/support budget, couple multiple shells,
or find a covariant identity which survives the rank extinction.  Adding
more standalone weighted-order generators is not enough: an exact full
weighted-order-five agreement-cycle test at m5 retained joint defect three.

## Earlier banded-state audit and process correction

The passive-`Z` polynomial-matrix audit in
`f101_order4_banded_smith_popov_6900.py` explains the earlier false lead.
For the full eleven weighted-order-four carriers at m4 it finds polynomial
rank 22, Smith valuations `3^3,4^6,5^9,6^4`, image degrees
`4^9,5^9,6^4`, and right-kernel indices `1^1,2^10`.  But the same literal
module has polynomial ranks 29 at m5, 32 at m6 and 33 from m7 onward.  The
lower-grade quotient audit likewise gives the eight-carrier ranks
`15,20,23,24` at m4,m5,m6,m8.  The rank-22 coincidence was a small-m phase,
not a uniform 22-state theorem.

The corrected workflow is:

1. test a proposed carrier on the first nonvacuous bordered target before
   interpreting its Smith count;
2. impose support conditions on the complete affine fibre, never on one
   canonical lift alone;
3. measure the lower/top Schur interface and the exact target quotient;
4. sweep the adjacent multiplicity immediately; and
5. stop a route when its contact kernel becomes zero rather than polishing
   a small-m pattern.
