# Full187 terminal carrier trellis: exact overlap STOP and corrected gate

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Verdict

The original three-carrier trellis is false in the arbitrary-direction
chamber, even after allowing its **whole legal coefficient space and every
legal passive shift**. The order-four eight-carrier repair closes the first
F101 residual and its target coefficient CRT/width gate is green, but the
proposed repeated `24 x 24` selected-row Toeplitz proof is also false: the
physical rows selected by adjacent carrier delays overlap.

This overlap is not removed by the lower-grade source. In a fully legal
`n=4,m=8` chamber, two layers give 48 carrier columns of rank 48 modulo the
complete lower-grade base, while the selected-row projection has rank only
30. Thus all 18 selected-invisible modes survive the base quotient.

There is nevertheless a useful replacement fact. After factoring the
individual delay `Z^(b+a+c)` from each input column, the `m=8` lowest-seed
coefficient matrix has column rank 24 and an explicit `24 x 24` minor of
determinant `32 mod 101`. This proves a full-vector leading injection in that
finite chamber. It does **not** prove that the forced residual lies in the
carrier module or that a finite polynomial solution has no top tail.

## 1. Whole-space STOP for the old three carriers

The exact discriminator uses

```text
F101,
(n,w,g,m,D,s,t,J,L)=(10,4,7,4,28,1,1,6,10),
Q=Xi_E^2, E={7,8,9}, error-direction offsets=(3,5,7).
```

For

```text
r  = (cQ+A Xi Lambda') mod Lambda,
B0 = -r+Lambda H,
B  = B0+cQ-2A Lambda Xi',
```

the whole legal family is exactly

```text
deg A <= 2, deg c <= 5, deg H <= 2,
dimension 3+6+3=12.
```

Exhaustiveness is certified inside the natural endpoint box
`deg(A,c,H)<=(2,11,2)`: its forbidden-coordinate map has rank six, so its
legal kernel has dimension 12 and equals the displayed coordinate space.

For matched directions the four shifts add ranks `4,8,12,12` and every
target defect is zero. For offsets `(3,5,7)`, every shift adds rank 12 but
the individual defects stay `(1,1,1)` and the joint defect stays one after
all shifts. An exact dual functional annihilates all 1,399 final source
columns and evaluates on `(F0,F1,F2)` as `(19,7,66)`.

Hence direction matching was a hidden premise of the old three-carrier
claim; more passive shifts cannot repair it.

## 2. What the order-four repair really establishes

The exact eight families are

```text
V^4, V^2 J1, Lambda V^3, Lambda V J1,
Lambda^2 V^2, Lambda^2 J1, Lambda^3 V, Lambda^4.
```

The offset grade-seven F101 correction decomposes into all eight families;
the three RHS are scalar multiples `(1,11,46)` of one compound correction.
The independent derivation is in commit `e0d8442`. The local one-layer
eight-carrier unit and the corrected Full187 uniform `deg p < 3e` Hermite
capacity are in commit `f44d26d`.

Those facts are genuine. The invalid inference was to repeat the local
selected block unchanged after `Z` shifts. A carrier `(a,c)` selects seed

```text
z=b+a+c+k
```

in shift `k`. Therefore rows from different `(a,c,k)` overlap.

## 3. Exact full-band overlap certificate

At one error node in the `m=4` F101 control, retaining all local contact
rows gives:

| Z layers | columns | distinct selected rows / rank | complete rank |
|---:|---:|---:|---:|
| 1 | 24 | 24 / 24 | 24 |
| 2 | 48 | 30 / 30 | 48 |
| 3 | 72 | 36 / 36 | 65 |
| 4 | 96 | 42 / 42 | 80 |

For two layers, the reproducer emits a deterministic 18-term input in the
selected kernel whose complete contact image has 23 nonzero rows, in seeds
`4,...,8`. Its coefficient and leakage hashes are

```text
coefficients 245879e68a1ca06e994f98bbaef13cc673ed7b098e9c123dfb4acb33846f7399
leakage      59ffd491db8dc2e2aaaf0d6973fad82eba0062a28fd0efbee29b2d5ba8e9406f
```

Thus selected-row cancellation is not complete-contact cancellation.

## 4. The lower-grade base does not kill the missing modes

Use the legal one-error chamber

```text
(n,w,g,m,D,s,t,J,L)=(4,1,3,8,24,1,1,10,14).
```

All 24 coefficient-jet carrier columns and their first shift are legal.
Exact quotient reduction gives

```text
lower-grade columns / rank       3729 / 3089
two carrier layers                  48
carrier rank modulo lower base      48
selected projection rank             30
selected-invisible surviving modes   18
```

This is the decisive process correction: neither the local one-layer unit
nor reduction by the earlier source justifies the selected-state recurrence.

The same chamber has base target quotient rank zero, so it is evidence about
carrier injection only. Any claim that this chamber demonstrates RHS
closure is vacuous.

## 5. Corrected leading-matrix evidence

Factor each column by its own minimum delay `Z^(b+a+c)`, retain that
coefficient, and forget the seed coordinate. The exact ranks for the 24
columns are

```text
m=4: 15,  m=5: 20,  m=6: 23,  m=8: 24.
```

At `m=8`, the first lexicographic 24-row minor has determinant `32 mod 101`.
Consequently the column-delay-normalized **complete vector-valued** carrier
matrix has a left-invertible constant leading block in this chamber. This
explains the exact rank-24 gain of every tested shift and is the appropriate
starting point for a Popov/Forney argument.

It still leaves two logically separate obligations:

1. prove that the nonvacuous forced terminal RHS is in the full vector-valued
   carrier module (all unselected contact channels included); and
2. prove finite endpoint closure, since a formal power-series inverse can
   create a top tail beyond the last legal shift.

Until both hold, the eight-carrier trellis is not an all-layer solution.

## 6. Artifacts and exact scope

```text
.experiments/f101_n10_full_shifted_three_carrier_trellis_gate_6900.py
.experiments/f101_order4_full_banded_carrier_image_gate_6900.py
.experiments/f101_n4_order4_terminal_quotient_state_audit_6900.py
.experiments/TerminalSeedToeplitzSolve6900.lean
```

The Lean file proves the ordinary scalar causal Toeplitz lemma: a nonzero
constant coefficient makes every finite scalar Toeplitz matrix invertible.
It is intentionally retained only as a conditional library lemma. The exact
overlap certificate shows that the carrier problem has not yet been reduced
to that scalar hypothesis.

Reproduce under the 4 GiB process cap with

```text
prlimit --as=4294967296 --rss=4294967296 -- \
  python3 .experiments/f101_order4_full_banded_carrier_image_gate_6900.py
```

The full-band payload/script hashes are

```text
canonical 4599b614aca02c32b225b4fd071c22d3fa9e16786fdaf133647af241bb9ce649
script    6164d50c3a9e54320b8545cd919f12ce9fda007c885dc2d1d0077fe6e17ffd51
```

The whole-three-carrier payload/script hashes are

```text
canonical 55e2d7fd3524d3c253cf08ed095eda6800e1f6ecdf282d8180545d71ba6b1db8
script    e1ac118bbaa6896570935b036540e70b26eb3cd4edf86b4c18e2ebe71cc6c816
```
