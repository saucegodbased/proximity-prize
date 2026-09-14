# Full187 pure face: exact two-generator contact basis

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production or
submission file is changed.

## Result

The unbounded pure-face contact module has a compact exact basis. Let `G` and
`E` be the agreement and error locators, so `GE=X^N-1` and `gcd(G,E)=1`.
For the two graph values `Y=0` on `G` and `Y=1` on `E`, put

```text
A = E Y,
B = G (Y-1).
```

Then the radical graph ideal is exactly

```text
I = (G,Y) intersect (E,Y-1)
  = (G,Y)(E,Y-1)
  = (A,B).
```

The first equality is the literal two-value graph. The second holds because
the two ideals are comaximal. For the last equality, `A` and `B` are visibly
in the product, while they recover the other two product generators through

```text
E B - G A = -GE,
u Y B + v (Y-1) A = Y(Y-1),   where uG+vE=1.
```

All graph-point maximal ideals are pairwise comaximal. Consequently, total
Hasse contact order 60 at every point is exactly the ordinary power

```text
I^60 = ((EY)^i (G(Y-1))^(60-i) : 0 <= i <= 60).
```

This supplies an explicit 61-row `F_p[X]` generating family for the complete
unbounded pure-face contact module. It is the missing soundness/completeness
input that a shifted-Popov reducer needs; no generic syzygy discovery is
required for this face.

The literal affine generator matrix has also been reduced exactly. Starting
from coefficient rows

```text
[0,E], [-G,G]                 with shift [0,W],
```

16,196 full-quotient Euclidean row reductions produce a weak-Popov basis
with

```text
row 0 component degrees       (196608, 65535)
row 0 shifted degree / pivot  (196608, constant position)
row 1 component degrees       (196607, 65536)
row 1 shifted degree / pivot  (196607, Y position)
sum of shifted degrees        393215 = N+W
determinant                   GE = X^N-1.
```

This is the exact target-scale starting point for reducing the 60th
symmetric power. It avoids first expanding 61 rows whose coefficients have
degrees up to 10,824,780.

## What remains load-bearing

The 61 raw generators are not themselves inside the Full187 tapered source
window. Their high weighted terms must cancel during shifted reduction.
Moreover, the two affine Popov degrees cannot simply be multiplied by 60:
power-ideal S-polynomials can lower the minimum degree (this occurs already
in the exact small controls). Thus this result does not prove either
membership or nonmembership of the fixed F3 boundary. The remaining task is:

1. form/reduce the 60th symmetric power of the two affine Popov rows,
   retaining the exact S-polynomial cancellations;
2. include permitted `Y` shifts through degree 82 and impose the literal
   tapered coefficient shifts;
3. test membership of the structured boundary residue frozen in `2bd2ce2`.

This narrows the pure-face theorem obligation, but it is not a Full187 F3
lift, four-packet bridge, score, candidate, build, comparator result, or
submission.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=3221225472 --cpu=600 -- \
  python3 -B .experiments/full187_pure_face_two_generator_basis_6900.py
```

Recorded literal-target receipt:

```text
gcd(G,E)                           1
Bezout coefficient degrees        81730, 180412
compact power-basis rows           61
affine Euclidean reductions     16196
affine row hash                  e1c0ca4e32500d7c5bbeaf83b7d80b8b58362444ea4fb8a47218e1e84137f98f
canonical sha256                1c6980ed5f4b6720b5c0b4e8946f10fb02d8b8123ce34c2061d83736a5be4bff
peak RSS                        170004 KiB
```
