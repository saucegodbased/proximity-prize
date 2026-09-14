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

## What remains load-bearing

The 61 raw generators are not themselves inside the Full187 tapered source
window. Their high weighted terms must cancel during shifted reduction. Thus
this result does not prove that the fixed F3 boundary is in the tapered
module. The remaining exact task is:

1. represent the 61 generators as polynomial rows in the `Y^0,...,Y^82`
   coefficient module, including the permitted `Y` shifts;
2. shifted-reduce them with the literal caps `deg C_n<n(G-W)` and the
   `G^(n-60)` high-tail divisibilities;
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
canonical sha256                  57e80afc3458a1de4c3fb22d1c9348b8357370e89c90545681c4a21a5de0149d
peak RSS                          169916 KiB
```
