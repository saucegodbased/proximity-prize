# Full187 q26 / all-noncapacity projection integration

Date: 2026-09-14 UTC. Scope: exact targeted integration of commits `7504148`
and `d1620d8`; lower-6900 research only. Production and submission files are
unchanged.

> **Supersession guard (2026-09-14):** the GREEN statement below is only
> about the weaker `7504148` projection.  It does **not** extend to the
> complete-depth projection `2d678e8`, which prescribes every q=0,...,25 jet
> in this d=29 sector.  The exact corrective gate
> `full187_q26_complete_depth_rank_6900.py` finds source rank 4862/4862 and
> augmented rank 4873: all eleven q26 blocks remain independent in the
> complete-depth quotient.  See
> `FULL187_Q26_COMPLETE_DEPTH_RANK_STOP_6900.md`.

## Verdict

The ninth-difference q26 construction is a **strict extension** of the new
all-noncapacity Pascal projection `7504148`, not a duplicate of it.  This
sentence is deliberately not a claim about `2d678e8`.

```text
7504148 projects every non-strong-capacity terminal top block.
All 495 f=8,q=26 origins are already strong-capacity.
Therefore all 495 deliberately remain after that projection.
```

The two constructions reuse physical source polynomials, but there is no jet
conflict. Every one of the 99 FD9 source coordinates is already a lower-active
Pascal correction coordinate. On the `k`th layer, the existing projection
prescribes exactly jets

```text
0,...,13-k,
```

while FD9 prescribes jet

```text
26-k.
```

The separation is exactly 13 for every stream and every `k`. Both sets fit in
one depth-26 all-node Hermite residue, with minimum strict window slack
207,989. Thus the correct integrated implementation superposes the two jet
prescriptions in the same physical polynomial; it must not overwrite the
earlier low jets with the standalone FD9 zero convention.

This resolves one concrete physical-coordinate collision in the residual
capacity section: the eleven direct `P8,q26` demands are replaced by 99
high-jet assignments that coexist with the Pascal projection. It does not
prove that the entire residual capacity section is collision-free.

Artifact:

```text
.experiments/full187_q26_projection_integration_6900.py
```

## 1. Exact block left by the Pascal projection

For each `s=0,...,10`, consider the terminal shape

```text
(r,s)=(21-s,s),   y=61,
```

and its `f=8` contact block. The all-noncapacity executable chooses the direct
lower-active physical correction

```text
P8_s(X) Y^8 R^(21-s) S^s Z^2674
```

because its noncapacity Hasse orders are exactly

```text
q=0,...,13.
```

At `q=26`, however, all 45 local `(aE,cS)` choices in each stream have strong
capacity. The targeted replay gives

```text
11 physical common blocks,
495 expanded provenance origins,
495 distinct T/E/R/S/Z rows,
495/495 classified strong-capacity.
```

Their pre-error capacity margin ranges from 2,333,004 to 5,219,622; after
reserving all 81,731 error values, the slack is still 2,251,273 to 5,137,891.
Thus commit `7504148` is correct to leave this slice in its residual quotient.

Trying to add the q26 jet to the same direct `P8_s` would require depth 27.
Its strict window misses `27N` by 54,136 through 54,146 coefficients. This is
exactly the obstruction proved in `249b160`.

The common q26 coefficient after an arbitrary weak-Pascal section is not just
the original `C_s` coefficient.  It is

```text
R_s = binom(61,8) U1^53 H26(C_s)
    + sum_(f=8)^57 binom(f,8) U1^(f-8) H26(P_(f,s)).
```

This is 51 provenance contributors per stream (25,245 expanded provenance
terms over the eleven streams and 45 contact monomials).  The universal FD9
prescription is therefore

```text
H_(26-k)(Q_(k,s)) = (-1)^k binom(9,k) R_s.
```

The earlier specialized coefficient is valid only if the chosen section sets
all the unused `H26(P_(f,s))` jets to zero.

## 2. The 99 reused physical coordinates

FD9 uses

```text
P_(k,s)(X) Y^(8+k) R^(21-s-k) S^s Z^2674,
1<=k<=9, 0<=s<=10,
```

at Hasse order `26-k`. This gives 99 pairwise distinct source coordinates.
Each is also exactly the `P_f` coordinate used by the descending Pascal
projection for terminal shape `(21-s-k,s)` and contact degree `f=8+k`.

The targeted census finds, uniformly in `s`,

```text
k                  1  2  3  4  5  6  7  8  9
Pascal maximum q  12 11 10  9  8  7  6  5  4
FD9 q             25 24 23 22 21 20 19 18 17
difference         13 13 13 13 13 13 13 13 13
```

There are twelve unassigned orders strictly between the two ranges. Since
every correction window contains all of `A_26`, one polynomial can carry

```text
the existing Pascal residues at q<=13-k
+ the new FD9 residue at q=26-k
+ arbitrary chosen intermediate residues.
```

Linearity and separation by coefficient-Hasse order show that the extra FD9
jet cannot reopen any Pascal cancellation at `q<=13-k`. Conversely, the lower
Pascal jets do not enter the q26 row identity. This is also compatible with
the adversarial-symbol design of `7504148`: its recurrence was proved without
assuming a convenient value for any unprescribed higher jet.

All 4,455 low-contact-degree FD9 heads in these reused coordinates are
themselves strong-capacity. FD9 therefore supplies a relation *inside* the
residual capacity quotient; it does not silently reclassify them as a
noncapacity block.

## 3. Exact residual after the trade

Write

```text
A = contactY = E+T*R-T^2*S/2,
U = E-T^2*S/2.
```

For each stream, the original q26 block plus its nine FD9 heads is exactly

```text
-binom(61,8) T^17 A^8 R^(12-s) U^9 S^s.          (RES-s)
```

Thus the trade does not replace 495 rows by 1,111 unrelated residual
coordinates. It replaces eleven physical `contactY^8` blocks by eleven
structured `U^9` blocks. The executable independently decomposes `(RES-s)`
in the already formalized order-two flag

```text
(d,q,t)=(29,21,10),
```

whose relevant pivot weights are 43 through 52. Every ordinary source
monomial in that flag has at least `26N+207977` coefficient room.

This is the exact benefit to the simultaneous capacity problem:

- eleven impossible direct depth-27 assignments disappear;
- the 99 replacement assignments coexist with all prior Pascal low jets;
- their complete same-Z low-degree projections collapse to eleven structured
  order-two residues.

The limit is equally exact: some canonical order-two terms in `(RES-s)` have
outer Hasse order above 25, and all lower-passive/error/boundary tails remain.
No global simultaneous capacity section or four-packet Schur map follows yet.

## 4. Reproduction

```bash
prlimit --as=1073741824 --cpu=120 -- \
  python3 -B \
  .experiments/full187_q26_projection_integration_6900.py
```

Recorded run:

```text
exit 0; elapsed 1.1 s; peak RSS 17,208 KiB
canonical sha256 5c3b9ef0b82baa30d45d40b1f1c4b4f29fccf5808ac8924623533fa825c0af5e
script sha256    03fa7a2be309b605d38c5656d3c370ee2e5e64eb259c4be581e7446cd6e30cfc
```

Decision:

```text
GREEN_ONLY_VS_WEAK_750__STOP_VS_COMPLETE_DEPTH_2D678E8
```

The fourth packet remains exactly

```text
F3=B*(Y-P-(Z-gamma)*q_H).
```
