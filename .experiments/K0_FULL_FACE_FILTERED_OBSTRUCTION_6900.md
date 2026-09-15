# K0 full-face filtered obstruction and combined connecting map

Status: **GREEN exact linear algebra; target liftability and boundary remain
OPEN.**

## Why this layer is necessary

The target last-passive-face count produces an associated top-symbol kernel.
That does not automatically produce a relation for the complete contact map.
Writing the contact target as lower passive grades plus the new top grade gives

```text
             old source P       new face F
lower Wlo       old                 lower
top   Whi        0                   top
```

A vector `v : ker(top)` lifts precisely when `lower(v)` belongs to
`range(old)`.  The exact obstruction is therefore

```text
obs : ker(top) -> Wlo / range(old),
obs(v) = [lower(v)].
```

`K0FullFaceFilteredObstruction6900.lean` proves:

* `v in ker(obs)` iff `v` is in the true relative/liftable face;
* `StrictAtFace old lower top` iff `obs = 0`;
* if `q <= dim ker(top)`, then
  `q - dim(Wlo / range(old)) <= dim ker(obs)`.

Thus the target associated lower bound `q = 23,088,879` is useful, but a
bound on the lower-grade cokernel (or literal strictness) is still required.
No such premise is silently assumed.

## One class carrying both obstruction and boundary

Let `oldBoundary : P -> B` and `faceBoundary : F -> B`.  The single
mapping-cone class is

```text
combined : ker(top) -> (Wlo x B) / range(old, oldBoundary),
combined(v) = [(lower(v), faceBoundary(v))].
```

`K0FullFaceCombinedConnecting6900.lean` constructs this map and its canonical
projection

```text
(Wlo x B) / range(old, oldBoundary) -> Wlo / range(old).
```

The composite is definitionally `obs`.  Therefore:

* before liftability, the class records the lower-contact obstruction;
* on `ker(obs)`, it records the correction-independent relative boundary,
  because changing the old correction changes the boundary only by the
  boundary of an old contact-kernel vector.

The file also proves the factorization principle.  If `obs` factors through a
finite syndrome space of dimension at most `r`, then

```text
q - r <= dim ker(obs).
```

At the exact target error count `e = 81,731`, the hoped-for three-scalar
factorization would give

```text
3e = 245,193
23,088,879 - 245,193 = 22,843,686 liftable relations.
```

Both equalities are checked by `norm_num`; no earlier `32,389` error count is
used anywhere in these files.

## Exact falsification of the tempting small-syndrome premise

Commit `e522925` independently tests the literal formal contact, after
quotienting by the complete old contact image.  Its key results are:

```text
m6, L8 -> L9: old/top/full ranks = 4719/726/5445
               top kernel = 133, obstruction rank = 0

m4, L4 -> L5: old/top/full ranks = 539/180/734
               top kernel = 45, obstruction rank = 15, errors e = 2
```

The m6 success is vacuous: the obstruction is already zero.  The m4 chamber
is decisive against a uniform argument:

* the two epsilon-zero scalar error rows leave obstruction rank 15;
* all 32 epsilon-zero error rows leave obstruction rank 15;
* first-three and last-three scalar packets leave obstruction rank 15;
* more strongly, `15 > 3e = 6`, so the obstruction cannot factor through any
  syndrome space of dimension at most `3e` in that chamber.

This rules out deriving the target factorization from generic contact
triangularity, head rank, or a terminal packet alone.  A target-specific
identity/cancellation or a genuinely different one-spare-layer mechanism is
needed.

## Verification

Commands:

```text
LEAN_PATH=.experiments lake env lean \
  .experiments/K0FullFaceFilteredObstruction6900.lean -j1 -M2500

LEAN_PATH=.experiments lake env lean \
  .experiments/K0FullFaceCombinedConnecting6900.lean -j1 -M2500
```

Both finish in under four seconds after their small experiment imports are
built.  Printed axioms are only the expected `propext`, `Classical.choice`,
and `Quot.sound` (the integer receipt uses only `propext`).  There is no
`sorry`, `native_decide`, or nonstandard axiom.

The exact falsifier in `e522925` ran in 59.866 seconds at 1,303,256 KiB peak
RSS, with canonical hash
`ca707493786e4e837c7a9d6c1fea58c4e1e3e190de07351873deac1e5be6c218`.

