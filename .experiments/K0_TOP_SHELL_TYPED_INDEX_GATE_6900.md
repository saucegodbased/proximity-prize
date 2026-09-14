# K0 top-shell typed-index gate for lower 6900

Date: 2026-09-14 UTC

## Verdict

**GREEN for the exact arithmetic/source-shape gate; OPEN for the 47 by 47
adjoint-observability gate.**

The simultaneous top faces of the current literal raw source are

```text
h + y + r = 64
2h + r = 16
0 <= h <= 8.
```

They have the unique parametrization

```text
r = 16 - 2h
y = 48 + h.
```

For `g=180413`, `w=131071`, and constant cutoff `D=47g=8479411`, every
one of these nine shapes has exactly the same remaining widths:

```text
X width = D - (w-2)h - (w-1)r - wy = 90883
Z width = 3757 + 1 - h - r - y       = 3694.
```

In particular, every top face contains far more than 47 consecutive legal X
coordinates.  There is no cap-crossing obstruction at the proposed seed
shell, and the arithmetic is independent of `h`.

## Checked artifact

`K0TopShellArithmeticProbe6900.lean` mirrors the exact sigma-index formulas
`budget` and `yCount`, constructs the full dependent index, proves the two
face equalities, and proves that any interval with `a0+47 <= 90883` supplies
47 consecutive X indices.  It compiles with Lean 4.32.2 under `-j1 -M3500`.
Its printed axioms are only the expected foundational axioms
`propext`, `Quot.sound`, and (for one simp-based face theorem)
`Classical.choice`; there is no `sorryAx`, `decide`, or `native_decide`.

`K0RawIndexContactCore6900.lean` is the completed minimal extraction.  It
imports only `Mathlib` and reproduces the accepted relaxed
`budget`/`yCount`/`Index`/`exponent` definitions, proves all five encoded
source inequalities, and types the literal direct composite

```text
raw coefficients -> reconstruct -> localize -> flatEquiv
                 -> truncateOuter 47 -> full contactMap 47.
```

It also records the corrected low selector (`{1,R}` at every legal `Y,Z`,
subcritical `Y^y*S` at every legal `Z`, and critical `Y^47*S` at `Z<=1`) and
the separate, not-yet-selected `S*Y^46*R` connector with every source-legal
`Z`.

`K0TopShellAdjointSeed6900.lean` now imports that minimal core and carries the
same constructor against `K0RawIndex 180413`.  Both it and the arithmetic
probe compile under the capped checker.  The core's printed theorem axioms
are exactly `propext`, `Classical.choice`, and `Quot.sound`; the top-shell
arithmetic theorems use subsets of that list.  No aggregate rebuild is
needed, and none is claimed.

## What this does not prove

The arithmetic width is not the missing global theorem.  The next hard gate
must expand `k0RawLocalContact_basis` on these literal indices and prove that
one specified 47-coordinate Hasse observation block is unitriangular over
the target field.  It must then propagate through every `budget`/`yCount`
seam without:

- using an index outside the raw source;
- replacing the full source by the contact-invisible `weightedTerm` family;
- assuming `gr(ker)=ker(gr)`;
- dropping a low-degree quotient defect; or
- silently changing `(s,L)=(8,3757)` to `(6,5107)`.

The route is to be stopped immediately if the literal 47 by 47 block has a
zero/nonunit diagonal, if a competing term destroys triangularity, or if any
propagation seam lacks a typed neighboring raw index.

## Process consequence

The top seed is no longer an arithmetic uncertainty.  The uncertainty is now
concentrated where it belongs: literal contact observability and global
tapered confluence.  This avoids spending further cycles on broad dimension
counts or on monolithic Lean rebuilds.
