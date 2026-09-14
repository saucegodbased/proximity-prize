# m69 all-defect actual residual: W-positive; 3276-zero branch GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production and the
accepted lower submission are unchanged.

## Decision

The exact first-defect observation in `b1554c4` extends to **all 140,153**
rank-insensitive deficient physical coefficients in the m69 census:

```text
every literal incoming target excludes its current h=0 control,
every remaining terminal/direct term has strictly positive W power,
hence every incoming target vanishes wherever W=N0/E0 vanishes.
```

Scanning all positive direct powers, rather than only the first four, gives a
substantial new zero/live split. Every one of the 6,930 deficient shapes has
a genuine Hasse prefix of dimension at least `258868` at some positive power.
Consequently a **single positive-power channel** contains its individual
actual target whenever the numerator has at least

```text
262144 - 258868 = 3276
```

nodal zeros. The exact per-shape threshold is between `3218` and `3276`.
This replaces the first-defect-only two-channel threshold `134317` with a
uniform all-defect one-channel threshold `3276`.

This is not simultaneous confluence. The selected high-contact tails are
shared between equations. Separate solvability of all 140,153 equations does
not yet prove that one assignment realizes them together. The remaining
individual rational-rank branch is now only `0 <= nodalZeros(N0) <= 3275`,
but the shared-tail allocation problem remains for every branch.

## Exact incoming formula

Fix any deficient physical coefficient `(y,r,s,q)` and put

```text
A         = y+r+s,
terminalY = J-r-s,
J         = 94,
M         = 69.
```

The source coefficient before solving the current control is exactly

```text
binom(J-r-s,y) W^(J-(y+r+s)) C_q
  + sum_(h=1)^(M-y-1) binom(y+h,y) W^h U_(y+h,q).
```

The `h=0` term is the current coefficient being solved and is therefore not
part of the incoming residual. The exhaustive ledger checks:

```text
deficient coefficients                         140153
positive ordinary U terms                     7778831
terminal C terms                                140153
total incoming terms                           7918984

last ordinary power range                         25..68
terminal power range                              31..94
terminal minus last ordinary power                 2..26
terminal X^q H_q(C) dimension             127755..127842
```

All Pascal scalars are nonzero modulo `p=2130706433`. Every direct channel
also satisfies `1 <= depth <= q <= 68` with nonempty prefix. Commit
`34bcb23` independently checks, over the exact field, that every diagonal
Hasse weight in every such physical prefix is nonzero. Thus these are actual
prefix images, not nominal dimensions.

The stream receipt over all 7,918,984 incoming terms is

```text
51a0ec13e653975af381221092343631801446f26aab27df29e4257451435932
```

The Lean theorem `positiveIncomingResidual_eq_mul` factors an arbitrary
finite residual with exactly this power pattern as `W * (...)`.

## Rational normalization audit

The frozen multiplier here is exactly

```text
W = N0/E0,
```

not `N0/(X*E0)`. After cancelling the common factor `B` at a live node, the
formal DataEleven cross field is literally

```text
E0(i) * (d(i)U0(i)-c(i)U1(i)) = N0(i).
```

The Pascal contact expansion contributes ordinary powers of that wedge; it
does not introduce an X/Hasse shift. This also agrees with the reciprocal
monomial experiment: `E0=X^e,N0=1` gives `W=X^(-e)`.

Accordingly, clearing the physical square channel gives

```text
N0^2 * H = E0^2 * H2,
```

with no `X^2` factor. The `X^2` premise in the earlier experimental theorem
`M69RationalTwoPowerGate6900.short_square_relation_forces_zero` was not
derived from the advertised physical envelope and must not be cited as that
adapter. `physical_square_relation_forces_zero` proves the corrected coprime
implication. The no-wrap numerator cutoff remains `129449` because its left
degree `2*deg(N0)+3245` is still the binding side.

## Best positive-power prefix

For each deficient shape `(y,r,s)`, the executable uniquely maximizes

```text
rho_h = width(y+h,r,s) mod 262144,
1 <= h <= M-y-1.
```

Across all shapes:

```text
selected h range                         24..68
selected rho_h range             258868..258926
exact threshold N-rho_h               3218..3276
uniform threshold                           3276
```

Two endpoints are useful sanity checks:

```text
shape (39,14,10), first defect:
  h=28, depth=1, rho=258926, threshold=3218

shape (0,0,0), old zero-set countergate:
  h=67, depth=13, rho=258868, threshold=3276
```

The full 6,930-shape selection receipt is

```text
06103677a707314308aeb50cc4adfe5e98de7de6a036f7551e4f536803bf4dfd
```

and the selected-channel stream over all 140,153 `(shape,q)` coefficients is

```text
339f284fefc7cfd9a9aecef491439103f74490bf3c6320a20a3392b4fa5a11a4
```

## Why one channel suffices when z >= threshold

Let `Z={i | W(i)=0}`, `z=|Z|`, and let the selected positive exponent be
`h`. The actual target `T` is zero on `Z` by the common-W factor. On the live
set, `W^h` is invertible. If

```text
N-z <= rho_h,
```

Lagrange-interpolate `T/W^h` on the live nodes by a polynomial `A` of degree
less than `rho_h`. Then

```text
W^h A = T
```

on the live set, and both sides are zero on `Z`. The Hasse diagonal
isomorphism from `34bcb23` converts `A` into the actual source-tail
coefficient. `exists_positive_power_interpolant` formalizes the interpolation
argument for an arbitrary finite field/node set and arbitrary positive power.

Because every selected `rho_h>=258868`, `z>=3276` implies

```text
N-z <= 258868 <= rho_h
```

uniformly for every deficient coefficient.

## What this removes, and what it does not

The arbitrary-target zero-set counterexample in `cb97180` remains a correct
RED for universal surjectivity: at `(0,0,0)`, an arbitrary word supported on
127,730 zeros cannot pass through the `h=0` prefix of dimension 127,729.
But an actual incoming target is not arbitrary there; it is divisible by W
and hence zero on those nodes. The high `h=67` prefix then has dimension
258,868 and handles the entire complement with enormous slack.

So numerator zeros are no longer the main obstruction for actual individual
targets except in the tiny branch `z<=3275`. The honest unresolved gates are:

1. **small-zero rational containment:** prove the individual result for
   `z<=3275`, likely by a punctured cyclic/Padé argument;
2. **simultaneous confluence:** prove that the same higher-contact source tail
   can satisfy every lower equation that uses it;
3. **content-root/Live adapter and the lower-passive connecting tails:** this
   experiment is only the normalized scalar top system.

No candidate, score, or submission claim follows until those gates close.

## Process learning

The first-defect audit inspected only powers `h=0,1,2,3`, producing the weak
large-zero threshold `134317`. That was correct but locally myopic. The exact
width recurrence alternates low and high fringes; late direct powers approach
a near-full prefix. Scanning the entire already-available power range exposed
the `3276` uniform threshold immediately and cheaply. Future rank audits
should optimize over the whole structural channel set before escalating a
local deficiency into a global obstruction.

The enumeration streams hashes rather than storing 7.9 million records. It
ran below 40 MiB RSS, safely under the 24 GiB verifier ceiling.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=1073741824 --cpu=300 -- \
  python3 -B \
  .experiments/m69_all_defect_actual_residual_positive_power_gate_6900.py

env LEAN_NUM_THREADS=1 lake env lean -j1 -M3500 \
  .experiments/M69AllDefectActualResidualPositivePower6900.lean
```

Recorded bounded results:

```text
Python exit / peak RSS   0 / 38536 KiB
canonical SHA256         3132cddfe8b2d01b598559e087ac706de48a1205233e6e966468b998ea0e7763
Python source SHA256     7536f869901668c83439bac9026506183fd85786985e1fc5061b2d9248bc7cca
Lean source SHA256       a15b13249d77535d776cf9395231d13003ca2b03a81fccd521ec892f01a082a5
Lean exit                0
Lean axiom sets          [propext, Classical.choice, Quot.sound]
```

Neither artifact uses `decide`, `native_decide`, `sorry`, `admit`, or an
unsafe declaration.
