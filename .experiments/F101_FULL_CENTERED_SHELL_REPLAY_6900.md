# Full F101 centered correction replay: endpoint covariance, no homogeneous recurrence

Date: 2026-09-13 UTC. Scope: lower-6900 research only. This is a bounded
finite-field mechanism audit, not a target-scale theorem, candidate, score,
or production/submission change.

## Verdict

The complete canonical `F0/F1/F2` corrections do have two exact, compact
centered covariant boundary shells, but they do **not** form a homogeneous
one-carrier shell recurrence. The failure is already forced at the first
possible transition, grade `1 -> 2`: every RHS has a nonzero pure `Z^2`
coefficient at grade two, whereas multiplying its grade-one centered normal
frame by an arbitrary homogeneous linear carrier has zero pure tail.

Thus this replay identifies an exact inhomogeneous tail which any genuine
target-scale trellis recurrence must generate. It does not justify extending
the previously found grade-seven Wronskian packet down through grades `1..6`.

## Exact replay and integrity checks

The script replays the same deterministic F101 source-vector selection used
by the root grade-seven factor probe, for

```text
F101, (n,w,A,m,D,s,t,J,L) = (11,5,8,4,32,1,1,6,10),
G = {0,...,7}, E = {8,9,10}, P = gamma = 0,
Q = Xi_E^2.
```

It keeps the original contact-kernel checks:

```text
contact rank/nullity       1735 / 39
normal image rank             12
```

For every complete source correction it makes the exact triangular change

```text
V  = Y - Q Z,
V1 = R - Q' Z,
V2 = S - Q'' Z
```

using `nmod_poly` over `F_101`, expands back, and asserts literal equality
with the original complete source polynomial. No grade is discarded: grades
`0..7` are all clustered and factored after the reconstruction assertion.

The centered term counts, followed by the degree of the coefficient gcd, are:

| RHS | g0 | g1 | g2 | g3 | g4 | g5 | g6 | g7 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| F0 | 0/- | 1/24 | 5/8 | 7/0 | 9/0 | 10/0 | 10/0 | 3/0 |
| F1 | 0/- | 2/16 | 5/8 | 7/0 | 9/0 | 10/0 | 10/0 | 3/0 |
| F2 | 0/- | 3/8 | 7/0 | 10/0 | 13/0 | 15/0 | 14/0 | 3/0 |

In particular, the middle grades are not being hidden by a common agreement
locator factor: all coefficient gcds are `1` from grade three onward.

## First shell: the exact normal frame

Put `Lambda` for the agreement locator and set

```text
J1 = Lambda V1 - Lambda' V,
J2 = Lambda^2 V2 - 2 Lambda Lambda' V1
     + (2(Lambda')^2 - Lambda Lambda'') V.
```

The replay asserts the complete grade-one identities

```text
H1(F0) = Lambda^3 V,
H1(F1) = Lambda^2 J1,
H1(F2) = Lambda J2.
```

These are the literal three locator-normal covariants, not a visual factor
match. Their coefficient gcds are respectively `Lambda^3`, `Lambda^2`, and
`Lambda`.

## First exact recurrence obstruction

Each grade-one frame has no pure tail: it vanishes after setting
`V = V1 = V2 = 0`. Consequently, for *any* homogeneous centered linear
carrier

```text
a(X)V + b(X)V1 + c(X)V2 + d(X)Z,
```

the product with a grade-one frame also has zero `Z^2` coefficient. The
actual grade-two coefficient is nonzero in all three canonical corrections:

```text
[Z^2] H2(F0) = 13 (X+57) Lambda^4,
[Z^2] H2(F1) = 68 (X+31) Lambda^4,
[Z^2] H2(F2) = 62 (X+80) Lambda^4                 in F_101[X].
```

The script asserts these polynomials are nonzero and records their complete
factorizations. This is an exact obstruction to a homogeneous first-order
carrier recurrence beginning from the normal frame. It does not rule out an
inhomogeneous recurrence with a separately proved pure-tail injection; that
is precisely the missing condition now exposed.

## Last shell: the Wronskian packet survives the full replay

All three grade-seven shells have exactly the support

```text
V^4 Z^3,  V^3 Z^4,  V^2 V1 Z^4,
```

and the script recovers and asserts, independently for each RHS,

```text
H7 = V^2 Z^3 (c V^2 + C Lambda V Z + A Xi J1 Z).
```

The recovered degrees are uniformly

```text
deg c = 0,   deg A = 4,   deg C = 6.
```

So the two endpoint facts are compatible but different:

```text
grade 1: Lambda^3 V, Lambda^2 J1, Lambda J2;
grade 7: V^2 Z^3 (c V^2 + C Lambda V Z + A Xi J1 Z).
```

The primitive, dense middle shells and the explicit grade-two pure tail mean
there is no verified shell-to-shell continuation between them.

## Reproduction

```text
prlimit --as=4294967296 --cpu=120 -- \
  python3 -B .experiments/f101_full_centered_shell_replay_6900.py
```

The replay completes in about six seconds under the 4 GiB address-space cap.
The current receipts are:

```text
script sha256:    c0b2e305710397122e4a5fcb081133517d09855d7afb46c244472f4d1a6ec7e5
payload sha256:   407fa4cce6eabfdfd1eaecb1239a0780044f893834d598397c143918604c5985
```

`F101FullCenteredShellReplay6900.lean` proves the parameter-free normal-frame
and Wronskian assembly identities. The finite nonzero `Z^2` witnesses remain
in the exact capped `nmod_poly` receipt, where their field-specific
factorizations are checked.

## Consequence

This is a `STOP` for treating the complete canonical F101 correction as a
single homogeneous Wronskian/binomial ladder. The next lawful theorem is more
specific: derive an inhomogeneous pure-tail transition, with its literal width
bounds, and then show that it couples to the grade-seven Wronskian packet
without losing source legality. No target-scale conclusion follows from this
finite audit.

