# Full187 F3 pure boundary: explicit agreement section and error residue

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production or
submission file is changed.

## Decision

The prescribed pure-face boundary is not an arbitrary affine right-hand
side. It has the following exact, fully legal agreement-side section:

```text
K0(X,Y) = -R(X)^60 Y (Y-H(X))^59.
```

Its coefficient of `Y` is exactly

```text
H^59 R^60 = B,
```

the Full187 F3 boundary. At an `H` agreement node, the sixty factors
`Y,(Y-H),...,(Y-H)` give contact order 60; at an `R` agreement node, the
factor `R^60` does. Its coefficient of `Y^n` has degree

```text
60 deg(R) + (60-n) deg(H) = D - n(W+1),
```

so it lies strictly inside the required window `deg < D-nW`, with exactly
`n-1` spare coefficient positions.

Under the exact graph transform of `48b1270`, this becomes

```text
F0(X,V) = -R V (R V-1)^59.
```

Thus its transformed coefficient `C_n` is a scalar multiple of `R^n`, and
`deg(R^n)=n(G-W-1)<n(G-W)`. This gives a small structured base point for the
pure-face correction problem.

It is not already an error-contact solution. Around the error centre `Y=1`,
its `j`-th Y-Hasse residue is exactly

```text
rho_j = -R^60 (1-H)^(59-j)
          * (binom(60,j) - H binom(59,j-1)),   0 <= j < 60.
```

The executable evaluates these factored expressions on the literal Full187
target and proves that every one of the sixty residues is nonzero even
modulo `E`. The correction problem is therefore real, but its right-hand
side is now one explicit 60-row binomial vector rather than an arbitrary
149,567,730-dimensional target.

## Process consequence

Future multirow approximant gates should test membership of this exact
residue vector first. Proving an entire coupled contact operator surjective
is stronger than necessary and can repeat the earlier arbitrary-section
detour. A RED global-surjectivity test is not a blocker if this structured
right-hand side still lies in the image.

This receipt does **not** prove a pure-face correction, Full187 F3 lift,
four-packet lift, score, candidate, build, comparator result, or submission.

## Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=3221225472 --cpu=600 -- \
  python3 -B .experiments/full187_f3_boundary_section_residue_6900.py
```

Recorded literal-target receipt:

```text
all 60 residues nonzero modulo E
all 60 residue degrees             81730 = deg(E)-1
residue-sequence sha256            c54ab00570540d477be96db5ae685378ce8727bb0b3467c14b1dad988e33dc42
canonical sha256                   cc8e733e3e2395b53a2cc58b6464bcebd52c8f17b009ac1a28d696defef78484
peak RSS                           234776 KiB
```
