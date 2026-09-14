# Full187 q26 versus complete-depth projection: exact rank STOP

Date: 2026-09-14 UTC.  Scope: the single active/passive sector containing the
f=8,q=26 fringe, after commit `2d678e8`.  Lower-6900 research only; no
production or submission files changed.

## Verdict

The ninth finite difference does **not** add a cancellation to the stronger
complete-depth projection.  It only changes the representative of each of
the eleven q26 quotient classes.

The exact target-field ranks are

```text
d=29, passive seed=53
physical complete-depth source jets q=0,...,25: 187*26 = 4,862
rank of those 4,862 columns:                         4,862
append the eleven y=8, r+s=21, q=26 blocks:         +11
augmented rank:                                      4,873
```

Thus:

1. the complete-depth physical source matrix is injective in this sector;
2. it has no source nullspace in which to hide the 99 FD jet changes;
3. every one of the eleven q26 blocks is nonzero and independent modulo the
   complete-depth image;
4. replacing, rather than superposing, the per-stream prescriptions cannot
   preserve all q<=25 cancellations while also cancelling q26.

Decision:

```text
RED_Q26_TARGETS_EXTEND_COMPLETE_DEPTH_AGGREGATE_IMAGE
```

This is a local STOP for integrating FD9 with `2d678e8`, not a STOP for the
whole 6900 proof.

## 1. Exact sector and provenance

Use the actual benchmark field

```text
F_p, p = 2,130,706,433,
```

and contact variables

```text
A = E + T*R - T^2*S/2,
U = E - T^2*S/2.
```

The affected homogeneous sector has active degree 29, passive seed 53
(absolute passive exponent 2674), contact cutoff 60, slope cap 21, and
curvature cap 10.  Its 187 physical shapes are

```text
T^q A^y R^r S^s,
y+r+s=29, y>=8, r+s<=21, s<=10.
```

For every one of these shapes the exact complete-depth window is 26 jets, so
commit `2d678e8` uses precisely q=0,...,25.  The eleven fringe targets are

```text
T^26 A^8 R^(21-s) S^s,       s=0,...,10.
```

The executable expands every physical column literally and checks all 5,049
columns q=0,...,26 against the adapted-coordinate construction.  The q<=25
source block has exactly 592,636 literal contact entries; the eleven q26
targets have 495 literal entries.  No separated-stream or symbolic-origin
independence is assumed.

## 2. Why the adapted rank is the raw contact rank

Factor `A^8`.  Index the residual `(21,10)` flag by ordinary pairs `(b,c)`:

```text
Y^8 * Y^(21-b-c) R^b S^c,
b+c<=21, c<=10.
```

There are 187 such pairs.  Put

```text
h   = 21-b,
e   = min(h,10)-c,
rho = h-min(h,10).
```

The source-side adapted basis is

```text
B_(b,c) = Y^8 R^b (Y-T*R)^rho
          (Y-T*R+T^2*S/2)^e S^c.
```

Expanding it in ordinary source monomials gives coefficient one at `(b,c)`;
every other pair `(b',c')` has `b'+c' > b+c`.  Hence this is an exact
unitriangular change of basis over `F_p[T]`.  The script constructs and
two-sided-checks all 187 inverse expansions.  The inverse has 8,503 nonzero
T coefficients and maximum T degree 31.

Under contact substitution,

```text
B_(b,c) |-> A^8 R^b U^rho E^e S^c.
```

Its unique minimum-weight monomial has valuation

```text
v_(b,c) = 8 + 2*rho + 3*e.
```

Therefore its coefficient survives exactly modulo

```text
T^(60-v_(b,c)).
```

The 187 truncated adapted coordinates have total dimension 5,797.  Literal
expansion independently verifies the unique pivot, sign `(-1/2)^rho`, active
degree 29, and truncation cap for every generator.  This proves the 5,797-row
adapted matrix computes the same rank as the raw 11,748-row contact matrix;
it is not a heuristic compression.

## 3. Exact rank and dual witnesses

Deterministic sparse Gaussian elimination over the actual target field gives

```text
source matrix:       5,797 x 4,862
adapted nonzeros:    196,542
rank:                4,862
nullity:             0
maximum live column: 185 nonzeros
```

Appending the q26 targets increases rank one at a time.  In adapted
coordinates each target is the singleton

```text
((b,c),26), where (b,c)=(21-s,s).
```

The script constructs eleven exact cokernel duals.  Their supports range from
104 to 136 adapted rows.  Each dual annihilates all 4,862 physical source
columns and evaluates as its corresponding standard basis vector on the
eleven targets.  Consequently the `+11` rank result has independent explicit
certificates, not just an elimination counter.

The earlier grouped SCC gate found one rank-3 chosen 4x4 pivot minor.  That was
not a full-column dependence: alternate unmatched contact rows restore the
rank.  The rectangular calculation here is the correction.  This sector is
source-injective even though the separate global residual-row audit is not
row-surjective and must remain block-correlated.

## 4. What FD9 actually does in this quotient

For each `s`, the ninth difference is the exact identity

```text
T^26 A^8 R^(21-s)S^s
+ sum_(k=1)^9 (-1)^k binom(9,k)
    T^(26-k) A^(8+k) R^(21-s-k)S^s
= -T^17 A^8 R^(12-s) U^9 S^s.
```

Every term in the sum is one of the q<=25 complete-depth source columns.
Hence, modulo their aggregate image,

```text
[-T^17 A^8 R^(12-s)U^9S^s]
  = [T^26 A^8 R^(21-s)S^s] != 0.
```

The eleven `U^9` residues are therefore exactly the same eleven independent
q26 classes.  FD9 cancels the degree-at-most-eight contact heads of a chosen
representative, but removes **zero** dimensions from the complete-depth
capacity quotient.

This also explains the physical-coordinate collision.  The 99 FD jets have
orders 17,...,25 and are already used by `2d678e8`.  Since the complete-depth
source matrix has nullity zero, changing any of them necessarily changes the
q<=25 image.  There is no aggregate-nullspace repair.

## 5. Safe integration choices

There are only two honest ways forward from this local result:

1. Keep `2d678e8` in this sector and treat the eleven q26 classes as genuine
   residual correlated blocks.  FD9 gives no quotient reduction.
2. Retain the weaker `7504148` projection in this affected sector.  Its low
   prescriptions end at `13-k` on the 99 FD coordinates, so jets `26-k` are
   available.  FD9 may then be used as a representative trade, but the eleven
   resulting `U^9` blocks still require an independent correlated-capacity
   argument; they are not discharged by the trade itself.

For option 2, after an arbitrary weak-Pascal section the actual common q26
coefficient is

```text
R_s = binom(61,8) U1^53 H26(C_s)
    + sum_(f=8)^57 binom(f,8) U1^(f-8) H26(P_(f,s)).
```

The universal prescription is

```text
H_(26-k)(Q_(k,s)) = (-1)^k binom(9,k) R_s.
```

This includes 51 provenance contributors per stream.  Using only the `C_s`
term silently assumes all unprescribed `H26(P_(f,s))` vanish.

## 6. Reproduction

```bash
python3 -B .experiments/full187_q26_complete_depth_rank_6900.py
```

Recorded run:

```text
exit 0; elapsed 9.3 s; peak RSS 53,628 KiB
canonical sha256 9a92f04f3063f9b5f0f5d204c83edbe09231ff4fc518aa81ba4f5482cab7cf8e
script sha256    c15371f217375cb169387346473a3e1b05c68a865c6783b953243bb93d7bff83
```

The exact fourth packet remains, without abbreviation,

```text
F3 = B*(Y-P-(Z-gamma)*q_H).
```
