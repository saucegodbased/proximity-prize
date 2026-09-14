# Full187 q26 adjacent-window Hankel rescue: GREEN

Date: 2026-09-14 UTC. Scope: the eleven `f=8,q=26` first-fringe
classes after the complete-depth projection in `2d678e8`. Lower-6900
research only; no production or submission file changed.

## Verdict

All eleven q26 classes left by the exact rank STOP in `4b5ea56` are globally
solvable by coupling the unused coefficient fringes of the adjacent physical
`P8` and `P9` polynomials. This is an exact frozen-target result over

```text
F_p, p = 2,130,706,433,       N = 262,144.
```

For every `s=0,...,10`, the residual high-coefficient Toeplitz map has full
row rank:

```text
s       0      1      2      3      4      5
rank 54146  54145  54144  54143  54142  54141

s       6      7      8      9     10
rank 54140  54139  54138  54137  54136
```

Each rank is certified independently by an exact nonsingular Hankel minor of
the same size. The right-hand side is arbitrary in `F_p^N`, so this solves
the actual correlated q26 common coefficient, including all terminal-`C` and
already-selected-higher-`P_k` contributions. It does not assume those terms
are independent or zero.

Decision:

```text
GREEN_ALL_ELEVEN_Q26_FIRST_FRINGES_BY_ADJACENT_P8_P9_HANKEL
```

The next gate is the retained multi-contact/multi-Hasse tail cascade. This
receipt does not claim the full Full187 confluence or a packet lift.

## 1. What this changes relative to the local q26 STOP

Commit `4b5ea56` established, in the active-29/passive-53 contact sector,

```text
complete-depth physical columns q=0,...,25:  4,862
exact source rank/nullity:                     4,862 / 0
eleven appended q26 blocks:                    rank gain 11.
```

Thus the ninth finite difference cannot be superposed inside that physical
source box. Its whole correlated identity is nevertheless exact:

```text
T^26 A^8 R^(21-s) S^s
 + sum_(k=1)^9 (-1)^k binom(9,k)
     T^(26-k) A^(8+k) R^(21-s-k) S^s
 = -T^17 A^8 R^(12-s) (E-T^2*S/2)^9 S^s,

A = E + T*R - T^2*S/2.
```

Every term in the sum is in the q<=25 source image. Therefore, in the
complete-depth quotient, the entire `U^9` polynomial on the right is exactly
the corresponding q26 class—not eleven separately assigned adapted
monomials. The executable reruns the literal integral finite-difference check
and all eleven whole-polynomial Order2 factorizations (each direct and
factorized expansion has 126 terms).

The new construction does not modify those q<=25 source columns. It uses the
coefficient-window kernels that remain after their jets have been fixed.
Consequently it resolves both representatives of each class: the direct q26
block and the whole `U^9` residual.

## 2. Exact adjacent physical sources

Fix `(r,s)=(21-s,s)`. Use

```text
P8(X) Y^8 R^(21-s) S^s Z^2674,
P9(X) Y^9 R^(21-s) S^s Z^2673.
```

Both have total degree 2703. Their active degrees are 29 and 30, strictly
below `J=82`; they satisfy `r+s=21` and `s<=10`. Their exact strict
coefficient windows are

```text
width(P8) = 7,023,742+s = 26N + (207,998+s),
width(P9) = 6,892,671+s = 26N + ( 76,927+s).
```

After the complete-depth section has fixed Hasse jets 0 through 25, every
legal preserving variation is of the form

```text
delta P8 = Omega^26 A_s,       deg A_s < a_s = 207,998+s,
delta P9 = Omega^26 B_s,       deg B_s < b_s =  76,927+s,
Omega = X^N-1.
```

The degree inequalities are strict:

```text
deg(delta Pi) <= 26N + fringe(Pi)-1 = width(Pi)-1.
```

At every domain node `x`, all Hasse jets below 26 vanish and

```text
H_26(Omega^26 V)(x) = (N*x^(-1))^26 V(x).
```

This diagonal is nonzero. At contact degree eight, `P8` contributes with
scalar one and the one-omission term of `P9` contributes
`binom(9,8)u1=9u1`. Removing the common diagonal gives the exact equation

```text
A_s + 9*u1*B_s = arbitrary q26 residual_s.
```

The scalar 9 is invertible (`9^-1 = 946,980,637 mod p`). Distinct `s` use
distinct physical `P8/P9` coefficient polynomials, so the eleven equations
can be solved simultaneously.

## 3. Toeplitz reduction and exact certificates

Pass from node values to coefficients in
`R=F_p[X]/(X^N-1)`. The first `a_s` coefficients are free through `A_s`.
The remaining

```text
m_s = N-a_s = 54,146-s
```

coefficients must be supplied by multiplication by the literal frozen `u1`.
The resulting rectangular map has shape

```text
m_s by b_s = (54,146-s) by (76,927+s)
```

and entries

```text
Toeplitz[i,j] = U1[a_s+i-j].
```

Its full coefficient range is always `[131072,262143]`, because

```text
a_s-b_s+1 = 131,072
```

for every stream. Select the final `m_s` input columns and reverse them. The
square minor is Hankel on the frozen sequence beginning at `U1[131072]`.
For each `s`, FLINT Berlekamp--Massey was run on the exact `2m_s`-term
sequence. It returned

```text
linear complexity = m_s,
remainder degree  = m_s-1,
both connection endpoints nonzero.
```

By the Hankel/Berlekamp--Massey determinant criterion, the selected
`m_s x m_s` minor is nonsingular. This is checked separately for all eleven
nested prefix lengths; a result for only the largest minor is not reused as
an assumption for the smaller ones.

Frozen `u1` coefficient-vector SHA-256 (packed little-endian u64):

```text
7751b961f73d2eec02dae9d43a19e5135fbd4c2456b0560894e79e59f92e0803
```

Representative exact certificate hashes:

```text
s=0,  m=54146
sequence   63a91766c7b0655ad4a92f90e6f7e00cabb83727d3ca35b037c1e5cf5d3d6c41
connection e609c1ac1c698924c41358e221b475157787a864318e88e8164f4812ca7ffb6e
remainder  c6bd55279bb926c3f5b7618ed47b1188a8f45d5d1e52ca9c40d88df616c3daaa

s=10, m=54136
sequence   044ed55d625f52428ba79a5c838b9ed6115e9076b946fbb358a19ff56c7f6d2d
connection 453f33f01efe364e6392e25c130b56f8d21345f820cb2f060cbf011a2215404e
remainder  d0d603f28cb61410984a747a112fa5623f7f51cba9a9f85a60b84349d4ca4586
```

The executable emits all eleven sequence, connection, remainder, endpoint,
and selected-column receipts.

## 4. Exact tail audit

The construction preserves q=0,...,25 identically. The executable enumerates
346,060 structural local occurrences below q26 and verifies that each carries
a zero coefficient jet. It then retains and classifies all 315,326 possible
q26-and-higher occurrences:

```text
solved f8,q26,z2674 contact occurrences                    990
P9 full-contact f9,q26,z2673; next weight 35              605
lower-contact full-node; strictly larger passive Z     62,040
strictly higher Hasse weight                           25,905
positive-u0, hence agreement-zero/error-only          225,786
```

The 990 solved occurrences are the 45 contact monomials from each of P8 and
P9 in each of eleven streams. They combine through the one common equation;
they are not counted as independent targets.

The remaining terms are oriented as follows.

- The `P9 f9,q26` block has contact/Hasse weight 35, strictly after the
  solved weight-34 block in the adjacent-contact cascade.
- Every `q>26` block has strictly larger Hasse weight.
- A full-node term with contact degree below eight has passive exponent
  strictly greater than 2674 and enters the passive-raising triangular
  prefix/connecting reducer.
- Every other term contains a positive power of `u0`; it vanishes at all
  agreement nodes and remains in the error-capacity connecting map.

No tail is set to zero, assigned independent capacity, or silently omitted.
In particular, this GREEN result leaves the global multi-`f`, multi-`q`
confluence as the next proof obligation.

## 5. Scope and exact packet

This certificate is target-specific but uniform across all eleven q26
streams. It proves an exact first-fringe section, not a symbolic theorem for
arbitrary `u1`, not the rest of the coefficient-window cascade, and not a
four-packet lift.

The exact fourth packet remains

```text
F3 = B*(Y-P-(Z-gamma)*q_H).
```

## 6. Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=2147483648 --cpu=180 -- \
  python3 -B .experiments/full187_q26_adjacent_fringe_hankel_6900.py
```

Recorded run:

```text
exit 0; elapsed 19.9 s; peak RSS 184,828 KiB
canonical sha256 6389613e383344a60cc67f1f60952ab2277bcf6516fa9d6db2c5dea32d5b2e38
script sha256    a58aabd42a0f6f09d30527ac60be945f1143aa3cdb6c8ad6f3e91f685d74e548
```
