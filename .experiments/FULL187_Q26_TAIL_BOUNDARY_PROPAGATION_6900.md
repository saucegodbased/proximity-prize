# Full187 q26 induced-tail and boundary propagation

Date: 2026-09-14 UTC. Scope: the exact target-field P8/P9 correction from
`14b5109`, after its `f=8,q=26` diagonal has been solved. Lower-6900 research
only; production and submission files are unchanged.

## Verdict

The first induced q26 tail is not a new obstruction and not a packet prelift.
It has an exact complete-depth sink with zero boundary normal.

For each stream `s=0,...,10`, the unique smallest centered-grade term is

```text
P9, contact f=0, u1-Z choices h=0, q=26,
u0 exponent 9,
contact row (T,E,R,S,Z)=(26,0,21-s,s,2673),
centered grade 2694.
```

It is zero on all agreement nodes and, at an error node `x`, equals

```text
(N*x^(-1))^26 B_s(x) R^(21-s)S^sZ^2673.
```

The legal lower-grade source

```text
Q_s(X) R^(21-s) S^s Z^2673
```

has `Y`-degree zero and a complete 30-jet all-node Hermite section. Its q26
jet cancels the entire aggregate error-supported tail. Because its `Y` degree
is zero, it creates no lower-contact or positive-`u0` tail; only unprescribed
q>=30 coefficient jets remain, all in the residual strong-capacity region.

Both the original P8/P9 correction and this absorber have exact first
boundary normal `(0,0,0,0)`. Thus the induced augmented class is a terminal
contact class with `beta=0`; it cannot initiate any of `F0,F1,F2,F3` and is
consistent with the endpoint STOP in `4ad9979`.

Decision:

```text
GREEN  smallest q26 u0 tail has an exact complete-depth sink;
GREEN  its literal boundary class is zero;
STOP   later strong-capacity rows still require target-specific,
       cross-shape simultaneous confluence.
```

The last STOP is load-bearing. Commit `d35fcb4` falsifies arbitrary-C,
per-shape adjacent-cascade containment in a ratio-faithful finite model. This
note does not infer global containment from local capacity inequalities.

## 1. Literal tail expansion

For a variation of a physical source

```text
delta P_y(X) Y^y R^r S^s Z^z,
```

one structural local term is

```text
H_q(delta P_y)
  * binom(y,f) binom(y-f,h)
  * u0^(y-f-h) u1^h Z^(z+h)
  * A^f R^r S^s,

A=E+T*R-T^2*S/2.
```

After expanding `A^f`, the exact remaining scalar is

```text
multinomial(f;aE,cS,f-aE-cS) * (-1/2)^cS.
```

The executable enumerates every surviving term of the q>=26 P8/P9
variations over the actual field `p=2,130,706,433`. All combinatorial scalars
are checked nonzero, and every row retains `(T,E,R,S,Z)`, source stream,
coefficient order, `u0/u1` powers, and centered grade.

The literal occurrence census is

| class | occurrences | distinct rows | grade range |
|---|---:|---:|---:|
| solved f8,q26 diagonal | 990 | 495 | 2703 |
| u0-free, complete-prefix | 4,400 | 1,740 | 2703 |
| u0-free, residual capacity | 84,150 | 15,575 | 2703 |
| positive-u0, complete-prefix | 17,864 | 7,552 | 2694..2702 |
| positive-u0, residual capacity | 207,922 | 50,366 | 2694..2702 |

The 990 solved occurrences are two physical provenances—P8 and P9—on each of
45 contact monomials in each stream. They are one common block equation, not
990 independent equations.

## 2. Why the grade-2694 term is first and genuinely nonzero

Centered grade drops by exactly the positive `u0` exponent:

```text
output grade = 2703-(y-f-h).
```

The maximum possible exponent is nine and occurs only for the P9 term
`f=h=0`. The minimum coefficient order is q26. Therefore the eleven rows
listed in the verdict are the unique lowest-grade, lowest-contact-weight
operators. Each has scalar one and one physical provenance; there is no
cross-stream row cancellation at this first sink.

The selected right inverse in `14b5109` maps the `m_s=54146-s` dimensional
high quotient isomorphically to a nonzero polynomial `B_s` with

```text
deg B_s < b_s = 76927+s < 81731 = number of error nodes.
```

Evaluation of such a polynomial on all 81,731 distinct error nodes is
injective. Multiplication by `(N*x^-1)^26` is an invertible diagonal. Hence
the first-tail operator has exact rank `54146-s`, total rank 595,551 over all
streams. This proves it is not a syntactic term that always vanishes. An
individual packet-derived RHS may still land in a smaller subspace; no
arbitrary-C conclusion is drawn.

## 3. Exact complete-depth sink

For `(r,s)=(21-s,s)`, the P0 absorber has

```text
width(P0) = 8,072,310+s
          = 30N + (207,990+s),
complete qmax = 29.
```

Thus the canonical all-node Hermite representative for arbitrary jets
q=0,...,29 has degree below `30N`, strictly inside the source window. Set its
q26 node vector to the negative of the error-supported first tail and set the
other complete jets as required by the aggregate recurrence. This is exact at
all N nodes; it is not an error-only dimension count.

The source is legal:

```text
active degree  r+s = 21 < J=82,
total non-X grade 21+2673 = 2694 <= L=2703,
r+s=21, s<=10.
```

Since it contains no `Y`, local contact substitution is diagonal in contact
degree and cannot create a lower-grade `u0` term. Its canonical coefficient
polynomial can have q>=30 jets; those are retained and locally lie in the
strong-capacity residual.

## 4. Complete-prefix staircase for the remaining tails

For fixed `r+s=21`, the exact complete qmax values for physical contact
degrees f=0 through 9 are

```text
f:       0  1  2  3  4  5  6  7  8  9
qmax:   29 29 28 28 27 27 26 26 25 25.
```

Equivalently, the q>=26 complete staircase is

```text
q26: f<=7,   q27: f<=5,   q28: f<=3,   q29: f<=1.
```

Across all eleven streams this contains 220 `(f,q)` blocks and 2,200 literal
contact origins. The remaining 3,025 blocks contain 47,410 literal origins.
Every one satisfies the exact strong-capacity inequality. After removing the
now-solved `f8,q26` block, the smallest residual margin is

```text
2,382,346 at (s,f,aE,cS,q)=(0,9,0,0,26),
margin-errors = 2,300,615.
```

This is a local license only. The correct structural recursion is:

1. process centered grades downward from 2703 to 2694;
2. within one grade, process contact degree downward;
3. replace each complete `q<=qmax(f)` prescription by the one aggregate
   correlated block RHS;
4. retain every `q>qmax(f)` block for the target-specific residual section.

An `u0`-free term stays at its current grade and forms the unitriangular
Pascal contact recurrence. A positive-`u0` term moves to a strictly smaller
grade. The executable checks this orientation on all grades and source/contact
degrees. All 1,100 possible recursive physical source shapes are legal.

## 5. Boundary/packet quotient and cross-shape guard

The exact normal-coordinate map retains only raw monomials of total non-X
degree one. Every P8/P9 tail and every recursive absorber here has total
non-X degree in

```text
2694,...,2703.
```

Therefore its four-component boundary normal is exactly zero. This is a
calculation in the coupled contact/boundary operator, not merely a direct
support comparison. The resulting class has the form

```text
(terminal contact tail, beta=0).
```

For reference, every such recursive source also has outer `Z>=2664` and
retains `R+S>=21`, while exact packet contact rows have `Z<=1` and `R+S<=1`.
This secondary support invariant agrees with, but is not substituted for, the
boundary calculation and the `4ad9979` endpoint STOP.

The later rows are heavily cross-shaped:

```text
class                         rows hit by >1 stream / total rows
u0-free complete                         424 / 1,740
u0-free residual capacity             11,252 / 15,575
positive-u0 complete                    2,255 / 7,552
positive-u0 residual capacity          32,086 / 50,366
```

The executable emits full stream- and provenance-multiplicity histograms.
These collisions are potential target-specific cancellations, but no
cancellation is inferred from shared row keys alone. In light of `d35fcb4`,
the next exact calculation must insert the actual four-packet/carrier RHS and
rank the cross-shape aggregate, not section each `(r,s)` independently.

The exact fourth packet remains

```text
F3 = B*(Y-P-(Z-gamma)*q_H).
```

## 6. Reproduction

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
prlimit --as=1073741824 --cpu=60 -- \
  python3 -B .experiments/full187_q26_tail_boundary_propagation_6900.py
```

Recorded run:

```text
exit 0; elapsed 2.0 s; peak RSS 152,048 KiB
canonical sha256 0379511478e302eaa434ff84c5fe4a4f25ec38c93fbaae20ea84cece99928bcb
script sha256    871c4af4f0b8b07fca8430e1713b846def6e7ad43012ee86f20271c860330b46
```
