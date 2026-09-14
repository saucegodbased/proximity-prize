# Complete-kernel mutation descent: exact Gaussian STOP

Date: 2026-09-14 UTC. Scope: lower-6900 experiments only. Production,
submission, `score.txt`, and `radius.txt` were not changed. This is not a
6900 candidate and does not change the accepted 6806 result.

## Binary verdict

**STOP as a structural descent theorem.** The complete coupled CRT/Hermite
family does recover the whole literal filtered kernel in the frozen F97
control, but orienting enough boundary-preserving mutations to cancel every
illegal leader is exactly a global Gaussian elimination.

The predeclared shifted/tapered monomial order is a genuine well-order, and
every already-oriented move strictly lowers its greatest illegal monomial.
The problem is completeness, not well-foundedness. In the two exact controls,
the natural 6,044 boundary-zero CRT mutations expose only 1,155 and 834
distinct raw leaders, while their illegal images have dimensions 5,576 and
5,604. Consequently any complete rewrite basis must manufacture at least
4,421 and 4,770 new leaders by coupled cancellations. Computing those
cancellations is RREF/Gröbner completion of essentially the entire
8.3k-by-6.0k defect matrix.

There is therefore no cheaper legality-descent mechanism in this
presentation. A descending basis exists after global elimination, as it does
for every finite vector space with an ordered coordinate basis, but calling
that basis a mutation theorem would only rename the dense filtered-kernel
solve.

The same gate emits an intrinsic red control. At the off-domain boundary
probe, the matched word has filtered boundary annihilator

```text
(0,0,0,1).
```

The unconstrained ambient CRT boundary map has rank four, so the pure-`Z`
unit residual has an ambient lift. Its pairing with this annihilator is one,
so no boundary-preserving complete-contact mutation can make any such lift
source-legal. This is a nonzero normal-form/dual certificate, independent of
which unconstrained lift or boundary section is chosen. The retained-bad word
has no boundary annihilator and does legally lift all four probe units, but
the only complete construction found is the global illegal-row nullspace.

## 1. Audited starting point

The frozen gate
`ABR4_CRT_HERMITE_CAP_GENERATOR_RED_6900.md` uses

```text
k=F_97, N=8, primitive eighth root=33,
nodes=(1,33,22,47,96,64,75,50),
(w,g,m,D,s,t,J,L)=(3,6,4,24,2,1,7,7).
```

It compares the matched direction `u1=0` with the retained-bad degree-four
locator direction

```text
u1(A)=75+9A+18A^2+91A^3+A^4.
```

At every node, with

```text
T_x=X-x,
F_x=Y-u0(x)-u1(x)Z-T_x R+T_x^2 S/2,
```

the local contact kernel is

```text
I_x=(T_x^a F_x^b : a+3b>=m).
```

Pairwise comaximality and the NTT Hermite coordinates give the exact ambient
presentation

```text
Omega=X^N-1,
B=(1+Omega)^(1/N),
A=X/B,
F=Y-U0(A)-U1(A)Z-A(B-1)R+A^2(B-1)^2S/2,
J_m=(Omega^h F^b : h+3b>=m).
```

The old gate correctly showed that none of its 2,968 individually filtered
normal generators is legal, although the literal source kernels have
dimensions 471 and 444. That falsifies individual-generator filtering.

The first audit result here is that 2,968 columns are not a complete family
for **coupled** filtering. The old enumeration also imposed the ordinary
faces `r+s<=2` and `s<=1` on the normal `R,S` exponents. That is invalid after
coupling: rewriting an ordinary `Y` as

```text
Y=F+U0(A)+U1(A)Z+A(B-1)R-A^2(B-1)^2S/2
```

can move one unit of ordinary active degree into either normal derivative
exponent. The invariant finite normal simplex is instead

```text
b+r+s<=J,
b+r+s+z<=L,
0<=a<N,
0<=h<m,
h+3b>=m.
```

It has exactly 6,048 nonzero columns. No one of these 6,048 columns is
source-legal in either word. Since every literal `X` width is below
`D=24<N*m=32`, a nonzero `Omega^m` coefficient cannot hide inside one
ordinary source shape. Thus this finite simplex is the correct bounded
ambient family for the control. The exact rank comparison below independently
certifies its completeness.

## 2. Full coupled filtering

Let `A` send the 6,048 normal coefficients to ordinary monomial
coefficients. Split its rows into literal legal and illegal monomials:

```text
L : ordinary legal projection (2,187 rows),
U : ordinary illegal projection.
```

Then `ker U` is the space of all coupled ambient combinations whose ordinary
pullback is source-legal. The executable computes `ker U`, maps it through
`L`, independently rebuilds the literal contact matrix `C`, and checks

```text
C * L(ker U)=0,
rank L(ker U)=nullity C.
```

The exact results are:

| word | all ordinary rows | illegal matrix | `rank U` | `null U` | literal `rank C/null C` | coupled legal rank |
|---|---:|---:|---:|---:|---:|---:|
| matched | 10,528 | 8,365 x 6,048 | 5,577 | 471 | 1,716 / 471 | 471 |
| retained bad | 10,560 | 8,373 x 6,048 | 5,604 | 444 | 1,743 / 444 | 444 |

The joined ranks of the coupled images with the independently computed
literal kernels are respectively 471 and 444. Hence the spaces are equal,
not merely equidimensional evidence. Their exact matrix fingerprints are:

```text
matched illegal projection
  47c8a2cec49d7b63c02bc7ebcc3dc3201d91374bcb6d7b872210f2081ea0ee1e
matched coupled legal image
  88158c2fec7760c396c46186f25b06fd53c98820cf789fa82882a078d908750a

retained-bad illegal projection
  079d177e78db55a195ee71fbe0be4870391bbc176a2e0658df94406f789c12ff
retained-bad coupled legal image
  bbff4dea0a8e008854454849357b89a7fa55e5cacb115b93689234b73a9c3495
```

This is a genuine positive result about the finite presentation: allowing the
whole triangular normal simplex repairs the incomplete 2,968-column coupled
family and exactly recovers all 471/444 relations. It is not yet an algorithm
smaller than solving `ker U`.

## 3. Exact shifted/tapered order

For an ordinary monomial `X^a Y^y R^r S^s Z^z`, fix the descending
lexicographic key

```text
(a+3y+2r+s, y+r+s+z, z, s, r, y, a).                 (ORDER)
```

The first component is precisely the literal shifted `X` degree. Every
component is additive under multiplication, and the exponent tie-breakers
make the key injective. The associated ascending relation is therefore a
well-founded monomial order. `(ORDER)` was fixed before the raw-leader run;
only source-illegal monomials are eligible as rewrite leaders.

For any mutation, normalize its greatest illegal monomial and subtract it
from a current correction with the same leader. The next illegal leader, if
one remains, is strictly smaller in `(ORDER)`. So there is no cycle or
failure of the proposed measure.

This observation alone is tautological: it orients a supplied vector but
does not guarantee that a supplied set of mutations has a rule for the next
leader.

## 4. Complete boundary-zero mutation space

At the off-domain probe `X=2`, let `beta` evaluate the four coefficient
polynomials attached to the ordinary unit shapes

```text
(Y,R,S,Z).
```

The ambient `beta` map has rank four in both words. Pick any four independent
ambient columns as a section, and for every other normal generator subtract
its section lift. This gives 6,044 explicit boundary-zero contact mutations.
The executable uses the first independent columns only to make this raw
presentation deterministic; all full-space ranks and the dual obstruction
below are independent of that choice.

The filtered-kernel probe ranks are three and four. Because the 6,048
ambient columns are independent and the coupled filtered kernels have the
dimensions proved above, rank-nullity gives the exact illegal-image ranks of
the **entire** boundary-zero mutation space:

```text
matched:
  6044 - (471-3) = 5576,

retained bad:
  6044 - (444-4) = 5604.
```

Now take the greatest illegal monomial of each of the 6,044 raw mutations in
`(ORDER)`. The result is:

| word | nonzero raw mutations | distinct raw leaders | complete mutation-image rank | new leaders needed at least |
|---|---:|---:|---:|---:|
| matched | 6,044 | 1,155 | 5,576 | 4,421 |
| retained bad | 6,044 | 834 | 5,604 | 4,770 |

The maximum leader multiplicities are 26 and 29. Illegal supports range from
8 to 701 terms in the matched word and from 12 to 2,380 terms in the bad
word. Total raw illegal incidences are 669,515 and 1,604,158.

The leader deficit is rigorous. A triangular basis for a rank-`r` vector
space has `r` distinct pivot coordinates. If the raw presentation exposes
only `q<r` distinct leaders, at least `r-q` pivot leaders occur only after
cancelling equal raw leaders and reducing the resulting S-polynomials. Here
over 79% and 85% of the required leaders are manufactured rather than raw.

Thus the complete mutation closure does terminate, but constructing it is
the global Gaussian completion that the proposed route was meant to avoid.
No fixed carrier or solver-selected lift was used to reach this conclusion.

## 5. Intrinsic nonzero normal-form certificate

The matched filtered boundary image has exact annihilator basis

```text
ell=(0,0,0,1).
```

It annihilates all 471 literal filtered-kernel columns coefficientwise at the
probe. Let `e_Z=(0,0,0,1)`. Then

```text
ell(e_Z)=1 mod 97.
```

Because ambient `beta` has rank four, `e_Z` has an unconstrained CRT/contact
lift. Suppose a boundary-zero complete-contact mutation made any such lift
source-legal. Its result would lie in the literal filtered kernel and retain
boundary `e_Z`, contradicting `ell(e_Z)=1`. Therefore the illegal part of an
ambient `e_Z` lift represents a nonzero class modulo the complete
boundary-zero mutation image. This is a two-sided dual certificate, not the
failure of a canonical representative.

For the retained-bad word the filtered boundary rank is four and the
annihilator basis is empty. All four probe unit residuals, including the
three locator normals and the independent `Z1` direction, have some legal
lift. Existence does not supply a local rewrite: the 4,770 synthesized-leader
lower bound remains.

## 6. Target relevance and stop rule

The target Full187 problem needs exactly three locator residuals plus the
independent `Z1` class. This finite gate correctly distinguishes their
matched/bad behavior and proves that unrestricted coupled cancellation is
powerful enough in the small retained-bad control. It simultaneously removes
the hoped-for complexity reduction:

```text
complete normal simplex + tapered order
  does not imply
a pre-existing complete set of descending legality mutations.
```

At target scale there are 187 physical derivative channels and the terminal
shell is already the load-bearing part of a source with roughly
`1.63e14` columns. A method whose first finite instance needs RREF of an
8,373-by-6,048 illegal projection and synthesizes 4,770 hidden leaders has no
identified target-scalable certificate. The monomial order proves
termination only after a complete mutation basis is known; it does not
construct that basis or predict its leaders as caps change.

This does not falsify a future special recurrence for the four target
residues. It does stop **complete-kernel mutation descent** as an independent
route unless a new theorem supplies a cap-uniform, word-independent subset of
the synthesized pivots without computing the full filtered kernel. Do not
promote an RREF basis, canonical lift, or fixed order-four carrier list as
that theorem.

## Reproduction

From `yukon-6900-work`:

```bash
python3 -m py_compile \
  .experiments/complete_kernel_mutation_descent_f97_6900.py

prlimit --as=6442450944 --cpu=1200 -- \
  python3 .experiments/complete_kernel_mutation_descent_f97_6900.py

prlimit --as=6442450944 --cpu=600 -- \
  python3 .experiments/complete_kernel_mutation_descent_f97_6900.py \
    --raw-profile
```

The final full run took 265.77 seconds and peaked at 1,901,008 KiB. Its
canonical semantic hash was

```text
dd815eed27c92c18f438659dd69f258d0cec7267231dc26bb453174bbf1a2673.
```

The final raw-profile run took 15.32 seconds and peaked at 451,608 KiB:

```text
canonical SHA256
  49c175b6a9471d7a639a69082ef01e3d4015943b27d062b79c88485d001ba166
```

Both runs stayed well below the requested 6-GiB address-space ceiling. The
script imports the frozen literal translation routine through the audited
CRT/Hermite gate and performs all rank, nullspace, annihilator, and leader
computations exactly over `F_97`.

```text
script SHA256
  199f4658c0dd8e7620facadfbdbbb8b6be353111faa0a3d8ef9cd3036e8a6151
```
