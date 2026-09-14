# Full187 symbolic Pascal straightening and the A57 window STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This note corrects the
all-active conjecture in commit `79637e2`, proves the fixed-outer-Z contact
rank theorem symbolically, and isolates the first literal all-node-prefix
window obstruction. It is not a production change, candidate, score, or
submission.

## Decision

There are two distinct results.

1. **GREEN symbolic straightening.** Every fixed `(A,n)` raw contact matrix
   decomposes into explicit one-variable Pascal blocks. For every homogeneous
   block `(A,n,H)`, its rank is a closed cardinality and it has a displayed
   Vandermonde unit minor. This theorem covers the faces `r+s=21` and `s=10`
   literally; neither is treated as generic or omitted.
2. **RED for one uniform fixed-Z all-node-prefix source class.** The old
   formula from `79637e2` spans for `69<=A<=77`, but first fails at `A=68`.
   The corrected minimal prefix recurrence remains source-legal and spans
   every raw module through `A=58`. At `A=57`, even the image of **all**
   coefficient jets admitted by every literal all-node Hermite window has
   rank 1341 versus raw rank 1342. The exact missing stratum is one
   dimensional and lies at the simultaneous slope/curvature corner.

The A57 result is a raw-surjectivity obstruction, not recurrence death. The
actual A58 prescribed-section outgoing operator can occupy a proper subspace
of the raw A57 module. The decisive next gate is its quotient rank modulo the
maximal legal A57 prefix image, including the canonical higher coefficient
jets. No conclusion about that target-specific quotient is made here.

## Frozen authorities

```text
full187_active75_parametric_initial_jet_staircase_gate_6900.py
  db1725a1bb483e60f0b5e649aaa801d2090a2c14591a92e76b8c4a34e909035a
full187_cross_slope_second_fringe_confluence_6900.py
  2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29
full187_earliest_positive_u0_curvature_frontier_gate_6900.py
  cd763ffc825c0a9e1d73f055d1278b583fdcdac162a5ed597e289e24d4db53b0
```

The new script checks those hashes before doing any work.

## Normalized contact algebra

Write the literal contact polynomial as

```text
T = E + X*R - (1/2)*X^2*S.
```

A raw coordinate is

```text
X^q R^r S^s T^y,
y+r+s=A,
r+s<=21,
s<=10,
y<60,
q<60-y,
```

projected onto rows `X^i E^a R^rho S^b` with `i+3a<60`. Localize only for
the purpose of a change of coordinates and put

```text
u = E/(X*R),
v = X*S/R,
t = u-v/2,
n = y+q-s.
```

Then

```text
X^q R^r S^s T^y = X^(n) R^A v^s (1+t)^y.
```

An output row determines `n` uniquely:

```text
n = i+a-b.
```

Consequently the full map is a direct sum over `n`; this is not merely a
filtration. In an `n` block let

```text
K = 60-n.
```

After substituting `t=u-v/2`, a homogeneous monomial `v^s t^j` of ordinary
degree

```text
H=s+j
```

has rows

```text
u^a v^(H-a),  0<=a<=j,  H+a<K.
```

The target dimension in that grade is therefore exactly

```text
d(A,n,H) = min(H+1,K-H),
```

for `0<=H<=min(A,K-1)`, and zero otherwise.

The replay checks this normalization against all 880 literal nonzero entries
of the exact active-75 matrix. The normalized `n` identity, row exponents,
truncation weight, and multinomial/curvature scalar all match.

## Exact source intervals, including both caps

At fixed `(A,n,s)`, the raw coordinate condition `q=n-y+s` makes the allowed
`y` values the consecutive interval

```text
L_A = max(0,A-21),
U_(A,n,s) = min(59,A-s,n+s),
Y_(A,n,s) = [L_A,U_(A,n,s)]
```

when `n+s<60` and `U>=L`; otherwise it is empty. Put

```text
m(A,n,s) = |Y_(A,n,s)|.
```

This formula treats the two dangerous boundaries exactly:

- `y=L_A` is the face `r+s=21` when `A>=21`;
- `s=10` is present as the literal endpoint of the `s` range;
- `y=A-s` is the face `r=0`.

There is no unstated extension beyond any face.

The powers `(1+t)^y` for distinct `y` have invertible finite-difference
transition matrix in characteristic greater than 60. Therefore the
associated leading monomials contributed by the `m(A,n,s)` columns are

```text
v^s t^j,  0<=j<m(A,n,s).
```

For a fixed homogeneous degree `H`, define

```text
Jraw(A,n,H)
  = {H-s : 0<=s<=10 and 0<=H-s<m(A,n,s)}.
```

These are distinct because `s=H-j`.

## Pascal rank and the unit-minor proof

The coefficient of target row `a` in `v^(H-j)t^j` is

```text
binom(j,a) * (-1/2)^(j-a).
```

Thus the exact rank of the `(A,n,H)` block is

```text
rank(A,n,H) = min(|Jraw(A,n,H)|, d(A,n,H)).
```

To prove it, take any `k=min(|Jraw|,d)` distinct values

```text
j_0 < ... < j_(k-1)
```

and target rows `a=0,...,k-1`. Their determinant is

```text
(-1/2)^(sum_c j_c-k(k-1)/2)
* product_(c<e) (j_e-j_c)
/ product_(a=0)^(k-1) a!.
```

This is the ordinary binomial-basis Vandermonde determinant. In the present
source geometry, `0<=j<=21` and `k<=11`. Hence it is a unit in every field of
characteristic greater than 60; in particular it is a unit modulo
`2130706433`.

This proves the rank formula symbolically. The script additionally checks all
132 distinct `J` minors occurring in all 78 active degrees. The full
stratum/minor receipt hash is

```text
01a1452f3cbe47b0d72a7b2d23c7a756a116a17fed0e9160aa8b5463e5bfc758.
```

Summing the formula gives raw ranks 56, 79, and 103 for `A=77,76,75`, exactly
matching the three independent dense computations.

## Correct rank criterion for any physical initial-prefix set

Let a proposed section family prescribe the initial coefficient prefix

```text
q=0,...,c(A,y,r,s)-1
```

on each physical polynomial. At fixed `(A,n,s)`, let

```text
m_c(A,n,s)
 = #{y in Y_(A,n,s) : n-y+s < c(A,y,A-y-s,s)}.
```

Finite differences depend only on the number of distinct `y` exponents, so
the associated set is

```text
J_c(A,n,H)
 = {H-s : 0<=s<=10 and 0<=H-s<m_c(A,n,s)}.
```

The proposed family spans the full raw contact module if and only if, for
every `(n,H)`,

```text
min(|J_c(A,n,H)|,d(A,n,H))
  = min(|Jraw(A,n,H)|,d(A,n,H)).
```

This equality is the corrected exact test. It replaces both dense rank
enumeration and inference from support matchings. A defect stratum is exactly
a strict inequality in this display.

The canonical minimal associated basis in each stratum is obtained by taking
the smallest `min(|Jraw|,d)` values of `Jraw`; its determinant is the displayed
unit. A physical prefix basis is constructed deterministically as follows:

1. scan coordinates by increasing `q`, then `y`, then `s`;
2. never take `q` unless all lower jets of that physical polynomial were
   taken;
3. when a new coordinate makes the current `(n,s)` count equal to `j`, it
   creates exactly the associated direction `j` at `H=s+j`;
4. retain it iff the current `J_c` rank at that stratum is below the raw rank.

Each accepted coordinate raises rank by exactly one. Without coefficient
windows, the resulting prefix count equals the symbolic raw rank for every
`0<=A<=77`. Its complete coordinate receipt hash is

```text
c37ed7d1058c8e22858005994dafd89369f7cb9d1bf2d2589d8671098f33e535.
```

## Correction of the old staircase at A68

The old formula

```text
qmax_old(y,s)
 = max(0,floor((59-y)/3),floor((49-y+s)/2))
```

has full rank for `69<=A<=77`, but not below. Its first descending defect is

```text
A=68, n=49, H=10, K=11,
d=1,
Jraw={0,1,2,3,4,5,6},
Jold={},
raw rank 1, old rank 0.
```

The deterministic corrected recurrence adds exactly one coordinate at this
first step:

```text
(y,r,s,q,z)=(57,2,9,1,2625).
```

Its literal two-jet window is very safe:

```text
width=1911972, needed=524288, slack=1387684.
```

So A68 is a failure of the old closed expression, not a capacity obstruction.
The corrected minimal recurrence continues with full rank and positive
literal slack for every active degree from 68 down through 58.

The complete old-formula census has 17,706 deficient homogeneous strata,
all at `A<=68`. The exact predicate above characterizes every one; their
ordered receipt hash is

```text
1dfb9480374b5be8e56d16e26ea7104e55704f571b0e69d832a6f87a3ed10a2d.
```

## Corrected prefix windows through A58

For the corrected minimal bases, the tight window alternates with the integer
width parity. The relevant descending receipts are:

| A | raw/basis rank | maximum prefix depth | minimum slack |
|---:|---:|---:|---:|
| 68 | 412 | 7 | 76,975 |
| 67 | 473 | 7 | 208,045 |
| 66 | 537 | 8 | 76,973 |
| 65 | 609 | 8 | 208,043 |
| 64 | 684 | 9 | 76,971 |
| 63 | 762 | 9 | 208,041 |
| 62 | 848 | 10 | 76,969 |
| 61 | 937 | 10 | 208,039 |
| 60 | 1,030 | 11 | 76,967 |
| 59 | 1,130 | 11 | 208,036 |
| 58 | 1,234 | 12 | 76,964 |
| 57 | 1,342 | 13 | **-54,108** |

Thus the corrected prefix recurrence has a contiguous GREEN range
`58<=A<=77`. It first exceeds a literal coefficient window at A57.

## The exact A57 obstruction

At A57, the one missing homogeneous block is

```text
n=38, H=21, K=22,
d=min(22,1)=1,
Jraw={11},
Jlegal={},
raw rank 1, maximal legal-prefix rank 0.
```

The only raw associated direction is

```text
j=11, s=10, H=s+j=21.
```

At fixed `(A,n,s)=(57,38,10)`, the raw `y` interval has exactly twelve
members `36,...,47`. Producing finite-difference order 11 requires all twelve.
They correspond to

```text
(y,r,s,q)=(y,47-y,10,48-y).
```

The first member is

```text
(y,r,s,q)=(36,11,10,12),
r+s=21, s=10,
width=3353764,
required depth=13,
needed=3407872,
slack=-54108.
```

Numerically, this is not an absent thirteenth coefficient channel:

```text
3353764 = 12*262144 + 208036.
```

After twelve complete all-node jets, the literal window retains a
degree-`<208036` partial thirteenth-jet polynomial. Relative to the full
262,144-node coefficient channel, only the complementary 54,108-dimensional
node quotient is missing. Thus the next target-specific question is whether
the actual A58 outgoing defect polynomial, after the row dual above, lies in
that residual degree window (possibly after kernel adjustments). It is not a
question about 262,144 unconstrained missing scalars.

The other eleven members fit their windows. The first one is admitted only
through depth 12, so the maximal legal set has `m_legal=11` and cannot create
`j=11`. This proves that no choice of fixed-Z all-node initial prefixes can
span the raw A57 module: the span of the union of **all** legal prefix jets is
already deficient.

The associated missing target monomial row is

```text
(i,a,R,S,z)=(59,0,36,21,2625).
```

The maximal legal image has exact rank

```text
1341 versus raw rank 1342.
```

### Independent-audit discrepancy and literal resolution

An independent audit initially found no A57 defect by projecting every
original `(1+t)^y` column separately into every homogeneous `H` block. That
counts the same physical column as an independently adjustable pivot at many
different `H` values. Its coefficients across those values are coupled.

The finite-difference count `m(A,n,s)` is what remains after eliminating the
lower homogeneous terms: `m` distinct exponents `(1+t)^y` provide exactly the
leading orders `t^0,...,t^(m-1)`, not a fresh copy of every higher order for
each original column. This is why `m=12` creates `j=11` and `m=11` does not.

The disputed block was therefore rebuilt directly from literal raw contact
columns, without the symbolic rank formula. At `(A,n)=(57,38)` it has

```text
87 raw coordinates,
86 literal-window-legal coordinates,
132 literal target rows,
raw rank 87,
legal rank 86.
```

The sole omitted coordinate is exactly

```text
(36,11,10,12,2625).
```

A deterministic row dual with support 87 annihilates all 86 legal columns
and evaluates to one on the omitted column. Stable hashes are

```text
omitted raw column
  707ed944ad4eda2740da7470292017ad43aad3b46d2bc0c4830a0c28f38456dc
normalized sparse dual
  ee4106cbef0fd9ae18a82d00f1692554c59aa0cbca9cae7aee0e12abfaa80be5
```

Thus the direct literal discriminator agrees with the filtered symbolic
theorem and explains exactly why the simpler per-`H` support count overcounts.

There is a parity recovery at A56: all legal prefixes span there again. This
does not repair a descending construction blocked at A57. For A55 and every
lower A, the maximal legal prefix image is again deficient. The entire legal
defect census consists of 9,031 homogeneous strata, exactly characterized by
the displayed `J` inequality; its ordered hash is

```text
21e976249053869a03c9112c02196c5434083a3758641682071d9a3430d8c3cc.
```

## Closest lower-outer-Z predecessors of the missing row

Reachability from an earlier outer-Z block is not empty. For a section tail
with one frozen-`U` shift, `deltaZ=1`, every closest predecessor of the
missing row is parameterized by

```text
0<=s<=10,
max(0,19-2s)<=r<=21-s,
y=58-r-s,
f=57-r-s,
q=r+2s-19,
source z=2624,
source active=58,
remaining u0 power=0.
```

There are 87 such physical predecessor shapes. Their exact row/scalar receipt
hash is

```text
77b438e5d11ae50200fdbc4048f8d20f0944c47d04f6a112e9e8f780e070c8e4.
```

The minimum derivative order is `r+s=10`, attained by exactly two closest
predecessors:

```text
(r,s,y,f,q,deltaZ,source z,source active,remaining u0)
  = (1,9,48,47,0,1,2624,58,0),
    (0,10,48,47,1,1,2624,58,0).
```

Their coefficient-prefix windows are legal:

```text
(r,s)=(1,9), q=0: width 3222681, slack 2960537;
(r,s)=(0,10),q=1: width 3222682, slack 2698394.
```

This is only reachability. It does not prove that either predecessor supplies
an independently adjustable kernel jet after its own earlier obligations and
canonical higher jets are imposed. That target-specific quotient is the next
falsifier.

## Well-founded induction statement

The proof-ready assembly theorem should use the finite lexicographic order

```text
(outer Z, J-active degree, contact weight).
```

At fixed `(outer Z,A)`, decompose by `n`, then solve the homogeneous `H`
blocks by the unit Pascal minors above. Prescribing an initial coefficient
prefix induces higher `q`; increasing `q` raises the first row exponent and
hence strictly raises contact weight. For a nonfull contact `f<y`, the
u0-free output increases `J-active`, while the positive-u0 mate also increases
outer Z. Therefore every unsolved output moves strictly forward in the
displayed finite order.

The exact conditional theorem is:

> If, at every visited `(outer Z,A,n,H)`, the actually available section
> prefixes have `J`-rank equal to the rank of the pending right-hand side,
> then the unit Pascal solves cancel that block and all induced outputs move
> strictly forward; hence the construction terminates.

Raw surjectivity is the stronger sufficient premise obtained by replacing
"pending right-hand side" with `Jraw`. It holds for the corrected prefixes
through A58 and fails at A57. The actual-tail quotient test may still satisfy
the weaker premise.

## Process corrections

- The active-75 receipt correctly labeled all-A span as a conjecture. It is
  now falsified at the first exact stratum A68/n49/H10; do not promote the old
  formula unchanged.
- Capacity of a proposed prefix and span of the raw module are independent
  checks. The old formula is capacity-safe globally but loses rank at A68.
- A dense raw-rank failure is stronger than needed for assembly. The A57
  obstruction must be tested against the actual incoming operator before any
  route is abandoned.
- Support matching is still not a determinant proof. The symbolic
  Vandermonde formula supplies the missing coefficient certificate.

## Replay

```text
python3 .experiments/full187_parametric_pascal_straightening_window_gate_6900.py
```

At note time, the run used about 65 MiB and 13 seconds, far below the 3 GiB
experiment cap. It expands no new full active matrix beyond the already
frozen 880-entry active-75 normalization control and the decisive small
`132 x 87` A57/n38 discriminator.

```text
script SHA256    f9c504d835c2a47009da6b27eef7b9d1f43535f11501ed960e2c94d9ae50a951
canonical SHA256 3312744f422d6f12ef581cf046c9a25f8e3cf831b60eb7fa134e7d268dda41de
```

The script and note make no production or submission changes.
