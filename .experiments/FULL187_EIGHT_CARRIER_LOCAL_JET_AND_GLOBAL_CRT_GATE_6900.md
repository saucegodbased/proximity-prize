# Full187 eight-carrier local jet block and global CRT gate

Date: 2026-09-13 UTC. Scope: lower-6900 THREE-RHS research only. No
production, submission, score, radius, or claim file was changed. The
independent `Z1` direction and downstream typed allocation remain outside
this note.

## Verdict

The order-four osculating module has an exact **local unit block**, even for
arbitrary received-direction offsets. No `J2` carrier is needed for this
block. For

```text
(a,c) = (0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)
```

put

```text
K[a,c](p)
 = p Lambda^a V^(m-a-2c) J1^c Z^(b+a+c),
b = J+1-m,
V = Y-QZ,
J1 = Lambda(R-Q'Z)-Lambda'V.
```

At an error root `alpha` of `Xi`, write

```text
lambda = Lambda(alpha),
delta  = received value residual != 0,
epsilon = received direction - Q(alpha).
```

Since `Q=Xi^2`, both `Q(alpha)` and `Q'(alpha)` vanish. Order the carriers by
`h=a+c`, and within a common `h` put the `c=1` carrier before the `c=0`
carrier. Select the local row

```text
R^c Z^(b+h).
```

The resulting `8 x 8` value matrix is lower triangular, with diagonal

```text
lambda^(a+c) delta^(m-a-2c).
```

Its determinant is

```text
lambda^16 delta^(8m-19).                              (DET8)
```

Thus it is a unit whenever `Lambda` is disjoint from the error locator and
the error value is nonzero. Direction mismatch `epsilon` and `Lambda'` occur
only below the diagonal. This is the desired arbitrary-offset local repair;
unlike the earlier narrow block, it does not depend on `Xi'(alpha)`.

The same ordering repeats for coefficient Hasse jets. For jet order `j`, use
the row

```text
T^j R^c Z^(b+h)
```

and the coefficient jet `p[a,c],j`. A coefficient jet of order greater than
`j` cannot contribute to that row, so the matrix through orders `0,1,2` is
block lower triangular with the value block repeated three times. Its
determinant is `(DET8)^3`. The literal F101 check obtains rank `24` for all
three tested errors with direction offsets `(3,5,7)` and nontrivial residual
values `(1,9,17)`.

There is, however, a sharp global guard. The extracted multiplier bounds

```text
deg p[a,c] <= 3e-1-a-c
```

have only

```text
sum_(a,c) (3e-a-c) = 24e-16                         (DIM)
```

coefficients, whereas arbitrary order-`0,1,2` data in eight channels at `e`
errors has dimension `24e`. For the F101 control this is `56` versus `72`.
Therefore local invertibility does **not** imply an unrestricted global
three-jet CRT theorem. Exactly sixteen global compatibility conditions must
be proved for the shifted forced-head residual, or a legal coupled gauge must
supply the missing freedom.

This is now the smallest honest remaining gate for the eight-carrier route.
The exact F101 forced `F0/F1/F2` terminal shells happen to satisfy the
compatibilities: the independent raw-module extraction reconstructs all
three using precisely the eight families above. What remains unproved is
that every residual produced during the target's 2621-layer seed induction
stays in that compatible subspace.

## 1. Why the local matrix is triangular

At `T=E=S=0`,

```text
V  = delta + epsilon Z,
J1 = lambda R - Lambda'(alpha) V.
```

The carrier `K[a,c]` starts at passive seed `b+h`. It cannot contribute to a
row with a smaller seed. At a fixed seed, a `c=0` carrier cannot produce an
`R` row, while a `c=1` carrier may leak into the `R^0` row through the
`-Lambda' V` part of `J1`. Hence increasing `h`, with `c=1` first on ties,
is lower triangular.

On its own selected row, every `J1` contributes its `lambda R` term, every
remaining `V` contributes `delta`, and every explicit `Lambda` contributes
`lambda`. The diagonal is therefore

```text
lambda^a delta^(m-a-2c) lambda^c
 = lambda^(a+c) delta^(m-a-2c).
```

For the eight indices,

```text
sum(a+c)       = 16,
sum(m-a-2c)    = 8m-19,
```

which proves `(DET8)`. Multiplying a carrier by `(X-alpha)^j` shifts its
first possible horizontal row by exactly `j`; this proves the repeated
Hasse-layer triangularity.

## 2. Exact literal F101 receipt

The checked chamber is

```text
F101,
(n,w,g,m,D,s,t,J,L)=(10,4,7,4,28,1,1,6,10),
G={0,...,6}, E={7,8,9}, Q=Xi_E^2.
```

At every error the Python receipt directly expands the eight raw carriers in
the benchmark's literal contact convention. It uses the three coefficient
basis elements

```text
1, (X-alpha), (X-alpha)^2
```

and extracts the 24 rows `T^j R^c Z^(b+a+c)`. It asserts every entry above
the diagonal is zero, every diagonal entry equals the formula above, the
determinant is `(DET8)^3`, and the matrix rank is 24. The checks include
nonzero arbitrary direction offsets; this is not another zero-offset probe.

The companion exact raw-module extraction
`f101_order4_osculating_covariant_basis_gate_6900.py` reports that the
grade-seven pieces of all three exact offset lifts use only

```text
V^4, Lambda V^3, Lambda^2 V^2, Lambda^3 V, Lambda^4,
V^2 J1, Lambda V J1, Lambda^2 J1,
```

with multiplier degrees at most `3e-1-a-c`. Its `J1^2`, `V J2`, and
`Lambda J2` multipliers are zero. Some individual covariants are outside the
tiny raw width, but their illegal terms cancel in the coupled sum; legality
is checked only after reconstruction. This endpoint coupling must be retained
at the target.

## 3. Why the old three-carrier block was not enough

For the narrower terminal family, the clean coordinates `(c,C,A)` give the
three selected rows

```text
Z^b, Z^(b+1), T R Z^(b+1)
```

with determinant `Xi'(alpha) Lambda(alpha)^2 delta^(3m-3)`. In raw
coordinates `(c,B0,A)`, using

```text
C(alpha)=B0(alpha)/Lambda(alpha)-2A(alpha)Xi'(alpha),
```

the determinant simplifies further to

```text
Xi'(alpha) Lambda(alpha) delta^(3m-3).
```

That block is real, but it controls only three selected coordinates. The
literal primary F101 audit gives the decisive completeness test:

* grade-at-most-six source rank: `1461` from `1463` columns;
* adding degree-`<e` value interpolants for all three clean carriers leaves
  defects `(0,0,1)`;
* adding the full individually legal clean family closes all three RHS, but
  its quotient rank is 12;
* exhaustive subset search shows that **12** clean columns are necessary;
  no smaller clean-column subset contains all three RHS modulo the lower
  image.

The canonical coupled terminal rows evade that 12-column requirement because
their individually over-width `A` and `C` endpoints cancel in the raw sum.
This explains both why the narrow local determinant looked encouraging and
why it failed under arbitrary offsets. It must not be promoted to a complete
contact theorem.

## 4. Smallest exact completion lemma

Let `H_3` send the eight bounded coefficient polynomials

```text
deg p[a,c] <= 3e-1-a-c
```

to their order-`0,1,2` Hasse data at the roots of `Xi`. Let `L` be the block
lower-triangular local contact map certified above. The remaining source
statement is:

> **Compatible eight-carrier seed induction (open).** At every passive seed
> layer, after eliminating earlier layers, the residual of each forced
> `F0/F1/F2` head lies in `L(image H_3)`. Solving there produces a coupled raw
> source row whose endpoint cancellations keep it inside the literal width,
> and the next residual again lies in the same compatible image.

Since `L` is a local isomorphism, the only new content is membership in the
codimension-at-most-sixteen global Hermite image plus coupled raw legality.
The F101 reconstruction verifies this membership for the initial three
terminal shells; it does not prove invariance across all target seed layers.
One acceptable alternative is an explicit legal 16-parameter gauge that
makes `H_3` surjective without destroying endpoint cancellation.

Even after this THREE-RHS lemma, `Z1` and downstream typed Full187 allocation
remain separate work. No end-to-end 6900 claim is made here.

## Reproduction

```text
python3 -m py_compile \
  .experiments/f101_order4_eight_carrier_local_jet_block_6900.py
python3 -B \
  .experiments/f101_order4_eight_carrier_local_jet_block_6900.py

python3 -m py_compile \
  .experiments/f101_terminal_local_jet_block_6900.py
python3 -B \
  .experiments/f101_terminal_local_jet_block_6900.py

.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187EightCarrierLocalJetBlock6900.lean
```

The Lean file proves `(DET8)`, its nonvanishing over a field, the repeated
three-layer nonvanishing, `(DIM)`, and the exact sixteen-dimensional deficit.
It uses no `sorry`, `decide`, or `native_decide`; printed axioms are standard
only.
