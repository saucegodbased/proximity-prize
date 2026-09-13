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

There is a sharp scale distinction. The extracted **tiny-F101** multiplier
bounds

```text
deg p[a,c] <= 3e-1-a-c
```

have only

```text
sum_(a,c) (3e-a-c) = 24e-16                         (DIM)
```

coefficients, whereas arbitrary order-`0,1,2` data in eight channels at `e`
errors has dimension `24e`. For the F101 control this is `56` versus `72`.
That sixteen-dimensional shortage is **not a target obstruction**. The
independent Full187 width theorem permits the uniform bound

```text
deg p[a,c] <= 3e-1 = 245192
```

for every one of the eight carriers, individually, with worst endpoint
margin `704064`. The target coefficient dimension is therefore exactly

```text
8(3e)=24e=1961544.
```

Ordinary Hermite CRT supplies arbitrary value/first/second coefficient jets
at all errors. Combined with the local determinant, the target three-jet
interface is green.

The smallest honest remaining gate is now the **complete-state and seed
assembly theorem**: prove that these 24 selected coordinates are a complete
state for the forced residual modulo the already eliminated lower-grade
image, and that all unselected leakage goes strictly to later passive seed.
The generic scalar Toeplitz determinant handles the latter once this state
identification is established.

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
is checked only after reconstruction. This endpoint coupling is essential
for the **tiny F101 control only**. At Full187 the uniform degree-`<3e` width
audit proves every one of the eight families individually legal, so target
source legality does not depend on that cancellation.

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

Let `H_3` send the eight target coefficient polynomials

```text
deg p[a,c] <= 3e-1
```

to their order-`0,1,2` Hasse data at the roots of `Xi`. Since `Xi` is
squarefree, Hermite CRT makes `H_3` an isomorphism. Let `L` be the block
lower-triangular local contact map certified above. The remaining source
statement is:

> **Complete-state eight-carrier seed induction (open).** Modulo the image of
> grades at most 82, the complete error-contact residual of every forced
> `F0/F1/F2` head is determined by the 24 per-node rows
> `T^j R^c Z^(b+a+c)`, `j=0,1,2`. After solving those rows by `L o H_3`, all
> remaining leakage has strictly larger passive seed. Repeating this through
> seed 2703 cancels the full residual.

There is no longer a local determinant, Hermite-dimension, or individual
target-width gap. The new content is precisely completeness of the selected
state modulo the lower image and compatibility of that reduction with the
passive-seed filtration. The F101 reconstruction verifies the initial
compound shells, and the independent shifted experiment observes a scalar
Toeplitz block; neither finite fact alone proves the target state theorem.

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
three-layer nonvanishing, the tiny-F101 identity `(DIM)`, and the exact
Full187 uniform `24e` parameter equality. It uses no `sorry`, `decide`, or
`native_decide`; printed axioms are standard only.
