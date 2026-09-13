# Full187 order-four covariant repair after the error-offset countergate

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Verdict

The old three-carrier shell is **not uniform** in the received directions.
The exact `(3,5,7)` error-offset chamber falsifies it on the entire affine
fibre, not merely for one unlucky linear solve. Recentring by the unique
degree-nine polynomial through all ten directions does not repair it.

There is, however, a substantially stronger exact replacement. Put

```text
V  = Y-QZ,
V1 = R-Q'Z,
J1 = Lambda V1-Lambda' V.
```

Every one of the three offset grade-seven correction shells is exactly a
single scalar multiple of a compound row in the eight-family weighted
order-four module

```text
Lambda^a V^b J1^c Z^(7-b-c),
c in {0,1},  a+b+2c=4.                              (M4)
```

Thus the families are

```text
V^4, Lambda V^3, Lambda^2 V^2, Lambda^3 V, Lambda^4,
V^2 J1, Lambda V J1, Lambda^2 J1.
```

The exact multipliers have the sharp observed degree pattern

```text
deg h_(a,b,c) <= 3e-1-a-c.                           (H3)
```

For the control `e=3`, these upper degrees are respectively
`8,7,6,5,4,7,6,5`. The three RHS compound rows have scales

```text
F0:F1:F2 = 1:11:46  in F_101.
```

This repairs the finite arbitrary-direction counterexample at the correct
algebraic level. It does **not** yet prove the Full187 shifted-trellis
surjectivity theorem. The missing theorem has become much more specific:
prove that three error-node Hasse coordinates per multiplier suffice for the
terminal residual state and that the eight-family diagonal propagates through
all 2621 seed layers.

## 1. Why the old shell must be retired

In the matched chamber the grade-seven correction happened to use only

```text
V^4, Lambda V^3, V^2 J1.
```

For error direction offsets `(3,5,7)`, the full exact solve still closes all
three locator normals with the same eight raw `(Y,R,Z)` shapes, but every one
of the five previously omitted centered slots is nonzero. A separate
affine-fibre feasibility calculation retains all 47 homogeneous `C+J`
freedoms and proves that imposing the old three-carrier equations is
inconsistent for each RHS. Hence this is not a basis-choice artifact.

Testing only the individually legal members of `(M4)` in the tiny chamber
also does not close the offset defect: the base has rank 1351, the 26 clean
covariant columns add rank 26, and the three individual defects and joint
defect remain `(1,1,1)` and `1`. This is expected because the tiny `D=28`
window excludes `Lambda^4` and some high multiplier terms.

The correct test works in the raw covariant module and imposes literal source
legality after summing. With multiplier degree at most eight, 99 generator
columns span each exact grade-seven offset shell. The reconstructed legal rows
have support 149. Across the selected representation, 148 occurrences that
are illegal term-by-term cancel exactly in the compound sum. Agreement contact
is checked directly to be zero after reconstruction.

No `J2` or curvature carrier is needed. This is important for the target,
because it keeps slope degree at most one and curvature degree zero.

## 2. Target width is comfortably green

At Full187 use

```text
(w,g,e,m,D)=(131071,180413,81731,60,10824780),
deg Q=2e=163462.
```

Multiply every order-four row by `V^56 Z^20`. It then has agreement contact
order 60 and total source grade 83. Every further `Z^k`, `0<=k<=2620`, stays
within the final grade 2703.

Give each multiplier the conservative uniform degree cap

```text
deg h <= 3e-1 = 245192.
```

Let `d=a+c<=4` be the number of locator-degree units in a family. At the
all-`Z` endpoint, a raw term is bounded by

```text
(3e-1) + d g + (60-d)(2e).
```

Replacing a centered factor by `Y` or `R` removes degree `2e` (or `2e-1`)
and adds source weight only `w` (or `w-1`). The degree-plus-weight therefore
drops by exactly `2e-w=32391` per replacement. The all-`Z` endpoint is the
worst one.

Since `g>2e`, the worst family is `Lambda^4 V^56 Z^27`:

```text
(3e-1)+4g+56(2e) = 10120716 < D,
margin = 704064.
```

So, unlike the tiny control, every family in `(M4)` is individually legal at
the target even before using the coupled high-head cancellations. The Lean
companion proves the entire raw strip uniformly in `d` and in the number of
active replacements, under the four-GiB wrapper.

## 3. Exact remaining bridge

The viable terminal statement is now:

> For every forced three-normal residual reaching grade 83, and at every
> passive shift through grade 2703, choose eight coefficient polynomials
> `h_(a,b,c)` of degree `<3e` so that the corresponding shifted `(M4)` row
> cancels the complete error contact, with later leakage confined to higher
> passive seed.

The finite result makes three facts exact: the old uniformity claim is false;
the missing offset residual is one compound carrier rather than five
unrelated accidents; and the robust carrier module has ample target width.
It does not establish that the live target residual at every layer is encoded
by only three Hasse coordinates per multiplier. That local diagonal/state
theorem, followed by finite lower-triangular induction, remains the principal
uncertainty. The independent `Z1` and downstream typed allocation also remain
after it.

## Reproduction

```text
python3 -m py_compile \
  .experiments/f101_order4_osculating_covariant_basis_gate_6900.py
prlimit --as=4294967296 -- python3 -B \
  .experiments/f101_order4_osculating_covariant_basis_gate_6900.py

.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187OrderFourCovariantWidth6900.lean
```

Canonical Python receipt:

```text
42e96db22d79eff748556ddb259a65a81e461e8974211bae53ef8e23c0601b80
```

Artifact hashes:

```text
afb1fe1f74394d9263a6521a7ffc4280ddd4aa6e56a352cf02f458a120d69875  f101_order4_osculating_covariant_basis_gate_6900.py
da228b13b15029ffef3661a871ccf2d6d6c5d7c80904e7c237d7b16b25d1b4e2  Full187OrderFourCovariantWidth6900.lean
```

The Lean width proof uses only standard axioms reported by `omega`/`norm_num`;
there is no `sorry`, `decide`, or `native_decide`.
