# k=0 locator-Schur factor audit and invariant replacement

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G` research. This note
audits whether the `4 x 4` determinant `72` in the m8/L16 locator-Schur
receipt can be promoted to a formula in the error mismatch data. It is not a
target theorem, candidate, build, comparator result, or submission.

## Verdict

**STOP treating the displayed `72` as a determinant polynomial. GO only for
the rank-adaptive maximal-minor/Fitting ideal.**

The m8 calculation proves the invariant statement

```text
rank(boundary restricted to ker contact) = 4.
```

The number `72` is the determinant of one four-column chart after two
parameter-specialized RREFs. It is not canonical, and the current receipt
does not define that chart over a polynomial parameter ring. A controlled
two-error interpolation gives a concrete reason this distinction is
load-bearing: the first-mismatch chart has at least six whole linear
resonance components, including the equal-mismatch component, although the
intrinsic conormal gain remains four there. Contact rank also changes between
strata, so no single maximal-contact bordered minor can cover the family.

The correct object is the ideal of all maximal minors of the induced
boundary map on the contact kernel, locally on each constant-contact-rank
chart. Equivalently, it is the zeroth Fitting ideal of that boundary
cokernel. Globally one must retain the contact-rank stratification.

## 1. Why the m8 determinant `72` is not a function of mismatches

The receipt at commit `618d008` first computes an agreement RREF, identifies
an implicit agreement-kernel basis, computes an error-on-kernel RREF, and
then forms a `4 x 268` boundary Schur matrix. Its first four RREF pivot
columns have determinant `72 mod 101`.

There are three independent coordinate choices in that number:

1. the agreement contact pivot basis;
2. the error-on-agreement-kernel pivot basis; and
3. the basis and ordering of the final 268-dimensional contact kernel.

If the first chosen final-kernel basis vector is multiplied by any
`u in F_101^*`, the displayed determinant becomes `72*u`. For example,
scaling by two changes it to `43`, and swapping two chosen vectors changes it
to `29`. Thus even at the fixed receipt only nonvanishing is invariant.

More seriously, the two RREF pivot selections were made *after* substituting
all received values. As those values vary, pivot denominators can vanish,
free coordinates can become pivots, and contact rank can change. The RREF
Schur output is therefore a piecewise rational chart, not a single raw
polynomial determinant. To obtain a polynomial on one open chart one must
freeze an original contact row minor `Delta`, its pivot source columns, and
four extra source columns before interpolation. The Schur determinant is
then, up to sign,

```text
det(frozen bordered raw minor) / Delta.
```

The current m8 receipt intentionally keeps the large kernel implicit and
does not record an original 17,411-row minor through both RREFs. Consequently
the scalar `72` cannot be reverse-engineered into a mismatch factorization.
Repeating the 17k elimination at many parameter values would still produce
different charts and would not solve this defect.

## 2. Exact two-error discriminator

The smallest faithful multi-error chamber is

```text
F_101,
(n,w,g,m,B,s,U,L,k,n0)=(6,2,4,3,3,1,4,6,0,1),
agreement nodes = 0,1,2,3,
error nodes = 4,5,
u0=(0,0,0,0,delta4,delta5),
u1=(0,0,0,a,b,c).
```

At `a=delta4=delta5=1`, the agreement interpolant has values `4` and
`10` at the errors, so

```text
epsilon4=b-4,    epsilon5=c-10.
```

The already committed exact rank audit gives

| direction `(b,c)` | contact rank | augmented rank | gain |
|---|---:|---:|---:|
| matched `(4,10)` | 724 | 728 | 4 |
| first only `(0,10)` | 726 | 730 | 4 |
| second only `(4,0)` | 726 | 730 | 4 |
| both `(0,0)` | 722 | 726 | 4 |
| generic equal mismatch `(7,13)` | 724 | 728 | 4 |

This alone proves that a fixed `730 x 730` maximal-contact bordered minor
cannot cover the both-mismatch point: the entire augmented matrix has rank
only 726 there.

The new executable freezes the first-mismatch `730 x 730` raw chart selected
over F101 and evaluates the same row and column indices over larger primes.
This separates an honest raw determinant from any later RREF. Over F1009,
every slice below has degree exactly 72 and passes an unused holdout value.

For `c=9,10,11`, exact univariate factorizations have the following stable
linear valuations, where `d=b-c`:

```text
d                  exponent 8
d+3                exponent 9
d+6                exponent 9 generically
3*d+7              exponent 8
3*d+4              exponent 8
3*d+2              exponent 1
```

At the special intersection `c=10`, the exponent of `d+6` jumps from 9 to
25 because another residual factor meets the same point. The same six
factors and generic exponents recur independently over F1013. For example,
at `c=10` the F1013 roots are

```text
b=10       (d=0),        exponent 8
b=7        (d=-3),       exponent 9
b=4        (d=-6),       exponent 25
b=683      (3d+7=0),     exponent 8
b=684      (3d+4=0),     exponent 8
b=347      (3d+2=0),     exponent 1.
```

Degree-bounded interpolation at 105 points proves that the determinant
restricts identically to zero on each of the six F1009 lines. The likely
homogeneous common factor of this fixed chart is therefore

```text
G(a,b,c) =
  (b-c)^8
  * (b-c+3*a)^9
  * (b-c+6*a)^9
  * (3*b-3*c+7*a)^8
  * (3*b-3*c+4*a)^8
  * (3*b-3*c+2*a).
```

The exact line tests prove each distinct linear divisor; the displayed
multiplicities are a cross-prime conjecture supported by generic slices, not
a symbolic bivariate factorization. After setting `a=1`, `G` has degree 43;
the remaining slice factor has degree 29 and has further algebraic zeros.

In mismatch coordinates the most important divisor is

```text
b-c+6*a = epsilon4-epsilon5.
```

Hence the whole equal-mismatch locus kills this fixed first-mismatch minor.
The matched chart is nonzero on generic points of that locus, but its exact
restriction there is a degree-21 polynomial with algebraic roots. It is not
a unit chart either.

The value residuals are coupled as well. At the valid first-mismatch point
`(b,c)=(0,10)`, the same raw chart gives over F1009

```text
D(delta4,1): degree 58, factor delta4^25 times nonzero-root factors;
D(1,delta5): degree 57, factor delta5^24 times nonzero-root factors.
```

So the one-error formulas
`unit * delta^alpha * mismatch^beta` do not tensor into a multi-error fixed
chart. Even with both value residuals nonzero, additional chart factors can
vanish.

Finally, a chart selected directly on the contact-rank-722 both-mismatch
stratum is a `726 x 726` raw minor with determinant `81 mod 101`. It is
nonzero also at the two single-mismatch sample points, but vanishes at the
matched and generic-equal-mismatch points. This is an explicit small chart
cover, not a universal determinant.

## 3. The invariant replacement

Let `R` be the polynomial parameter ring, let

```text
C : R^N -> R^M       (all-node contact),
B : R^N -> R^4       (four boundary rows),
A = [C; B].
```

Write `I_j(M)` for the ideal generated by the `j x j` minors of a matrix.
On the contact-rank-`r` stratum

```text
Sigma_r = V(I_(r+1)(C)) intersect D(I_r(C)),
```

the failure locus for four-normal gain is exactly

```text
Sigma_r intersect V(I_(r+4)(A)).
```

Indeed, on `Sigma_r`, gain four is equivalent to `rank(A)=r+4`, and the
boundary block can add at most four ranks. A coordinate-free algebraic audit
can use the saturated determinantal ideal

```text
(I_(r+4)(A) + I_(r+1)(C)) : I_r(C)^infinity
```

for each rank stratum, followed by localization at the certified nonzero
agreement Newton coefficient, value residuals, and Vandermonde factors.

On a particular open contact chart `Delta != 0`, the contact kernel is free
and the induced map

```text
beta_Delta : ker(C)_Delta -> R_Delta^4
```

has invariant maximal-minor ideal

```text
I_4(beta_Delta) = Fitt_0(coker beta_Delta).
```

Changing the agreement, error, or final-kernel basis mixes its generators
but does not change this ideal. Each frozen bordered determinant is only one
generator on one `Delta`-chart. This is precisely the invariant that the m8
rank-four computation witnesses at its one point.

The rank stratification cannot be omitted: formation of `ker(C)` need not
commute with specialization when contact rank jumps, exactly as the
722/724/726 two-error example demonstrates.

## 4. GO / STOP decision

**STOP**:

* assigning mismatch factors to the m8 scalar `72`;
* repeatedly rerunning the 17k RREF and comparing its first Schur pivots;
* extrapolating either one-error pure-power bordered formula by a product over
  errors; or
* fixing one maximal contact rank globally.

**GO**:

* formulate the target recurrence as a rank-adaptive statement about
  `I_4(beta)` / the relative determinantal ideal;
* freeze raw row/column charts before any future interpolation;
* use the first live mismatch to choose a chart, while allowing lower contact
  rank on resonance strata; and
* prove that the common zero locus of the relevant chart family is empty
  after localizing at the genuine nonzero hypotheses.

This narrows the remaining theorem but does not close it. The finite m8
result remains strong evidence that the invariant ideal is nonzero at one
positive-margin point; it is not evidence that one determinant generator is
globally a unit.

## Reproduction

The generic interpolation tool is

```text
.experiments/k0_two_error_bordered_interpolate_6900.py
```

Representative commands are

```bash
python3 -B .experiments/k0_two_error_bordered_interpolate_6900.py \
  --chart 1 --variable b --fixed 10 --prime 1009 --samples 110

python3 -B .experiments/k0_two_error_bordered_interpolate_6900.py \
  --chart 1 --variable line --b-line 4,1 --c-line 10,1 \
  --prime 1009 --samples 105

python3 -B .experiments/k0_two_error_bordered_interpolate_6900.py \
  --chart 1 --variable d4 --b 0 --c 10 --d5 1 \
  --prime 1009 --samples 70
```

Each 105-value interpolation takes about 40 seconds and peaks below 70 MiB.
The executable sets a 3.9-GiB address-space ceiling. It uses exact modular
linear algebra only; no floating point, `decide`, or `native_decide`.
