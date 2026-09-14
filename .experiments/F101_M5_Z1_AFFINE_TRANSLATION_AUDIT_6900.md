# m5 Z1 affine-translation audit: the defect is not an origin artifact

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, `score.txt`, `radius.txt`, and the accepted 6806 result are
unchanged.

## Verdict

The exceptionally sparse m5 dual witness

```text
take the coefficient of X^0 Z
```

is caused by putting the agreement point `X=0` in the finite control. The
**Z1 defect itself is not**. Translating every field point so that no
agreement point is zero makes the constant-Z coefficient row nonzero on
almost every kernel coordinate, but pure constant `Z=1` remains defect one.
The sparse witness is replaced exactly by evaluation of the Z-coordinate at
one translated agreement point.

Therefore an affine X-coordinate change is not a repair for filtered Z1.
Coefficientwise Z1 remains a genuine target obligation. The fraction-field
rank-four calculation can see a nonzero polynomial Z direction because it
may invert a locator factor; a polynomial translation cannot perform that
inversion.

## 1. What is theorem-level and what is finite evidence

The following algebraic statements are general, not empirical.

Let `tau_a` be the polynomial automorphism induced by `X -> X+a`, applied
coefficientwise to all four boundary coordinates.

1. `tau_a` fixes the constant polynomial `1`.
2. `tau_a` cannot turn a nonconstant polynomial into a constant. If
   `tau_a(p)=c`, applying `tau_{-a}` gives `p=c`.
3. The source support used here is downward closed in X-degree at each fixed
   `(Y,R,S,Z)` shape. Indeed its relevant cap is

   ```text
   x + w*y + (w-1)*r + (w-2)*s < D.
   ```

   Expanding `(X+a)^x` only produces powers `X^j` with `j<=x`, so translation
   preserves this cap as well as every Y/R/S/Z cap. The inverse translation
   proves equality, not merely containment. Shape by shape the change-of-
   basis matrix is unitriangular.
4. If all node coordinates, received data, contact maps, and source
   polynomials are translated consistently, the new boundary image is
   `tau_a(B)` for the old image `B`. Hence

   ```text
   constant-Z in tau_a(B)  iff  constant-Z in B.
   ```

   Translating only the polynomial while leaving the node/contact instance
   fixed is not a coordinate change of the same problem.

The ranks, support counts, and double-root statements in Section 3 are exact
finite `F_101` evidence for the m5 control. They are not a Full187 theorem
and do not prove that the target boundary image has a common locator factor.

## 2. Actual benchmark-domain semantics

`ProximityPrize/Benchmark/IRSProfile.lean` defines

```text
baseNttDomain.node i = omega^i
domain i = Ext.ofBase (baseNttDomain.node i),
```

where `omega` is a primitive `2^18`-th root of unity. Thus every actual NTT
node is nonzero; embedding it into `KoalaBear.Ext6` remains nonzero. The
actual benchmark does **not** contain the field point zero.

At the abstract source/interpolation layer, a translated node embedding is
still injective, and the X-degree/source caps permit a simultaneous affine
reparameterization. However, the benchmark evaluation domain itself is
fixed: one cannot translate just one side of an evaluation identity and
silently claim it is the same codeword. A legal simultaneous
reparameterization is conjugacy of the whole construction, and by the
general argument above it preserves the constant-Z membership question.

So there are two cases, neither useful as a Z1 shortcut:

```text
translate only X-polynomials:       not the same contact/evaluation instance;
translate the whole construction:   legal conjugacy, but Z1 defect invariant.
```

## 3. Exact shifted-node control

The script

```text
.experiments/f101_m5_z1_affine_translation_audit_6900.py
```

rebuilds the literal source/contact matrix for

```text
F_101,
(N,w,g,m,D,s,t,J,L)=(10,4,7,5,35,1,1,7,11),
error-direction offsets=(3,5,7),
maximum centered grade=11.
```

Logical node `i` is represented successively by field points `i`, `i+1`,
and `i+17`. Every locator, direction polynomial, node evaluation, and local
contact translation is rebuilt with the shifted field coordinates. The
monomial source is unchanged. For each control the script row-reduces the
complete literal contact matrix and computes the full coefficientwise
Y/R/S/Z boundary image on its kernel.

| shift | agreement points | contains 0? | contact rank/nullity | coefficient image rows/cols/rank | localized rank over `F_101(X)` | nonzero entries in constant-Z row | constant Z defect |
|---:|---|:---:|---:|---:|---:|---:|---:|
| 0 | 0,...,6 | yes | 3820/296 | 131/296/12 | 4 | 0 | 1 |
| 1 | 1,...,7 | no | 3820/296 | 131/296/12 | 4 | 294 | 1 |
| 17 | 17,...,23 | no | 3820/296 | 131/296/12 | 4 | 293 | 1 |

Thus the rank and Z1 defect are unchanged even though the literal
constant-coefficient row changes from identically zero to almost fully
supported.

There is also an explicit transported dual witness. At shift zero,
evaluation of the Z-coordinate at the first agreement point is

```text
z(X) |-> z(0) = [X^0]z,
```

so its coefficient support has size one. At shift one the transported
witness is

```text
z(X) |-> z(1) = sum_{d=0}^{34} [X^d]z,
```

with support size 35. At shift 17 its coefficients are `17^d mod 101`, again
with support size 35. In all three controls this functional annihilates the
entire boundary image and pairs with pure constant Z as `1`.

The script checks more: for every one of the four boundary coordinates,
every image column has both value and first derivative zero at all seven
agreement points. Equivalently in this finite m5 control, every coordinate
has the common factor

```text
Lambda_agreement(X)^2 = Lambda_agreement(X)^(m-3).
```

This explains both observations at once:

* over `F_101[X]`, constant Z cannot be in the image because it does not
  vanish at an agreement point;
* over `F_101(X)`, the nonzero locator factor becomes invertible, so the
  packed/localized four-rank can still be four.

Moving the roots of `Lambda_agreement` away from zero changes its constant
coefficient but does not change its positive degree or make it a unit.

## 4. Consequence for Full187

This audit closes one tempting but invalid escape route:

```text
STOP  blame the m5 Z1 failure on choosing X=0 as an agreement point;
STOP  translate a nonconstant polynomial Z boundary and call its new
      constant coefficient a normalized constant-Z boundary;
STOP  use localized rank four as a coefficientwise lift.
```

The remaining target question is still the honest one:

```text
Can target-specific active/derivative terminal coupling produce a complete
contact-kernel vector whose Y/R/S boundary is zero and whose exact normalized
Z boundary is 1?
```

The m5 calculation cannot answer that target question negatively. Its common
double-zero factor is an exact fact about this finite control, not a theorem
about the much richer Full187 source. In particular, the conservative 103
terminal shapes and their lower-grade connecting tails may supply coupling
absent from `(s,t)=(1,1)`. That is the remaining productive search space.

## 5. Reproduction and resource receipt

```text
prlimit --as=4294967296 --rss=4294967296 -- \
  python3 -B \
  .experiments/f101_m5_z1_affine_translation_audit_6900.py
```

The exact run exited zero in 70.54 seconds and peaked at 783,388 KiB RSS
under the explicit 4 GiB address-space/RSS cap.

```text
canonical payload SHA-256
  3d7449fcce425e067375bcf90b04c05fe54da9cc3eae34439e8425348fbe9e36

script SHA-256
  347802489fb293e1bfb25c057199a4c46359dac5b15801e1027f5c8097bc8262
```

Final process decision:

```text
GO    keep coefficient windows and test target-specific Z1 coupling;
STOP  spend further time on affine-origin changes as a Z1 mechanism.
```
