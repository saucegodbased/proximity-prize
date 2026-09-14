# K0 locator/error CRT: exact target-scalable part and remaining seam

## Scope and verdict

`K0LocatorErrorCRT6900.lean` isolates the polynomial fact behind the staged
`m=8` Schur receipt and checks it at the lower-6900 constants.  The result is
useful but deliberately narrower than the missing source theorem:

* **GREEN:** error **values** decouple one locator grade at a time at cost
  `q*g+e` in X-degree;
* **GREEN:** the agreement Hasse coefficients killed by `Lambda_G^q` are
  exactly the orders `j<q`, not all 47 orders;
* **GREEN:** one-shot depth-47 error Hermite interpolation exists, but costs
  `q*g+47e`;
* **RED as a proposed shortcut:** the one-shot depth-47 construction does not
  fit even the target `SR*Y^43` X-window at locator grade zero;
* **OPEN:** lift the universal local contact-kernel repair through the global
  tapered source while retaining the layered error control.  The L10/L11
  ablation says the relevant extra source is passive-Z reach, not the new
  terminal active face.

Thus the exact `6537 x 6784` finite error Schur is not promoted to a target
theorem here.  What is promoted is the CRT component that remains valid when
`g` grows from 5 to 180,413.

## Lean theorem chain

The file proves, over an arbitrary field and arbitrary finite agreement and
error index types:

1. `agreementLocator_monic` and `agreementLocator_natDegree`:
   `Lambda_G` is monic of degree `|G|`.
2. `agreementLocator_eval_error_ne_zero`: cross-disjoint nodes make
   `Lambda_G(beta)` nonzero at every error `beta`.
3. `agreementLocator_isCoprime_errorJetDenominator`:
   `Lambda_G` is coprime to
   `prod_(beta in E) (X-beta)^m`.
4. `hasseAt_agreementLocator_pow_mul_eq_zero`:
   every `Lambda_G^q V` has zero agreement Hasse coefficients only in the
   strict range `j<q`.
5. `exists_locatorGrade_for_error_values`: for arbitrary `f:E->K`, there is
   `V` of degree `<|E|` such that

   ```text
   (Lambda_G^q V)(beta)=f(beta)       for every beta in E,
   Hasse_j(Lambda_G^q V)(alpha)=0    for alpha in G and j<q.
   ```

   The construction is literal depth-one Hermite interpolation after dividing
   by the nonzero scalars `Lambda_G(beta)^q`.
6. `exists_locatorGrade_for_error_jets`: for arbitrary depth-`m` error jets,
   there is a residual `V` of degree `<m|E|`.  It uses a Bezout inverse of
   `Lambda_G^q` modulo the error-jet denominator and proves equality of every
   Hasse coordinate.  This theorem is chiefly a cost guardrail.

No `decide`, `native_decide`, `sorry`, or nonstandard axiom occurs.

## Exact target arithmetic

The target constants are

```text
g=180413, e=81731, w=131071, m=47, D=47g=8479411.
```

Lean checks:

```text
e < g,
e < w,
q*g+e < 47g                           for every q<=46,
13g+e < Xwindow(SR*Y^43),
13g+e < Xwindow(SR*Y^44),
Xwindow(SR*Y^43) < 47e.
```

The last inequality is decisive.  The relevant numbers are

```text
Xwindow(SR*Y^43) = 2581219,
47e                  = 3841357.
```

So even `q=0` cannot hide all 47 error jets in that critical source line.
In contrast, error values cost only `e=81731`, and locator grades through 13
fit in the two target analogues of the finite witness heights.  The intended
transport must therefore be a 47-step triangular recurrence in locator/Hasse
order.  Saying that `q=1` "vanishes on G" is valid for values and false for
the other 46 Hasse coordinates.

At the top active-degree lines the taper is tighter still: the source windows
are only about 90,867--90,870, so only locator grade zero plus error-value
interpolation fits there.  Those layers must be reduced by the contact
recurrences before positive locator grade is requested; raw pointwise CRT is
not a global right inverse.

## Interaction with the L10/L11 cap ladder

Multiplication by `Lambda_G^q V` changes only the X exponent.  It consumes no
active `(Y,R,S)` degree and no passive `Z` degree.  Consequently this CRT
piece needs **zero** units of the L-cap slack.

The independent exact ablation found that adding only the 101 newly legal
active-total-11, `z=0` columns to L10 keeps boundary gain three: all 101 are
contact pivots and create no new relation.  Hence the fourth normal cannot be
attributed to the terminal active face.  If the complementary 1,860-column
ablation confirms gain four, the single-unit L11 repair is specifically the
new passive boundary `z -> z+1` on already legal active shapes.  Algebraically
that belongs to inversion of the `u0+u1 Z` anchor/contact recurrence, not to
the locator/error CRT above.

## Exact remaining module

After this file, the unknown is not error interpolation.  It is the associated
graded contact/locator confluence map:

```text
global tapered raw source
  -> product of agreement-local relaxed sources
  -> quotient by the product of universal local contact kernels
  -> error contact rows and four boundary rows.
```

For `m=8`, its first quotient has 91 locator/Hasse cells and the five local
665-dimensional kernels surject onto all 91; the error restriction then has
shape `6537 x 6784`, rank 6516, before the final `4 x 268` boundary Schur.
At target scale neither "91" nor the four finite witness columns may be
reused.  The required uniform statement must prove that each passive-Z
boundary correction can be made inside the next locator/Hasse filtration
without violating the shape-dependent X taper.  Once that is proved, the
theorems here supply the error-value pivot at every step and the existing HRS
reverse-Hasse induction supplies singleton error localization.

## Verification receipt

Command:

```bash
bash .experiments/run_lean_8g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/K0LocatorErrorCRT6900.lean
```

The isolated compile completed in about 5.5 seconds.  Every printed theorem
depends only on the expected `propext`, `Classical.choice`, and `Quot.sound`
(some arithmetic theorems omit `Classical.choice`).  There is no `sorryAx`.
