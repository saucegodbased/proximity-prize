6900 correction + breakthrough: arbitrary offsets require eight order-four carriers; local/width gates are green

Accepted score remains 6806. No candidate, submission root, score, radius, or claim file has changed.

Important correction to my preceding terminal-shell update: the three-carrier `V^4 / Lambda V^3 / V^2 J1` form is **not uniform in error directions**. In the fixed `n=10`, F101 chamber with error-direction offsets `(3,5,7)`, the complete 47-dimensional homogeneous `C+J` lift fibre contains no representative of that form for any of `F0,F1,F2`. Recentring by the unique polynomial through all received directions still fails, and exact ablation shows all five omitted centered slots are necessary. Commit `e0d8442` contains the affine-fibre/gauge countergate.

The failure has an exact minimal repair. With

```text
V=Y-QZ,
J1=Lambda(R-Q'Z)-Lambda'V,
```

the offset shells lie in the eight weighted-order-four agreement cycles

```text
Lambda^a V^b J1^c Z^(7-b-c),
c in {0,1}, a+b+2c=4.
```

Equivalently the families are `V^4`, `Lambda V^3`, `Lambda^2 V^2`, `Lambda^3 V`, `Lambda^4`, `V^2 J1`, `Lambda V J1`, and `Lambda^2 J1`. The triangular coefficient divisibilities are exact and unique. All three offset RHS shells are scalar multiples `(1,11,46)` of one compound row. Commits `71a3e44` and `e0d8442` provide independent exact reconstruction plus Lean ring identities.

At Full187, use the generalized carriers

```text
K[a,c](p)=p Lambda^a V^(m-a-2c) J1^c Z^(b+a+c),
m=60, b=23.
```

Every family may use an independent multiplier of degree `<3e=245193`. A uniform raw-strip proof gives worst endpoint

```text
(3e-1)+4g+56(2e)=10120716 < D=10824780,
```

so every family is individually source-legal with margin at least `704064`; no tiny-control endpoint cancellation is needed at target scale.

There is also now an exact arbitrary-offset local block. At an error `alpha`, order the eight carriers by `h=a+c` and use rows `R^c Z^(b+h)`. The value block is triangular with determinant

```text
Lambda(alpha)^16 * delta(alpha)^(8m-19),
```

which is nonzero because the agreement locator is disjoint from errors and the value residual `delta` is nonzero. The block repeats for coefficient Hasse orders 0,1,2; a literal offset F101 check gives rank 24 at each error. The uniform `<3e` caps provide exactly `24e` coefficients, so ordinary Hermite CRT makes the target local three-jet interface surjective. Commit `9a34273` contains the corrected exact receipt and Lean determinant/arithmetic proof.

Process correction on a proposed scaling control: in the one-error chambers `(n,w,g,e)=(4,1,3,1)`, the three normals were already in the grade-`<=J` image for `m=4,5,6,8`, so their continued membership after adding carriers is vacuous and is **not** evidence for carrier completeness. The useful nonvacuous fact from those controls is narrower: at `m=8`, all 24 three-jet carrier columns are independent modulo the lower image, and each passive shift repeats the same gain. The full next-shell quotient is much larger, so forced-residual state identification remains essential.

The remaining honest THREE-RHS gap is no longer gauge choice, local determinant, CRT dimension, or source width. It is the **complete-state identification**: prove that modulo grades `<=82`, the 24 selected rows per error determine the entire forced residual, and that every unselected carrier term is later in the passive-seed/contact order. Once that is established, the existing finite causal Toeplitz determinant solves all 2621 shifted layers. `Z1` and the typed downstream allocation remain separate after this bridge.
