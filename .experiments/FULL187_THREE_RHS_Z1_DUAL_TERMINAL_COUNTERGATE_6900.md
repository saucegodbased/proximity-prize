# Full187 three-RHS plus Z1: exact dual terminal countergate

Date: 2026-09-13 UTC. Scope: lower-6900 source research only. No production,
submission, score, or claim file was changed.

## Result

The Full187 producer has a strictly smaller exact dual target than DUAL4 or
whole-error-space surjectivity.  Work over the coefficient field after the
literal source is restricted to the agreement-contact kernel:

```text
U = ker C_G,
J = J_YRS : U -> k^3,
D = C_E : U -> E,
z = J_Z : U -> k,
delta_i = C_E(F_i),  i=0,1,2.
```

Put `W = ker J`.  The three prescribed Full187 corrections are exactly

```text
delta_i in range(D|W),  i=0,1,2.                         (P-3)
```

Their smallest exact dual annihilator condition is

```text
for every lambda in E*,
  D*lambda in range(J*)
    => lambda(delta_0)=lambda(delta_1)=lambda(delta_2)=0. (D-3)
```

Indeed `D*lambda in range(J*)` is equivalent to `lambda` annihilating
`D(ker J)`.  Thus a failure certificate is only

```text
lambda in E*, mu in (k^3)*, i in {0,1,2}
D*lambda = J*mu,    lambda(delta_i) != 0.                (FAIL-3)
```

It is neither a full contact-row relation nor an assertion that every error
syndrome is correctable.  This is the exact terminal-Schur condition to test
after a terminal quotient calculation has supplied the induced `D` and `J`.

The residual Z condition remains independent.  Once `(P-3)` is established,
the normalized Z row exists iff

```text
z* notin range((D,J)*).                                  (D-Z1)
```

Equivalently, the sole Z failure certificate is a pair

```text
lambda in E*, mu in (k^3)*,
z* = D*lambda + J*mu.                                    (FAIL-Z1)
```

This is the dual form of “`z` is nonzero on `ker D intersect ker J`”.  It
does not follow from the three syndrome equations, and no additional terminal
dimension statement enters either test.

`Full187ThreeRHSZ1DualAnnihilator6900.lean` formally proves both equivalences
and their conjunction.  Its theorem names are

```text
threeCorrections_iff_threeRHSAnnihilator
normalizedZ_iff_z1DualNoncontainment
threeCorrections_and_normalizedZ_iff_dualGate.
```

The first theorem has no finite-dimensional hypothesis: it uses the exact
annihilator/range identity, so it applies equally to a finite terminal Schur
quotient and to a polynomial-module presentation after scalar extension.

## Terminal use

For a prefix/terminal split `C(p,f)=C0(p)+CT(f)`, first form

```text
K_T = ker((W/range C0) <- CT).
```

Choose any correction lift for terminal vectors and reduce its boundary by
the prefix-kernel boundary image.  The resulting terminal maps are the
`D,J,z` above.  A valid terminal calculation need prove only that `(FAIL-3)`
and `(FAIL-Z1)` cannot occur.  In particular, the raw shell surplus
`127554977` is not an input to either assertion; it cannot certify a
prescribed syndrome value or rule out `z*` containment.

## Low-E/rank-40/occupancy-three test: no contradiction

The remaining DataEleven leaf supplies scalar-family information, not a map
from the scalar family into the reduced Full187 cokernel.  The named numerical
conditions therefore do not contradict `(FAIL-3)` or `(FAIL-Z1)`.  Here is an
explicit compatibility model.

Set

```text
M = 253511670984674103,
E0(X) = X^18414,
P_gamma(X) = sum_(j=0)^39 gamma^j X^j,
Gamma = {0,1,...,M-1} subset Q.
```

Exact checks are

```text
deg E0 = 18414 < 18415,
deg P_gamma <= 39 <= 131071,
|Gamma| = M >= 40.
```

The forty rows `P_0,...,P_39` have coefficient determinant

```text
det(gamma^j)_(0<=gamma,j<40)
  = product_(0<=a<b<40) (b-a)
  = product_(b=1)^39 b! != 0,
```

so this scalar-polynomial family has rank exactly forty (it lies in the
40-dimensional span of `1,X,...,X^39`).  For arbitrary `A(X),B(X)`, a member
of the literal affine pencil satisfies

```text
P_gamma = A + gamma B
  => gamma^2 = [X^2]A + gamma [X^2]B.
```

The right condition is one nonzero monic quadratic in `gamma`; it has at most
two roots.  Hence every literal pencil fibre has occupancy at most `2 <= 3`.

Independently take the reduced-contact linear data

```text
U = Q^4,       E = Q,       J(x0,x1,x2,t) = (x0,x1,x2),
D(x0,x1,x2,t) = x0,         z = 0,
F0=(1,0,0,0), F1=(0,1,0,0), F2=(0,0,1,0).
```

The `F_i` have the identity (hence triangular) Y/R/S jet.  With
`lambda = id_Q` and `mu` the first coordinate covector,

```text
D*lambda = J*mu,
lambda(D(F0)) = 1 != 0.
```

This is `(FAIL-3)`.  Also `z*=0` is in `range((D,J)*)`, namely with both
covectors zero, so `(FAIL-Z1)` holds as well.  Taking the direct product with
the scalar family above makes the rank-forty, occupancy-two, retained-size,
and `deg E0=18414` statements coexist with both dual failures.

This is not claimed to be a counterexample to the complete target leaf: it
does not attempt to satisfy the literal Full187 source/contact geometry.
It is the precise countergate requested by the stated summaries: rank at
least 40, occupancy at most 3, and `deg E0 < 18415` alone contain no
source-to-dual map and therefore cannot imply either required noncontainment.
Any successful use of those leaf hypotheses must add a concrete map forcing
the terminal certificates `(FAIL-3)` and `(FAIL-Z1)` to violate a source,
degree, or contact identity.

## Formal and arithmetic receipt

The Lean arithmetic theorem checks exactly

```text
18414 < 18415,  39 <= 131071,  2 <= 3,
40 <= 253511670984674103.
```

Command, under the repository's task-local `-M3500` (under 4 GiB) cap:

```text
.experiments/run_lean_4g_capped.sh \
  .experiments/Full187ThreeRHSZ1DualAnnihilator6900.lean
```

It exits zero and prints only `propext`, `Classical.choice`, and `Quot.sound`.
No dense rank computation, `decide`, or `native_decide` is used.
