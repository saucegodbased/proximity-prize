# K0 affine-mismatch geometric recurrence: exact target STOP

Date: 2026-09-15 UTC. Scope: lower 6900, corrected low head
`epsilon^0,...,epsilon^43`. No production file, candidate, claim, or
submission root is changed.

## Verdict

**RED for the natural common-residual geometric recurrence.** The recurrence
is mathematically valid, but its literal target source leaves the weighted X
cap after only five error orders for the `Y/R/S` boundary lanes and six error
orders for the passive `W` lane. It must reach order 44 to annihilate the
corrected low head.

This is not a proof that every possible matrix-valued or shape-changing
annihilator is impossible. It is a precise STOP for the most direct concrete
realization of the four-dimensional nodal recurrence defect.

## The recurrence tested

Let `H` be the degree-`g` locator of the agreement nodes. Interpolate the two
received symbols globally and form the received-line residual

```text
J = Y - U0(X) - U1(X) W.
```

At every old node, literal K0 contact sends `J` to a series with zero constant
coefficient, hence contact order at least one. At an agreement, `H` also has
order one; at an error, `H` is a unit. Therefore the canonical rung

```text
F_t(B) = H^(44-t) J^t B
```

has agreement order 44 and error order `t`. This is exactly the tempting
geometric recurrence: use successive `t` to kill the old error coefficients,
while agreement contact remains invisible to the low head.

The order equation is sound:

```text
(44-t) + t = 44.
```

The failure is source legality, not local contact algebra.

## A faithful worst-case branch

A theorem uniform in the received word must allow a full received interpolant
of degree `n-1=262143`. This is not a fictitious degree bound. For an
adversarial instance one may take a zero candidate, include zero among the
agreement nodes, put

```text
U1 = 0,
U0 = H * X^(e-1),
```

and take all error nodes nonzero. Then `deg U0=g+e-1=n-1`, `U0` vanishes on
the `g` agreement nodes, and it is nonzero on every error node.

Projecting `F_t(B)` first to active residual degree zero and then to `W=0`
isolates the unique binomial branch

```text
(+ or -) H^(44-t) U0^t B.
```

Its coefficient is exactly `+1` at `t=6` and `-1` at `t=7`, so there is no
characteristic-dependent binomial coefficient to save the construction.
For monic `H,U0`, Lean proves that the X degrees are exact, not upper bounds:

```text
t=5: (44-5)g + 5(n-1) = 8,346,822
t=6: (44-6)g + 6(n-1) = 8,428,552
t=7: (44-7)g + 7(n-1) = 8,510,282.
```

## First failed recurrence equations

The literal K0 strict cutoff is

```text
D = 47g = 8,479,411,
w(Y)=131071, w(R)=131070, w(S)=131069, w(W)=0.
```

For the active boundary lanes the active-zero branch at `t=5` is still
legal, with tiny slack:

```text
B=Y: 1,518
B=R: 1,519
B=S: 1,520.
```

The next, epsilon-six recurrence equation requires the `t=6` branch, which is
already illegal by

```text
B=Y: 80,212
B=R: 80,211
B=S: 80,210.
```

The passive lane survives at `t=6` with X slack 50,859, but its epsilon-seven
equation requires `t=7`, whose X degree alone exceeds `D` by 30,871.

`K0AffineMismatchGeometricRecurrenceStop6900.lean` checks all five literal
source caps through `rawShapeLegal`, proves the exact monic degree equalities,
and proves the unique-branch algebra identities. Thus the contradiction is a
specific source monomial forced by the proposed carrier, not a heuristic
dimension count.

## Relation to the fixed four-carrier audit

Independent commit `2345ece` reaches the same process decision from the
dual/coefficient side. The epsilon-zero matrix of

```text
H^43 A, H^42 B1, H^41 B2, H^44 W
```

is invertible at every error. If corrections stay in those same four
families, the recurrence forces 44 Hasse jets of each coefficient polynomial
to vanish at all `81,731` errors. That costs degree `44e=3,596,164`, while the
largest coefficient window is only `590,583`. Hence the fixed-family repair
is also RED.

Together the two receipts rule out both obvious incarnations of the
four-dimensional recurrence:

- multiplying by the common received residual accumulates one error-degree
  payment per rung and hits the explicit epsilon-six/seven cliff;
- keeping the original four carrier shapes accumulates error-Hermite
  multiplicity and exceeds the coefficient window by over three million.

Any surviving annihilator must introduce genuinely new contact-order shapes
and show, at every order, how their earlier coefficients cancel without
accumulating either of these two costs. It cannot be described as merely
reusing the same four rows with a geometric or polynomial-coefficient update.

## Replay and trust

```bash
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/\
K0AffineMismatchGeometricRecurrenceStop6900.lean
```

The replay completes in about three seconds under Lean's 3.5-GiB allocator
cap. Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, `decide`, `native_decide`, explicit axiom, or
unsafe declaration.

