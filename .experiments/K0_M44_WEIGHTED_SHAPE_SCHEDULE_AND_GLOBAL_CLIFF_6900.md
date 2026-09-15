# K0 order-44 shape schedule: local GO, global locator STOP

Date: 2026-09-15 UTC. Scope: lower 6900 only. This changes no production
submission, score, or claim.

## Verdict

The accepted weighted `U/J/V` algebra really does contain a cap-respecting,
shape-changing **local** schedule through contact order 44. It is not just a
dimension heuristic. However, the schedule is translated separately at each
node, and no existing theorem lifts an arbitrary family of those local normal
forms to one global raw polynomial. The standard source-literal replacement,
an order-44 full-agreement partial-locator packet multiplied by the error
locator, survives only through error order 6 and fails at order 7.

Therefore this lane is:

```text
node-local weighted order ladder                         GO / exact
simultaneous raw lift of independently translated ladder OPEN
full-G partial-locator + error-locator globalization     STOP at 7
complete order-44 global schedule                        NOT OBTAINED
```

This is a real reduction in uncertainty: `U/J/V` avoids 44 local coefficient
jets, but it does not by itself evade the global interpolation problem.

## 1. Exact local shape change

In the accepted local variables, put

```text
V = A-R,
U = V + epsilon*S.
```

The literal contact substitution is

```text
A -> R-epsilon*S+epsilon^2*T,
```

so `U -> epsilon^2*T` exactly. The following schedule uses no repeated Hasse
jets of a coefficient polynomial:

```text
0 <= t < 24:   epsilon^t
24 <= t <= 44: epsilon^(t-16) * U^8.
```

For the high range its contact is exactly

```text
epsilon^t * T^8.
```

The switch at 24 is forced by the raw support condition `a+b<=r`: with eight
`U` factors one needs outer exponent `r=t-16>=8`. Every high rung obeys the
literal target caps:

```text
outer epsilon exponent <=28<47
curvature/second-derivative exponent a=8<=8
weighted derivative cost 2a=16<=16
active degree 8<=64
total degree 8<=3757.
```

`K0M44WeightedShapeSchedule6900.lean` proves the exact contact identity and
membership of every truncated rung in

```text
SecondJetRelaxedSpace.source 47 3757 16 8 64 (fun _ => 64).
```

In particular, the final local normal form is the explicit accepted shape

```text
epsilon^28 * U^8  ->  epsilon^44 * T^8.
```

This is the genuinely shape-changing mechanism missing from the fixed four
carrier family. It demonstrates that the local algebra does not inherently
require 44 jets of four polynomial coefficients.

## 2. Why this is not yet a target schedule

`epsilon` and `U` above live in a contact chart centered at one node and its
received pair. For different errors, they are different translated raw
linear combinations. The accepted weighted kernel proof constructs and
counts these relations *after localization*. It does not prove that an
arbitrary choice of one such relation at every node is the localization of a
single global raw coefficient vector.

The exact missing statement was already named
`K0WeightedNodeFamilyLiftable` in
`K0WeightedRawAdjointRecurrence6900.lean`. Neither `make_zero` nor
`exists_weighted_global_contact` is a right inverse onto prescribed nodewise
weighted parameters. Treating the local schedule as a global raw schedule
would repeat that type error.

## 3. Strongest literal partial-locator globalization

To test whether the local ladder could be replaced by a standard global
carrier, retarget the osculating packet from agreement depth 47 to the actual
low-head depth 44. Let `G` be the full agreement locator, `E` the error
locator, and let an osculating packet have internal agreement contact weight

```text
d = i + 2*r + 3*s <= 44.
```

Before an external X shift its top weighted degree is `44*g-d`. Multiplying
by `E^t` gives a literal global carrier of agreement order 44 and error order
`t`, with top weight

```text
44*g - d + t*e.
```

This already grants the packet the best possible `d`-unit refund. At the
target

```text
g=180413, e=81731, D=47*g=8479411.
```

A concrete maximal-refund shape is `A^41*B2`, with `d=41+3=44`, active
degree 42, derivative cost at most 2, curvature exponent at most 1, and total
degree at most 42. Thus all non-X caps are extremely safe.

The four original boundary carriers can be boosted without changing their
leading error matrix:

```text
H^43*A    -> H^2*A^42       d=42
H^42*B1   -> H*A^41*B1      d=43
H^41*B2   -> A^41*B2        d=44
H^44*W    -> H^3*A^41*W     d=41.
```

At an error, the common `A^41` multiplies the old invertible leading matrix
by the nonzero value residual to the 41st power. Multiplication by `E^t`
moves the first error contact to order `t`. This is a genuine change of raw
shape, not the fixed-carrier Hermite recurrence.

The exact strict-cutoff ledger is nevertheless decisive:

| boosted carrier d | slack at t=6 | overage at t=7 |
|---:|---:|---:|
| 42 | 50,895 | 30,836 |
| 43 | 50,896 | 30,835 |
| 44 | 50,897 | 30,834 |
| 41 | 50,894 | 30,837 |

More generally, every `d<=44` packet fits for `t<=6`, while every such packet
fails at `t=7`, even with `d=44`. External X shifts only worsen the result.
The low head needs all orders through 43, so this cannot be completed.

## 4. Process decision

Do not spend more time tuning `i,r,s` inside the standard order-44
partial-locator packet: the universal `d<=44` inequality already grants its
best possible source refund and still fails at the seventh equation.

The only surviving use of the weighted ladder is a new simultaneous-global-
lift theorem that couples node-local `U/J/V` relations through raw
coefficients or passive-seed syzygies. That is a qualitatively new theorem;
it cannot be inferred from the accepted local rank subtraction. Until such a
theorem is proved, this route supplies no 6900 candidate.

## Verification

The Lean receipt compiles with

```text
env LEAN_PATH=.experiments lake env lean -j1 -M4200 \
  .experiments/K0M44WeightedShapeSchedule6900.lean
```

in about five seconds. Printed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, `admit`, `decide`,
`native_decide`, explicit axiom, or unsafe declaration.
