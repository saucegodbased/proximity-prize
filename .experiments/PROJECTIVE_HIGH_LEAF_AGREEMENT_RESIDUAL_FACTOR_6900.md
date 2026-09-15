# Projective-high exact-leaf agreement residual factor

Date: 2026-09-15 UTC. Scope: lower score 6900 only. This is a verified
same-witness reduction, not a proof of `ProtocolClaim6900`, a candidate, or a
submission.

## Outcome

`ProjectiveHighLeafAgreementResidualFactor6900.lean` now proves, for the
literal
`ProjectiveHighDataElevenHighEClosedIncidenceLeaf U Gamma agreement selected`
and every actual `gamma in Gamma`, that there is a nonzero polynomial
`R_gamma` such that

```text
Q_gamma - selected(gamma) = H_gamma * R_gamma,
deg R_gamma <= 81730,

Q_gamma = interp_all_nodes(U0 + gamma U1),
H_gamma = product_{i in agreement(gamma)} (X-domain(i)).
```

It also proves the coefficient form that is relevant to a global
approximant. For every `k > 131071`,

```text
coeff_k(H_gamma R_gamma)
  = coeff_k(V0) + gamma * coeff_k(V1),

V_r = interp_all_nodes(U_r).
```

Thus the high coefficients of every varying product `H_gamma R_gamma` lie
on the same affine two-row canonical pencil. The agreement locator is monic,
has degree exactly `|agreement(gamma)|`, and is coefficientwise fixed by the
target Frobenius.

## For-dummies explanation

Each candidate polynomial matches the received word at at least 180413
evaluation points. The canonical polynomial representing that entire
received word has degree at most 262143 and, on this projective-high leaf,
degree at least 180413. Subtracting the candidate cannot cancel that high
degree because the candidate has degree only 131071.

The difference vanishes at every matched point, so it contains one linear
factor for each of those points. Removing all at least 180413 factors from a
polynomial of degree at most 262143 leaves a nonzero quotient of degree at
most

```text
262143 - 180413 = 81730.
```

Above degree 131071 the candidate contributes no coefficients, so the
product of the large locator and short quotient must reproduce the fixed
two-row received pencil exactly.

## Exact fit to the missing no-leaf proposition

The exported endpoint theorem is

```text
projectiveHigh_incidence_leaf_residual_factor
  (leaf : ProjectiveHighDataElevenHighEClosedIncidenceLeaf
    U Gamma agreement selected)
  (hgamma : gamma in Gamma) :
  exists R_gamma != 0,
    Q_gamma - selected(gamma) = H_gamma * R_gamma and
    deg R_gamma <= 81730.
```

It consumes the same `U`, `Gamma`, `agreement`, and `selected` appearing in
`NoProjectiveHighDataElevenHighEClosedIncidenceLeaf6900`. No family exchange,
shrinking, abstract replacement, or supplied residual is used. The stronger
`projectiveHigh_incidence_leaf_residual_high_coefficients` theorem retains
those same witnesses and exposes the common affine high-tail constraint.

## Endpoint budget verdict

No numerical family cap improves yet. In particular this file does **not**
prove the missing no-leaf proposition.

The new data replace an arbitrary selected polynomial by a large varying
base-field locator times a short nonzero residual. They do not yet bound how
many pairs `(H_gamma,R_gamma)` can realize the shared affine high tail.
Counting locators independently is hopeless: even complements of size at
most 81731 have vastly more possible supports than the 6900 allowance.
Counting residual coefficients independently is equally hopeless.

The exact remaining mathematical hinge is therefore a cross-seed Padé or
semilinear eliminant theorem that charges the variation of `H_gamma` while
using the common affine pencil. It must produce a cumulative exceptional
degree below the endpoint allowance, not just a per-seed quotient bound.

The existing natural residual-coordinate quotient/norm route cannot serve
as that theorem: its formally proved identity majority is at least
`253511670984411959`, and after spending the full identity allowance the
seed-faithful quotient rank is still at least `253511669862642210`, far above
the cumulative degree gate `42700739`. The present product-tail relation is
different data, but no existing consumer was found that turns it into the
needed global cap.

## Verification and process audit

- The complete file checks in about five seconds through the isolated
  library shim.
- The check used the shared capped runner, two global probe slots, one Lean
  worker for the proof, and no benchmark-sized evaluation.
- An initial monolithic proof caused elaborator allocation failures because
  concrete target-index expressions were repeatedly unfolded. Splitting the
  algebraic factorization and interpolation facts into small generic lemmas
  reduced the check to a stable low-memory run. This was a proof-engineering
  issue, not a mathematical failure.
- A separate cached-module audit reports exactly
  `{propext, Classical.choice, Quot.sound}` for every exported theorem.
- Source scan finds no `sorry`, `admit`, `native_decide`, or `unsafe`.

## Honest next test

Do not enumerate `(H_gamma,R_gamma)` or revisit the already stopped natural
coordinate/norm packaging. The next useful test is whether an existing
same-witness source theorem can turn

```text
highTail(H_gamma R_gamma) = highTail(V0 + gamma V1)
```

and Frobenius-fixedness of `H_gamma` into one fixed, bounded-degree
semilinear approximant. If every resulting equation still carries an
independently varying locator or quotient, record STOP; it is not a family
count.
