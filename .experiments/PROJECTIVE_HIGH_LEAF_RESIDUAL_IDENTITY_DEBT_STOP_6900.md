# Projective-high same-witness residual identity debt: exact STOP

Date: 2026-09-15 UTC. Scope: the exact
`ProjectiveHighDataElevenHighEClosedIncidenceLeaf` introduced at `8b35e3e`,
with its original `U/Gamma/agreement/selected` witness. This is a compiled
route discriminator, not a 6900 candidate or submission.

## Verdict

The most direct one-ground-coordinate eliminant has extremely cheap degree
but catastrophically large identity mass.

Unpack the leaf's retained fixed-scalar witness

```text
E0 P_gamma = a + gamma b + Q(c + gamma d) scalar_gamma,
scalar_gamma(x_i) = centre_i             for i in agreement_gamma.
```

Define the two node functions

```text
A_i = E0(x_i) U0(i) - a(x_i) - Q(x_i)c(x_i)centre_i,
B_i = E0(x_i) U1(i) - b(x_i) - Q(x_i)d(x_i)centre_i.
```

The original selected agreement and the exact residual identity give

```text
A_i + gamma B_i = 0                      (i in agreement_gamma).
```

Thus each coordinate supplies the literal degree-one relation

```text
T_i(Z) = B_i Z + A_i.
```

Its cumulative degree over all 262144 nodes is at most 262144, far below the
consumer cap 42700739. The obstruction is nonidentity, not degree.

If two distinct retained seeds `gamma != delta` both own coordinate `i`,
subtracting their two equations gives

```text
(gamma-delta) B_i = 0,
```

so `B_i=0`, and either original equation then gives `A_i=0`. Therefore a
coordinate can be nonidentity for at most one retained seed. Choosing one
nonidentity owned coordinate for every seed that has one injects those seeds
into the 262144-node domain.

The retained scalar family has cardinality at least
`253511670984674103`. Consequently at least

```text
253511670984674103 - 262144
  = 253511670984411959
```

retained candidates own **only identity specializations** of these natural
relations. The exact one-coordinate consumer permits identity/uncovered mass
at most `1121769749`. The excess debt is

```text
253511670984411959 - 1121769749
  = 253511669862642210.
```

So this natural residual-coordinate eliminant misses its identity allowance
by more than 226 million times. No degree tuning can repair it.

## What the theorem consumes

`ProjectiveHighLeafResidualIdentityDebt6900.lean` works directly from the
lossless leaf. In particular it uses:

* the same retained `Good subset Gamma` and its exact lower cardinality;
* the same `agreement` and `selected` maps;
* the leaf's original selected agreement equality;
* the same scalar, centre and exact residual identity.

It does not switch witnesses, replace agreement sets, infer combinatorics
from the misleading name `cross_no_adjacent_hard_corner`, or use merely local
rank. The `projectiveHigh` field is retained by the input but is not needed:
projective highness cannot reduce this identity debt.

The main compiled declarations are:

* `residualCoordinateRelation_eval`;
* `residualCoordinateRelation_eq_zero_iff`;
* `identityOnlySeeds_relation_eq_zero`;
* `activeSeeds_card_le`;
* `identityOnlySeeds_card_lower`;
* `projectiveHigh_leaf_natural_residual_identity_debt`.

## Consequences for the ADHD routes

### Source-coordinate / characteristic-polynomial route

A quotient norm or characteristic polynomial is useful only if its
specialization is nonidentity on nearly every candidate. The obvious quotient
whose coordinate equations are the two residual rows fails before a
characteristic polynomial is formed: almost the entire retained family is in
its identity-only branch. Any replacement must introduce a genuinely new
relation on this branch, not package the same rows as a Fitting ideal or norm.

Also, a quotient which retains every selected seed as a distinct reduced
point cannot have module rank at most 42700739: its reduced length is already
at least the retained cardinality. A low-rank quotient must deliberately
identify candidates and separately pay its fibres; that payment is precisely
the unresolved identity/uncovered clause.

### Signature-panel / first-separator route

The same subtraction calculation proves that pairwise common agreement nodes
already lie in the identity locus of the natural affine relation. Hence
first-separator bookkeeping on these rows has essentially no nonidentity
mass to charge. The separate exact small-field panel control in
`adhd_signature_panel_separator_gate_6900.py` additionally shows that a fixed
evaluation panel can become injective exactly when its reusable equal-signature
difference factors disappear. The two stops agree: a panel needs a new
disjoint charge, not just a separating signature.

## What remains live

This result does **not** prove that every possible same-witness eliminant has
large identity debt. It kills the direct two-row residual relation and any
renaming of it. A live successor must do one of the following on the
identity-only majority:

1. use the original passive receiving factor to produce a new nonzero
   coordinate relation, with cumulative degree at most 42700739;
2. exploit a quotient-tail coefficient whose vanishing is not tautological
   on the fixed centre and pay every zero/identity fibre; or
3. construct an original-coefficient locus cover with total incidence cost
   below 90982740402923737.

The literal fixed-centre source permits the identity locus to be the whole
domain (`LargeIdentityLocusActualSourceTautologyStop6900.lean`), so identity
cardinality, projective-highness, or the aligned cross equations alone cannot
provide item 1 or 2.

## Verification

The source compiled in 6.5 seconds under the existing valuation compatibility
overlay, two Lean threads, and an 8 GiB address-space cap. Every printed axiom
set is a subset of

```text
[propext, Classical.choice, Quot.sound].
```

There is no `sorry`, `admit`, `native_decide`, `unsafe`, or declared axiom in
the source. Production and submission roots were not touched.

