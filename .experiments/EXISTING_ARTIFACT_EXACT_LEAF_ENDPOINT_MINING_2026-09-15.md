# Existing-artifact endpoint mining for the exact 6900 leaf

Date: 2026-09-15

## Verdict

No existing theorem is endpoint-ready: there is no assumption-free composition
from
`ProjectiveHighDataElevenHighEClosedIncidenceLeaf U Gamma agreement selected`
to `False`.  The benchmark-facing composition is already complete conditional
on precisely that missing statement:

```text
NoProjectiveHighDataElevenHighEClosedIncidenceLeaf6900
  -> targetBadFamilyBound_of_noProjectiveHighDataElevenIncidenceLeaf
  -> protocolClaim6900_of_noProjectiveHighDataElevenIncidenceLeaf
```

The producer side is likewise lossless:

```text
target_bad_family_small_or_projective_high_dataEleven_incidence_leaf
  -> Gamma.card < 254684620614660120
     OR the exact incidence leaf, with U/Gamma/agreement/selected unchanged.
```

The search criterion here was deliberately stricter than “has useful-looking
arithmetic”: a candidate had to consume that exact leaf, preserve its actual
witnesses, introduce no geometric/routing/rank premise, and reach the strict
target bound (or `False`). Symbol-reference tracing and theorem-call inspection
found no such consumer.

## Ranked surviving mechanisms

All three are YELLOW research directions, not GREEN endpoint compositions.

### 1. Actual agreement-locator residual plus the same scalar identity

This is the strongest exact invariant currently available.  The direct
consumer
`ProjectiveHighLeafAgreementResidualFactor6900.projectiveHigh_incidence_leaf_residual_factor`
gives, for every actual `gamma in Gamma`, a certificate for

```text
Q_gamma = interpolation of U0 + gamma U1
D_gamma = Q_gamma - selected_gamma = H_gamma * R_gamma
180413 <= deg Q_gamma <= 262143
H_gamma = supportLocator agreement_gamma
deg H_gamma = |agreement_gamma|, H_gamma monic, H_gamma base-field fixed
R_gamma != 0, deg R_gamma <= 81730.
```

On the same leaf, `cross_no_adjacent_hard_corner` supplies a retained actual
`Good`, the same selected family, and

```text
E0 * selected_gamma
  = a + C gamma * b + Qmin * (c + C gamma * d) * scalar_gamma.
```

Thus a mechanical algebra adapter gives the genuinely same-witness identity

```text
E0 * Q_gamma
  = a + C gamma * b
    + Qmin * (c + C gamma * d) * scalar_gamma
    + E0 * H_gamma * R_gamma.
```

This is the closest analogue of the accepted moving-fibre architecture: it
exposes a fixed two-dimensional received line, an actual locator, and a
low-degree residual, rather than inventing an unrelated phase witness.

Hard missing premise: a cross-seed theorem must turn the varying pair
`(H_gamma, R_gamma)` into either a bounded-degree eliminant family or a global
approximant/count.  To use
`SourceCoordinateEliminantIdentityAggregation6900.one_coordinate_remainder_lt`,
the produced relations must have cumulative seed degree at most `42,700,739`
and leave at most `1,121,769,749` uncovered/identity seeds.  No artifact proves
that conversion.  Per-seed factorization alone has no cardinality force.

### 2. Actual original-coefficient incidence cover

There is an exact, same-witness producer:

```text
incidence leaf
  -> toProjectiveHighDataElevenHighEClosedLeaf
  -> toDataElevenHighEClosedLeaf
  -> toWeightedLeaf.cross_weighted_low_window
  -> ActualOriginalCoefficientHyperplanes6900.exists_actual_hyperplane_family.
```

It gives `Good subset Gamma`,
`253511670984674103 <= Good.card`, an injective actual scalar family, the
original points `(gamma, selected gamma)`, at least `180413` incident fixed-node
hyperplanes per point, and pairwise common incidence at most `149776`.

Hard missing premise: an exhaustive bounded-complexity locus cover for these
actual coefficient points, followed by a count below the retained-family
budget.  The required cover cannot merely assume a curve/surface/routing
condition; it must be derived from the displayed residual identity.  No
downstream theorem consumes `exists_actual_hyperplane_family` and produces the
benchmark bound.  Existing point/curve degree ledgers are consumers without
this global producer.

### 3. Fixed residual identity-node concentration, followed by a narrow
top-coefficient count

The scalar residual can be evaluated nodewise and fed, without changing the
actual `Good`, support, scalar, or centre, to
`FixedLinearNodeSupportConcentration6900.scalar_residual_support_concentration_6900`.
It yields a fixed identity-node locus `Z` with

```text
217317 <= |Z|
|Good  supportCore(Good, agreement, Z)| <= 44827.
```

The already-proved
`LeadingCoefficientShortIdentityJohnson6900.boundary_W133120_card_le_of_identity_card_le_244509`
then gives the very strong cap
`Good.card <= 432277721144676`, but only under all of the following extra
premises: scalar degree at most `133120`, scalar coefficient fixedness, and
`244508 <= |Z| <= 244509`.

Hard missing premise: the exact leaf supplies only the much broader scalar
window (up to `149776`) and the concentration theorem supplies no upper bound
on `|Z|`.  Neither the high-degree scalar strata nor the large-`Z` strata are
closed.  Consequently this is a useful branch consumer, not a universal leaf
consumer.

## Adversarially rejected near-misses

1. **Natural residual / quotient-norm aggregation is quantitatively RED.**
   `projectiveHigh_leaf_natural_residual_identity_debt` proves that at least
   `253511670984411959` retained seeds are identity-only for the natural two
   residual rows, vastly exceeding the allowed `1,121,769,749` identity mass.
   `projectiveHigh_leaf_no_small_seed_faithful_identity_quotient` further proves
   that preserving the seed coordinate on those identities forces quotient
   rank at least `253511669862642210`, not the admissible `42,700,739`.

2. **Literal moving-quotient injectivity is true but has no adequate endpoint
   consumer.**
   `exists_actual_moving_quotient_injective` gives an injective map
   `gamma |-> scalar_gamma / E`, with `1 <= deg E <= 18705`, on the actual
   retained `Good`.  The triple-routing theorem assumes
   `HasChargedNodeTripleRouting84`; that premise is not derived.  More
   importantly, its conclusion is merely
   `Good.card < 254684620614660120`, which is compatible with the known lower
   bound `253511670984674103` and does not pay `Gamma \ Good`.  It therefore
   does not exclude the exact leaf even if the routing premise were supplied.

3. **Projectively constant locators close only the constant stratum.**
   `ProjectivelyConstantLocatorFamily6900.card_le_one_of_supportLocators_projectively_equal`
   is a valid recurrence-coset injection, but the exact leaf does not make all
   actual locators projectively equal and provides no bounded cover by such
   classes.  Replacing “varying base-fixed locator” by “common locator” would be
   a hidden assumption.

4. **The projective high-tail rank statement points in the wrong direction for
   a low-rank closure.**  The exact theorem gives a two-dimensional independent
   tail.  Likewise, the post-high-E scalar theorem proves rank greater than 31,
   not an upper rank usable by a finite list count.

5. **The order-seven approximant receipts are local.**  They establish a legal
   dimension budget and a live reversed coefficient, but no uniform joint
   kernel or seed-count theorem.  The order-eight and order-nine artifacts
   record explicit degree/rank stops, so treating the local receipt as a tower
   is not valid.

6. **The accepted 6811 proof is an analogy, not an importable endpoint.**  Its
   moving-fibre carrier/factor/count chain is downstream of stronger source
   margins.  At agreement `180413`, the missing step is exactly the new source
   theorem represented by mechanism 1; none of the accepted count theorems can
   be instantiated directly with the current leaf.

7. **Unaugmented generic-locator determinants vanish identically.**
   `ProjectiveHighLeafGenericLocatorDeterminantStop6900` consumes the exact leaf
   and proves that the degree-`81731` generic locator matrix has kernel finrank
   at least `7459`, hence rank at most `74273`; every `74274`-square (and every
   maximal-column) minor is zero.  Therefore mechanism 1 cannot be finished by
   simply taking a generic Hankel/locator determinant.  A viable determinant
   route must derive candidate-dependent augmentations and pay both their seed
   degree and their identity fibres.

## Scheduling consequence

Do not spend another cycle packaging conditional wrappers.  The only route
that improves the exact frontier is mechanism 1: prove or falsify a
cross-seed eliminant/global-approximant theorem for the coupled identity with
`H_gamma R_gamma`.  Mechanism 2 is the independent geometric alternative.
Mechanism 3 should be used only if a new theorem first forces its missing
degree and identity-size strata.  The quotient-norm and assumed-routing paths
should remain frozen.
