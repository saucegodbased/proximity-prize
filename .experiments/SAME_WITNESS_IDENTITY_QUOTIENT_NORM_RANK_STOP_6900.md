# Same-witness identity quotient/norm rank STOP

Date: 2026-09-15 UTC. Scope: the exact
`ProjectiveHighDataElevenHighEClosedIncidenceLeaf`, its retained
`Good/agreement/selected` witness, and the natural fixed residual rows from
`ProjectiveHighLeafResidualIdentityDebt6900.lean`. This is a formal research
gate, not a candidate or submission.

## Verdict

**GREEN theorem, RED route.** Repackaging the natural residual identity rows
as an exact finite agreement quotient, a Fitting algebra, or a quotient norm
cannot repair their identity debt while keeping the endpoint rank/degree
budget.

The previous same-witness theorem proves that the natural row relations have
at least

```text
253,511,670,984,411,959
```

identity-only seeds. Give the quotient the weakest literal meaning needed by
a characteristic-polynomial argument:

* it is a finite-dimensional algebra `A` over the challenge field;
* it contains an element `z` representing the seed coordinate; and
* every retained seed `gamma` gives an algebra character `chi_gamma : A -> K`
  with `chi_gamma(z)=gamma`.

Dedekind independence says the distinct characters are linearly independent
in the linear dual of `A`. Since evaluation at `z` recovers `gamma`, the
characters really are distinct. Consequently

```text
number of retained seed characters <= finrank_K(A).
```

This statement does not assume that the quotient is reduced, radical,
generically smooth, or presented by a complete intersection.

## Exact endpoint obstruction

Spend the full permitted identity/uncovered allowance:

```text
identity seeds                         253,511,670,984,411,959
maximum discarded                       1,121,769,749
minimum characters still represented 253,511,669,862,642,210
maximum quotient rank / degree gate               42,700,739
rank excess                            253,511,669,819,941,471
```

Thus any quotient that remains seed-faithful after the permitted deletion has
rank at least `253511669862642210`, more than `5,936,938,699` times the allowed
rank `42700739`. Conversely, a quotient of allowed rank must collapse or omit
almost every identity seed. Those seeds are then uncovered and exceed the
allowed mass by the same enormous margin.

The direct theorem

```text
projectiveHigh_leaf_no_small_seed_faithful_identity_quotient
```

extracts the `Good`, `row0`, and `row1` from the exact lossless leaf and says
that no rank-`<=42700739` finite algebra can retain its seed coordinate on all
natural identity seeds after deleting only `<=1121769749` candidates. There
is no witness switch.

## What this kills, and what it does not

This closes the quotient-norm binary gate proposed in
`ADHD_SAME_WITNESS_ENDPOINT_PIVOT_2026-09-15.md` **for the natural two residual
rows**. The obstruction applies equally to a characteristic polynomial,
determinant/norm, or Fitting presentation of their exact incidence quotient:
changing the presentation does not change the independent characters.

It does **not** prove that every possible new relation has the same identity
locus. A viable quotient/norm pivot must first produce genuinely different
same-witness equations that make all but `1121769749` candidates nonidentity;
it cannot merely repackage the current row equations. Nor does this theorem
rule out a non-exact compression carrying an independently proved fibre-size
bound. Such a fibre bound would itself be the missing global theorem and must
be charged explicitly.

## Formal receipt

`.experiments/SameWitnessIdentityQuotientNormRankStop6900.lean` proves:

* `seed_faithful_characters_card_le_finrank`;
* the exact after-discard rank theorem;
* the two endpoint arithmetic bounds; and
* the direct adapter to the exact projective-high DataEleven incidence leaf.

It compiled under the established 8 GiB compatibility shim in under five
seconds. Printed dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`; the source contains no `sorry`, `admit`, `native_decide`,
`unsafe`, or declared axiom.

## Scheduling consequence

Freeze natural-residual Fitting/norm repackagings. The only honest reopen is a
new relation whose nonidentity coverage is proved on the same retained family,
or a seed-fibre compression theorem with total uncovered mass at most
`1121769749`. Work should therefore return to source-specific coupling (the
huge-family scalar/divisibility structure) rather than another presentation
of the degree-one rows.
