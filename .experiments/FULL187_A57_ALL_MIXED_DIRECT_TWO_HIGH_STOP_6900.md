# Full187 A57: all mixed direct channels remain RED after the two-high-row cut

Date: 2026-09-14 UTC  
Scope: lower-6900 experiments only  
Decision: **STRUCTURAL STOP for every direct mixed `U0/U1` predecessor**

## Result

The projective endpoint argument newly forces the high-degree tails of the
two received rows to be linearly independent.  That is a real strengthening,
but it does not repair the direct Full187 A57 construction.

Take the exact pair

```text
U0 = X^133121,
U1 = X^133120.
```

For every `(a,b) != (0,0)`, the polynomial `a*U0+b*U1` has degree at least
`133120`.  Thus this pair satisfies the strongest currently proved
projective endpoint invariant, not merely the separate degree lower bounds
on the two rows.

Grant the direct A57 source a deliberately stronger envelope than the
physical construction: for every total received-row power `0<=t<24` and
every `0<=k<=t`, let the mixed channel

```text
U0^k * U1^(t-k) * V_(t,k)
```

vary independently throughout the complete physical residual window for
total power `t`.  There are

```text
sum_(t=0)^23 (t+1) = 300
```

such channels.  Their monomial shifts are

```text
(t*133120+k) mod 262144,
```

and their residual dimensions are

```text
t even: 208036+t,
t odd :  76964+t.
```

Every shifted interval ends before coefficient `255186`.  Their union is
exactly the prefix `[0,255185]`, so even this enlarged independent-channel
envelope has rank at most `255186` and defect at least

```text
262144 - 255186 = 6958.
```

The Lean theorem kernel-checks the only implication needed for the STOP:
every admissible term, and hence their complete double sum, has coefficient
`255186` equal to zero.  It also proves the hostile pair's every-direction
degree lower bound.  The printed axioms are exactly

```text
[propext, Classical.choice, Quot.sound].
```

## Relation to the preceding one-row STOP

Commit `8848d88` used `U1=X^133120` and all 24 direct `u0`-free channels.  It
proved exact image prefix `[0,255162]` and defect `6981`.  Adding every mixed
positive-`U0` monomial for the smallest high-tail-independent pair extends
the prefix by only 23 coefficients.  The remaining 6958-dimensional suffix
is not a coefficient accident or a missing physical group; it survives an
envelope in which all mixed groups are allowed to vary independently.

This means the new projective endpoint breakthrough must feed one of:

1. an indirect source outside the direct physical predecessor family;
2. a whole-family count for directions with deficient A57 multiplication;
3. an actual-packet theorem confining the A57 right-hand side to the direct
   image.

It must not be cited as making the old direct A57 map universally onto.

## Forward cutoff sensitivity

An independent 24-interval merge (not part of the Lean theorem) gives the
following exact monomial-pair envelope ranks if a stronger scalar-list cut
raises the hostile pair to `(X^(D+1),X^D)`:

```text
D       rank       defect
133120  255186       6958
133217  257417       4727
133222  257532       4612
133376  261074       1070
133423  262144          0
```

Thus the newly found numerical scalar frontier `W=133221` would materially
shrink this particular obstruction but would not remove it.  Direct
surjectivity for this hostile monomial family first appears at high cutoff
`D=133423`, far beyond the current weighted architecture.  This table is a
route-selection diagnostic, not a universal rank theorem for arbitrary row
pairs.

## Artifact

```text
.experiments/Full187A57AllMixedDirectPredecessorsTwoHighStop6900.lean
```

Fresh capped compilation took about six seconds and used no `sorry`,
`decide`, or `native_decide`.
