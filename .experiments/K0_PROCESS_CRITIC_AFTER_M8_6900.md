# K0 process critic after the m8 selected-family RED

Date: 2026-09-14 UTC. Scope: lower-6900 full-source dual route. This is a
logical/evidence audit, not a new local lemma or candidate change.

## Correct verdict

The m8/L12 calculation is a real exact result about its selected family, but
it is **not a target-faithful RED for the full-source route**. Its full source
fails the very capacity premise which creates the target kernel:

```text
(n,w,g,m,B,s,U,L)       (8,3,5,8,3,1,12,12)
full source columns                     11,711
published one-node rank bound            1,531
n * rank bound                           12,248
full-source margin                         -537
```

The exact `6812/6812/0/0` result therefore proves only that

```text
{1,R} + subcritical S + SY^7R + SY^8(Z^0,Z^1)
```

does not possess its own relation in that chamber. It falsifies an
unconditional *standalone sparse-family* theorem. It does not furnish a
nonzero dual compatible with the full target-positive source, and it cannot
refute a proof which genuinely uses constraints supplied by the omitted high
R/S layers. The note in `949c79b` was correctly amended to retract the
stronger target conclusion.

This downgrade does not rehabilitate a sparse-source dimension argument. The
exact target frontier in `dba7cca` shows that every proper nested m47
envelope has negative margin under the published rank bound; only the full
envelope is certified positive. The higher derivative layers are
load-bearing capacity scaffolding even if a final normal form has low target
shape.

## Premise graph and the hidden assumption

The sound proof order is:

```text
positive full-source ledger
  -> assume four-boundary rank defect
  -> obtain ell != 0 and eta compatible with the FULL contact map
  -> use full raw-coordinate adjoint equations
  -> derive a tapered error HRS recurrence
  -> force ell = 0, contradiction.
```

`K0WeightedRawAdjointRecurrence6900.lean` correctly starts `eta` from the
full map. That is genuine progress. But an argument which subsequently
evaluates the compatibility equation only on vectors supported in
`k0CriticalFilteredCarrier` has not used the high-layer constraints. On
those vectors, full compatibility supplies exactly the same equations as
compatibility with the restricted low map.

The unproved predicate `K0CriticalFilteredShapeRealization` is therefore the
critical hidden premise. It asks for a low-supported global vector which
simultaneously cancels agreement pairing and realizes a prescribed error
shape. Neither full-source dimension surplus nor local triangularity implies
this. Treating the predicate as a mechanical consequence would reintroduce
the sparse-family surjectivity/confluence claim which the exact controls warn
against.

There is also a profile-consistency hazard. The typed raw map currently uses
`(s,L)=(8,3757)`, whereas the newer positive endpoint uses `(6,5107)`.
Target-shape identities are reusable, but a compatible dual, raw lift, and
source realization must all belong to one fixed profile. Results from these
two spaces cannot be spliced silently.

## WeightedTerm: reject the carrier, retain the reduction rule

The prior rejection of `weightedTerm` was correct only in its direct-carrier
form:

```text
contact(weightedTerm) = 0,
```

so pairing it directly with `eta` yields `0=0` and exposes no HRS moment.

It was too strong to discard the family entirely. Its triangular expansion
can in principle be oriented as a **local Gröbner reduction rule**: a high
raw target monomial occurring as its initial term can be replaced by lower
target terms. Then the actual equations still come from legal high global
raw columns in the full map, while `weightedTerm` only supplies their local
normal form. This is the plausible mechanism by which high capacity layers
could constrain a low-dimensional final numerator.

That use is not yet a theorem, for three reasons:

1. `weightedTerm_coeff_self` has initial coefficient containing powers of
   `v`; it is not a unit reduction for every raw monomial.
2. The rank proof constructs kernel families independently in each local
   source. It does not construct one tapered global raw vector realizing
   those nodewise reductions.
3. Pulling the local normal forms back through node translation introduces
   node-dependent `u0,u1` coefficients. CRT interpolation of those
   coefficients may overflow the strict X windows; this is exactly the
   unresolved confluence/taper gate.

Thus the noncircular opportunity is narrow: reduce the contact image of each
*actual full-source global column* locally, then prove that the resulting
all-node transpose has a legal common global numerator. Crediting the local
kernel count itself as global multiplier capacity would be circular.

## What currently changes target confidence

| Evidence | Honest update |
|---|---|
| Full m47 source/consumer arithmetic is positive | Strong feasibility evidence only; no boundary rank theorem |
| Rank-adaptive full-map dual and raw/HRS adjoint are formal | Strong interface progress; the mathematical realization premise remains open |
| Literal three-cell identity retains `u1*Z^2` | Removes the old pair-only counterexample, but gives no global taper by itself |
| m5 adjacent critical cells close generic controls | Mechanism evidence; not profile-universal |
| m8/L12 selected family is injective | Strong negative evidence against sparse-family-only proofs; essentially no direct update on full target DUAL0 because capacity is negative |
| Target nested-envelope frontier | Strong negative evidence against pruning high layers or borrowing the full rank certificate for a low family |
| Source-positive m5/m6 complete-source controls have gain four | Moderate positive evidence for the full-source route, weakened by their special small receipts |
| Conditional `lambdaS * Q'' = 0` endpoint | Complete semantic endpoint, conditional on the missing global recurrence |

The local three-cell repair should therefore not raise target confidence by
itself. The principal uncertainty is not the local algebra; it is whether
the high full-source constraints admit a global tapered normal form.

## Single highest-information next gate

Use one receipt and one **capacity-positive** m8/B3 chamber, and compare the
selected family with the complete source. The prepared correction is

```text
(n,w,g,m,B,s,U,L)       (8,3,5,8,3,1,12,16)
full source columns                     17,679
published one-node rank bound            2,179
n * rank bound                           17,432
full-source margin                         +247
selected corrected family columns        9,964
```

Compute normal gain as

```text
rank([contact ; boundary]) - rank(contact),
```

first for the selected family and then for the **full source**, rebuilding
and ranking sequentially rather than allocating a nullspace and its square
kernel matrix. Do not run broad shape ablations first.

The three possible outcomes have distinct decisions:

1. selected gain four: the corrected adjacent mechanism survives its first
   capacity-aware discriminator;
2. selected gain below four but full gain four: high layers genuinely kill
   the residual dual, so the next theorem must orient `weightedTerm`/full
   raw equations as a global normal-form reduction;
3. full gain below four: a capacity-positive exact-chamber counterexample to
   the present full-source theorem template, requiring a route/profile pivot.

This one comparison is more informative than another local identity or a
one-family ablation because it tests the exact logical distinction currently
at risk: sparse recurrence versus constraints inherited from the complete
positive-margin source.
