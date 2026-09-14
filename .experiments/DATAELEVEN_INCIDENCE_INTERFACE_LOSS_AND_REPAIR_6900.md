# DataEleven same-family incidence interface: exact loss and repair

Date: 2026-09-14 UTC. Scope: lower-6900 research interface only. No
production submission file or score changed.

## Binary verdict

The current `DataElevenHighEClosedLeaf` is **not strong enough as a theorem
interface** to exclude the reciprocal/high-high controls by same-family
incidence. Its upstream constructor receives

```text
deg selected_gamma <= 131071
180413 <= |agreement_gamma|
selected_gamma(x_i) = U0(i) + gamma U1(i)
one original received row is bad on agreement_gamma,
```

but the structure stores none of these four fields.  Its terminal
fixed-scalar payload only asserts `scalar_gamma(x_i)=centre(i)` for
`i in agreement_gamma`; it does not assert that those sets are large.

This is an interface RED, not a mathematical counterexample to the full
benchmark assumptions.  It explains why attempts to use the current leaf
alone repeatedly failed to turn the enormous retained family into a
constraint on the received pair.

## Kernel-checked discriminator

`FixedScalarIncidencePayloadLoss6900.lean` proves that the exact
`FixedScalarWeightedNoAdjacentHardCornerCondition` payload admits all of the
following simultaneously:

```text
constant c=1 and d=0;
every nonzero constant received direction has canonical degree >=260095;
the complete fixed-scalar/pole/minimum/excess/no-adjacent record;
|Gamma| >= 253511670984674103;
agreement_gamma = empty for every gamma.
```

The construction reuses the already checked reciprocal plane payload with
`E0=X^2049-theta`, `Q=1`, and `s=0`.  The new theorem explicitly extracts
the retained `Good subset Gamma` field to prove the ambient family is huge,
then proves that the omitted `180413` agreement lower bound is false.

Therefore no argument whose input is only
`cross_no_adjacent_hard_corner` (even together with projective high tails)
can invoke the `98682` pair-overlap root bound or any stronger actual
agreement incidence.  The hostile payload survives precisely because empty
agreements make its centre-equality clause vacuous.

## Lossless repair and exact caller

`DataElevenHighEClosedIncidenceRepair6900.lean` defines
`DataElevenHighEClosedIncidenceLeaf`, extending the old leaf with exactly the
four omitted caller hypotheses, and proves the lossless endpoint

```text
target_bad_family_small_or_dataEleven_high_e_closed_incidence_leaf.
```

This theorem is a direct wrapper around the existing endpoint and exchanges
no witness.  Future same-family work should consume this repaired record (or
keep the original hypotheses as theorem arguments).  The exact downstream
consumer remains the missing no-leaf theorem

```text
DataElevenHighEClosedIncidenceLeaf ... -> False,
```

which would feed the already green bad-family-to-`ProtocolClaim 6900`
closure.  The repair does not prove that theorem; it makes the information
needed to state it available.

## What this says about the A57 hostile pair

The monomial/high-reciprocal controls are not evidence against the full
benchmark family, because actual `180413`-node agreement can kill simple
low-denominator reciprocal words by a cleared root count.  They *are*
evidence against the old erased leaf API: that API cannot express the root
count's decisive premise.  Accordingly:

- degree-only A57 promotion remains stopped;
- a full-leaf counterexample was not claimed;
- rebuilding deep `DataEleven` ancestry for the reciprocal control was
  intentionally avoided;
- the next legitimate incidence theorem must start from the repaired leaf
  and visibly use `agreement_card` plus `selected_agrees` (and probably
  `selected_bad`).

No `decide`, `native_decide`, finite-field enumeration, or large computation
is used.
