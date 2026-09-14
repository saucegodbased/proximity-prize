# m69 exact endpoint composition gate: one universal no-leaf premise

Date: 2026-09-14 UTC. Scope: lower target 6900. Production, score, radius,
candidate, and submission roots are unchanged.

## Outcome

`M69DataElevenNoLeafEndpointBridge6900.lean` fixes the exact outgoing theorem
that the m69 program must prove. Define

```text
NoDataElevenHighEClosedLeaf6900 :=
  for every received pair U, seed family Gamma, agreement family A,
  and selected-polynomial family P,
    DataElevenHighEClosedLeaf U Gamma A P -> False.
```

The new Lean theorem proves

```text
NoDataElevenHighEClosedLeaf6900
  -> SelectedBadGivenSetsBound domain 131071 81731
       254684620614660120.
```

The conclusion is definitionally the proposition consumed by the existing
axiom-clean theorem

```text
Order2ProtocolBadFamily6900.protocolClaim6900_of_bad_family
```

to produce

```text
ProtocolClaim 6900 10461695 33554432.
```

Thus there is no missing numerical or combinatorial step after a universal
no-leaf theorem. Conversely, an m69 result which handles only one rational
function, one received word, one deficient shape, or each residual separately
does not fill the premise.

## Exact proof edge

For arbitrary data satisfying the definition of `SelectedBadGivenSetsBound`,
the already compiled DataEleven dichotomy gives

```text
Gamma.card < 254684620614660120
  OR Nonempty (DataElevenHighEClosedLeaf U Gamma agreement selected).
```

The new premise removes the second alternative. The strict first alternative
implies the required weak inequality. The only arithmetic conversion in the
adapter is

```text
Fintype.card Index - 81731 = 262144 - 81731 = 180413,
```

which matches the agreement threshold expected by the DataEleven theorem.

## Current theorem DAG

Closed:

```text
arbitrary selected bad family
  -> small family OR actual DataElevenHighEClosedLeaf

no actual DataElevenHighEClosedLeaf
  -> TargetBadFamilyBound6900
  -> ProtocolClaim 6900.
```

Active source side:

```text
DataElevenHighEClosedLeaf
  -> normalized coprime E0,N0 and W=N0/E0                 CLOSED
  -> deg E0 in 2151..18414, deg N0<=149776               CLOSED
  -> exact m69 deficient-shape/coefficient census         CLOSED executable
  -> actual incoming residuals all divisible by W         CLOSED in model;
                                                            leaf adapter OPEN
  -> concrete physical prefix-dual encoding               OPEN
  -> individual rational containment
       z>=3276                                             CLOSED in model;
                                                            leaf adapter OPEN
       1125<=z<3276                                        CONDITIONAL on adapter
       deg N0<=130508                                      CONDITIONAL on adapter
       z<=1124 and deg N0>=130509                          OPEN Padé gate
  -> simultaneous shared-tail allocation/confluence       OPEN
  -> construct the full source contradiction/no-leaf      OPEN
  -> endpoint bridge                                       CLOSED.
```

The last source-to-no-leaf edge is intentionally listed separately from
confluence. A complete residual section still has to be shown to contradict
an actual leaf through the precise Full187/m69 consumer; it cannot be inferred
from source dimension or local rank alone.

## Process and packaging finding

A direct experimental import of both the legacy DataEleven stack and the
modern endpoint stack triggered the known declaration collision

```text
Mathlib.RingTheory.Valuation.Integral
versus declarations copied into ProximityPrize.SubmissionLower.V6.
```

The source theorem was therefore compiled against the existing isolated
library-backed V6 compatibility shim. The production submission must replace
the copied legacy V6 block with the canonical library import before combining
the two stacks. This is a real assembly task, but not a mathematical gap.

The adapter compiled in about five seconds under the 3.5-GiB Lean allocator
cap and prints only

```text
[propext, Classical.choice, Quot.sound].
```

It contains no `sorry`, `admit`, `decide`, `native_decide`, unsafe declaration,
or generated table.

## Completion-credit rule

Only a theorem that inhabits `NoDataElevenHighEClosedLeaf6900`, or a stronger
universal theorem directly implying the same selected-family bound, closes
the active mathematical cut. The following remain valuable research facts
but receive no endpoint-completion credit by themselves:

```text
one monomial reciprocal rank;
one coefficient target in one prefix image;
all coefficients individually in possibly incompatible images;
a conditional dual recurrence without the concrete source encoding;
positive source-minus-target dimension;
one fixed target instance.
```

This interface is the guard against repeating the earlier confidence error:
every future GREEN must name the exact arrow it closes in the displayed DAG.
