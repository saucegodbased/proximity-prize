# k0 cap-3757 relative attachment: exact producer and augmented-rank STOP

Date: 2026-09-14 UTC. Scope: lower-6900 k0 profile at exact
`(g,m,w,L,B,s,U)=(180413,47,131071,3757,16,8,64)`. This changes no
production submission.

## Classification

The parameter move to `L=3757` is a retuning, but the missing proof is
fundamentally new. The target is the first cap with a positive source margin;
`L=3756` has margin `-20,717,799`. Therefore the fourth conormal cannot be
proved by taking an already-certified old kernel vector and multiplying it by
`Z`.

That direct mechanism is also false on the exact audited kernel: all 317
candidate specializations are zero by the degree-47/root-multiplicity-48
argument, the value row has rank zero, and shifting or combining those
relations leaves boundary rank three.

The correct object is the relative map created by attaching the last passive
face.

## Formal result

`.experiments/K0RelativeAttachmentExactSequence6900.lean` proves, for
arbitrary fields and arbitrary old/face contact maps, the exact sequence

```text
ker C_old  -->  ker [C_old C_face]  -->
{f in face | C_face(f) lies in range C_old}  -->  0.
```

The second arrow is surjective without assuming that `ker C_old` is nonzero
or that `C_old` has a chosen pivot. Boundary space is then quotiented by the
image already produced by `ker C_old`, and the boundary map factors
canonically through the old-correctable new-face space. The central theorem is

```text
attachedNormal_surjective_iff_relativeConnectingBoundary_surjective
```

and its exact four-dimensional rank form is

```text
rank(relative connecting boundary) + rank(old normal image) = 4.
```

The dual form

```text
attachedNormal_surjective_iff_no_relative_dual
```

says exactly what a reverse-Hasse proof must establish: every covector on the
relative boundary quotient which annihilates all old-correctable cap-3757
face vectors is zero.

The file compiles with `lake env lean -j1 -M4000`. Printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `admit`,
`decide`, or `native_decide`.

## Exact dimension audit

The published target numbers are

```text
source columns                         65,061,789,117,960
all-node contact-rank budget           65,061,786,746,880
contact margin                                  2,371,080
```

Appending four boundary rows gives only

```text
dim ker(contact,boundary) >= 2,371,076.
```

This is now a formal theorem
`target_L3757_augmented_kernel_lower_bound`. It is a large space of vectors
which kill both contact and boundary, not evidence that the boundary image
has rank four. `dimension_margin_four_countermodel` gives an axiom-clean
falsifier: a five-dimensional source with zero contact and zero boundary has
four units of dimension margin and boundary rank zero.

There is a second, stronger conditional ledger for the new face. If one
proves that the actual rank increment across `3756 -> 3757` is bounded by the
difference of the published rank budgets, then

```text
new-face columns                        17,434,693,359
all-node rank-budget increment          17,411,604,480
old-correctable face dimension >=           23,088,879
relative contact+boundary kernel >=         23,088,875.
```

The formal theorems are
`target_lastFace_liftable_finrank_of_increment_bound` and
`target_lastFace_jointKernel_of_increment_bound`. Separate upper bounds on
the ranks at `L=3756` and `L=3757` do not imply the needed rank-increment
bound; a filtration-compatible nesting theorem for the accepted weighted
kernel family would be required. Even if that nesting theorem is supplied,
the resulting conclusion is still nullity, not boundary rank.

## What the commutator and CRT do—and do not—supply

`K0CriticalAdjacentCellCommutator6900.lean` proves the literal local identity

```text
nextY - u0*base - u1*nextZ = epsilon^(m+1) * (...).
```

Thus the three-cell combination gains a full contact order. This is a real
local syzygy, but its coefficients `u0,u1` vary by node.

`K0LocatorErrorCRT6900.lean` proves that locator grade `q` can prescribe
arbitrary error values while killing agreement Hasse coordinates strictly
below `q`. This is also exact, but it is one-grade-at-a-time interpolation.
It does not construct one tapered global raw vector realizing all required
nodewise three-cell relations.

Consequently these two results do not yet produce an element of the relative
domain, much less show that its boundary classes span the missing quotient.
Both statements remain true if the boundary map is identically zero, so the
formal countermodel above is also a logical falsifier for deriving rank four
from them plus dimension alone.

## First unproved producer hypothesis

After the routine literal identification of the cap-3757 raw source with its
old and last-face coordinates, the first genuinely unproved hypothesis is:

```text
For every nonzero covector ell on
  Boundary4 / boundary(ker C_3756),
there is a last-face vector f with
  C_face(f) in range C_3756
and
  ell(relativeBoundary(f)) != 0.
```

Equivalently, the canonical relative connecting boundary is surjective. In
the reverse-Hasse language, the required new theorem is a
filtration-compatible global realization/confluence result: it must lift the
adjacent `Y/Z` commutator and locator/error values through the actual tapered
raw source and retain a nonzero boundary pairing. The existing
`K0FullSourceShapeRealization` interface identifies the same global-lift
gap, but it has not been proved for the cap-3757 last face.

Until that producer is established, the honest status is STOP for a 6900
candidate: the uncertainty is no longer numerical source capacity or the
linear-algebra bridge; it is the single global tapered relative-separation
theorem above.
