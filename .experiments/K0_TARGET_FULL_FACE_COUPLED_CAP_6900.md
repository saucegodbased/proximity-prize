# Target full-face coupled cap: exact weighted-kernel bridge

Status: **GREEN production local-kernel homogeneity/count ingredients once the
companion Lean file finishes its production-module replay; YELLOW as an
assembled target associated-rank certificate.  Complete-contact liftability
and boundary separation remain OPEN.**

## Result in plain language

The new passive layer at target cap 3757 contains 17,434,693,359 legal global
coefficients.  At one evaluation node, the exact new layer of the relaxed
second-jet source has 91,368 coordinates.  It also contains 24,948 explicitly
independent relations built from the production `weightedVector/weightedTerm`
family.  These relations are homogeneous in passive degree, so they really do
live in the new associated face rather than mixing the old and new caps.

Therefore these ingredients give the candidate one-node associated rank cap

```text
91,368 - 24,948 = 66,420.
```

Across 262,144 nodes this is 17,411,604,480 rows, leaving

```text
17,434,693,359 - 17,411,604,480 = 23,088,879
```

dimensions in the kernel of the associated top-face map, once the actual
global cap-3757 face map is explicitly factored through the direct sum of the
normalized local exact-face contact maps.

This is the first target-native positive dimension calculation in this lane.
It is not yet a 6900 proof: the global-to-local associated-map factorization
still has to be assembled in Lean; after that, an associated relation can have
lower-passive contact terms that are not in the image of the cap-3756 source,
and a liftable relation must still give the missing boundary direction.

More precisely, the 66,420 bound is a **per-node normalized local associated
cap**. Summing it over nodes only bounds the image in the direct sum of
nodewise associated targets; it supplies no lower-grade correction. Killing
the lower remainder requires membership in the image of the one global
cap-3756 source. Allowing unrelated nodewise corrections would be a strictly
coarser problem. Passing from the associated kernel to a global lift is
exactly the filtered obstruction problem, not a consequence of the count.
The m4 rank-15 countercheck below demonstrates the distinction concretely.

## Exact production bridge

`K0FullFaceCoupledCap6900.lean` imports the actual
`ProximityPrize.SubmissionLower.LowerGeometry` definitions.  It proves:

1. Every support monomial of

   ```text
   weightedVector r h a b i j z l
   ```

   has passive degree exactly `h+a+b+i+j+z`.  The proof applies the existing
   signed support bound twice, with passive weights `(0,1,1,1,1)` and their
   negatives.  This upgrades the existing one-sided support inequality to
   equality.

2. Under `flatEquiv`, the exact vector used by the production relaxed family
   is `weightedTerm`; its contact is divisible by `epsilon^m` whenever
   `m <= r+2a+b`.  This is a direct wrapper around the production
   `flatEquiv_weightedVector` and `weightedTerm_vanishes` lemmas.

3. `KernelFaceBlock` is the subtype of the production
   `SecondJetRelaxedRank.Block` satisfying passive degree exactly `L`.
   `kernelFaceMake` is the production `weightedMake`, restricted to these
   exact-face blocks and followed by the production outer truncation.

4. `kernelFaceMake` is injective by the production triangular initial-term
   theorem `truncateOuter_weightedMake_injective`.

5. `kernelFaceMake` has zero complete local contact, using the exact production
   budget identity `r+2a+b=m`.  In particular it lies in the associated
   top-face kernel.

6. A finite equivalence removes the uniquely determined terminal `Z`
   exponent from every exact-face block.  The remaining clipped two-coordinate
   sum has exactly 24,948 elements at `(m,B,s,U,L)=(47,16,8,64,3757)`.

7. A second finite equivalence removes the uniquely determined `Z` exponent
   from the exact face of the production `SecondJetRelaxedSpace.Index`.  Its
   target cardinality is exactly 91,368.

The 24,948 kernel count uses `decide` only on a compact closed sum (47 outer
rows, 9 curvature rows, and small clipped rectangles).  The 91,368 source
count first proves that its inner cutoff is vacuous at the target and then
normalizes the resulting finite sums.  Neither count enumerates an ambient
`Fin 3758` cube, and neither uses `native_decide`.

## Raw-S attribution

The deterministic Python enumerator also reports cumulative certificates by
the raw-S cap:

| raw-S cap | global face minus all-node coupled cap |
|---:|---:|
| 0 | -72,401,997 |
| 1 | -93,031,377 |
| 2 | -81,942,429 |
| 3 | -55,257,276 |
| 4 | -25,165,875 |
| 5 | **+73,983** |
| 6 | +16,136,673 |
| 7 | +22,628,736 |
| 8 | **+23,088,879** |

So the raw-R/Y portion and all cumulative truncations through raw S=4 are
insufficient for this certificate.  Raw S=5 is the first load-bearing tier.
These rows are cumulative coupled certificates: `q(m,s,r,h)` changes with the
curvature cap, so they must not be presented as independent additive exact-S
contributions.

As a control, the raw-only face has 278,534,035 global columns against an
all-node bivariate Hermite cap of 295,698,432, a deficit of 17,164,397.  Thus
the small-profile raw-face recurrence (`2g-w=n`) is accidental and cannot
justify the target result.  The derivative shapes, especially through raw
S=5, are essential.

## Relationship to the filtered obstruction

Commit `7dcbada` defines

```text
obs : ker(top) -> Wlo / range(oldContact)
```

and proves that `ker(obs)` is exactly the truly liftable relative face.  It
also packages the obstruction and boundary in the single mapping-cone class

```text
ker(top) -> (Wlo x Boundary) / range(oldContact, oldBoundary).
```

After the still-explicit global associated-map assembly, the surplus will prove

```text
23,088,879 <= dim ker(top).
```

The exact unconditional continuation is only

```text
23,088,879 - dim(Wlo / range(oldContact)) <= dim ker(obs).
```

A small error-supported obstruction factor would have closed much of this
gap, but commit `e522925` falsifies that generic route: in a correct literal
m4 chamber with two errors the obstruction has rank 15, greater than `3e=6`,
and survives scalar epsilon-zero, all epsilon-zero, and three-layer scalar
packets.  The m6 chamber has obstruction zero only vacuously.  Consequently a
target-specific identity, not generic triangularity, is required.

## Deterministic replay

```text
PYTHONHASHSEED=0 python3 \
  .experiments/k0_target_full_face_coupled_cap_6900.py
```

Latest exact output:

* canonical SHA-256:
  `3698e0da2b14c662399605913425add6e9f9dbd29a7110bf2c2431e765068528`
* script SHA-256:
  `32c235226c691e6d6a6ada15863750dd823075565e79d180c76cd34934b5b1f0`
* runtime: 0.055438 seconds
* peak RSS: 19,116 KiB

Lean replay (after the production module is built):

```text
lake env lean .experiments/K0FullFaceCoupledCap6900.lean -j1 -M4200
```

## Honest remaining premises

1. Assemble the actual global cap-3757 associated-face map and prove its rank
   is bounded by the direct sum of the local 66,420-dimensional images.
2. Bound or kill the literal target filtered obstruction `obs`; generic
   epsilon-zero/error-packet factorization is RED.
3. On the resulting liftable subspace, show that the relative connecting
   boundary has the missing fourth direction.  The abstract terminal detector
   is available, but no target-uniform producer for its premise has been proved.
4. Only after all three steps should this associated certificate be assembled into
   a submission theorem.
