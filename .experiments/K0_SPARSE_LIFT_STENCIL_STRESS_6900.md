# k=0 sparse-lift stencil stress test (exact stage)

## Question and verdict

The first tracked fourth-boundary relation in the small `m=3`, `p=101`
seed used only five raw face cells,

`Z^3, Y Z^2, Y^2 Z, R Z^2, Y R Z`.

This is **not a datum-uniform local stencil**.  It is reproducible under the
seed translation and one structured change of all three off-agreement
directions, but it changes sharply for the two arbitrary-direction data
families.  One such family does not reach boundary rank four after the entire
positive face.  A cross-field `m=3` control also does not reach four, and the
`m=4` witnesses require seven or fifteen face-cell types.

Accordingly, the five-cell pattern is useful evidence for a narrower
polynomial/structured-direction identity, but it cannot be the target-uniform
6900 lift mechanism by itself.

## Semantics and safety

The test uses the literal flattened contact

`X = x + eps`,
`Y = u0 + u1 Z + eps R - eps^2 S + eps^3 T`,
`eps^m = 0`,

and the formal Hasse-normalized boundary (`S = Hasse2(P)`).  Sparse column
elimination tracks an exact source relation.  Every reported witness is
rechecked by summing its literal contact columns to zero before its boundary
is inspected.

The script deliberately does **not** use the exploratory
`associated_top_contact_conditions` block in
`k0_small_full_face_sparse_lift_6900.py`.  Merely centering `Y` by `QZ`
without transporting `R`, `S`, and the connection terms does not preserve the
flattened contact map, so those conditions are not evidence.  This note makes
only raw-coordinate rank and support claims.

## Exact results

All extensions below attach the newly available positive-`Z` face, not every
new zero-`Z` column of the successor cap.  `normal` means the rank of the four
formal boundary rows on the literal contact kernel.

| profile / datum | contact rank old -> face extension | normal rank old -> face extension | first fourth witness |
|---|---:|---:|---|
| seed `m3 p101`, prefix/poly, `gamma=0` | `246 -> 386` | `3 -> 4` | face position 88; support `295=228 old+67 face`; 5 face cells, raw/R only |
| same, `gamma=5` | `246 -> 386` | `3 -> 4` | same position, support counts, and 5 face cells |
| seed, spread/arbitrary, `gamma=0` | `256 -> 398` | `0 -> 4` | position 145; support `343=218+125`; 8 face cells including S and R2 |
| same, `gamma=5` | `256 -> 398` | `0 -> 4` | position 145; support `359=234+125`; same 8 face cells |
| seed, random/arbitrary, `gamma=0,5` | `255 -> 398` | `0 -> 3` | **no fourth relation** |
| seed, one error-node `u1 += 1` | `252 -> 393` | `2 -> 3` | **no fourth relation** |
| seed, all 3 error-node values `u1 += 1` | `246 -> 386` | `3 -> 4` | position 91; support `250=167+83`; the same 5 face cells |
| cross `m3 p17`, prefix/poly | `241 -> 379` | `1 -> 3` | **no fourth relation** |
| cross `m3 p17`, either arbitrary family | `242 -> 385` | `0 -> 0` | no boundary event |
| cross `m4 p101`, prefix/poly | `539 -> 717` | `2 -> 4` | position 96; support `541=493+48`; 7 raw/R face cells |
| cross `m4 p101`, spread/arbitrary | `539 -> 720` | `2 -> 4` | position 193; support `600=445+155`; 15 face cells, all shapes |
| cross `m4 p101`, random/arbitrary | `539 -> 720` | `2 -> 4` | position 193; support `656=503+153`; 15 face cells, all shapes |

In all 14 runs, zero individual face columns were contact-correctable by the
old source.  Thus every new boundary event is genuinely a multi-column face
relation, never a one-column lift.

The seed five-cell raw types are exactly

```
(Y,R,S,Z) = (0,0,0,3), (0,1,0,2), (1,0,0,2),
            (1,1,0,1), (2,0,0,1).
```

Their invariance under `gamma=0 -> 5` is expected from the translated datum
symmetry and is a useful regression.  Their survival when all three error
directions are shifted together, but failure after changing only one error
direction, is evidence of global interpolation structure rather than a
node-local identity.

## Consequence for the 6900 route

This closes a misleading branch: do not try to formalize the five raw cell
types as a universal lift.  The next useful invariant has to account for the
globally coupled off-agreement directions, either through the exact relative
obstruction map or through a construction that explicitly interpolates those
directions.  The fact that the arbitrary `m=4` witnesses recruit S and R2
also says that discarding derivative shapes is not stable across jet order.

These are finite structure-discovery controls, not a target-size theorem, and
the first relation depends on deterministic column/pivot order; no
minimal-support claim is made.

## Receipt

- Script: `.experiments/k0_sparse_lift_stencil_stress_6900.py`
- Cases: 14 exact runs
- Full-receipt canonical SHA-256:
  `a0f6f6221578bf0567159312afd8a50a58bf6186bfb66fddd35dd48254652ce9`
- Script SHA-256:
  `071deec746a18997b0dc2e221637fc90b39d3552e5758d9281cb75b973612111`
- Runtime: 28.668 seconds
- Peak RSS: 44,636 KiB
- Address-space cap: 4,294,967,296 bytes

