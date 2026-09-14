# Full187 pure face: patched CompPoly Lee--O'Sullivan interface

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production or
submission file is changed.

## Exact identification

The pure `R=S=Z=0` contact problem is not merely analogous to a
Guruswami--Sudan interpolation module. It is literally the instance already
implemented and proved sound and complete by patched CompPoly.

Let `Omega=X^N-1`, and let `Rcv(X)` be the degree-`<N` polynomial which is
zero on the agreement roots and one on the error roots. The graph-point ideal
is

```text
J = (Omega, Y-Rcv).
```

The two-value description from `5801b65` is the same ideal:

```text
J = (E*Y, G*(Y-1)).
```

Indeed both cut out the same reduced graph over all `N` distinct roots, and
the existing target receipt gives the explicit indicator

```text
Rcv = G * (N^-1 X E').
```

The second factor is `G^-1 mod E`, so `Rcv=0 mod G` and `Rcv=1 mod E`.
Because the point maximal ideals are pairwise comaximal, total Hasse contact
order 60 is exactly `J^60`.

Use the CompPoly parameters

```text
messageDegree       = 131072
yWeight             = 131071
multiplicity        = 60
weightedDegreeBound = 10824779 = D-1.
```

Then `interpolationYCap=82` and `leeOSullivanWidth=83`. CompPoly's basis row
`i` is exactly

```text
Y^(i-t) * (Y-Rcv)^t * Omega^(60-t),   t=min(i,60),  0<=i<=82.
```

Thus its 83-row module is the complete bounded-`Y` pure contact module needed
here, with shift `i*131071`. This supersedes the earlier concern that a new
contact-completeness theorem had to be written for this face. That concern
remains valid for the full `(Y,R,S,Z)` module, but not for the bivariate pure
face.

The field match is also exact: `KoalaBear.fieldSize=2130706433`, and the
library exposes a native-word fast KoalaBear Lee--O'Sullivan context with a
proved canonical-field bridge.

## What the library does and does not decide

The public correctness theorem proves the executable interpolation operation
complete for distinct `X` coordinates whenever any bounded nonzero witness
exists. Its shifted reducer is proved row-span preserving and weak Popov.
Consequently the semantic-to-polynomial-module bridge is already verifier
clean.

This does **not** yet settle the affine boundary problem. The stock operation
selects one least-degree nonzero row; the Full187 packet needs coefficient
`[Y]Q=H^59 Rloc^60`, not an arbitrary scalar normalization. We must either:

1. inspect/combine every reduced row below `D` and solve this fixed coefficient
   equation; or
2. use the same complete Lee basis in an affine shifted-Pade membership test.

The direct executable reducer is elementary Mulders--Storjohann reduction.
At target size its raw 83-row power basis is far too large to materialize
naively, so merely calling the stock operation is not yet a memory-safe target
computation. The useful breakthrough is the already-formalized exact module
and completeness theorem, not a claim that the target run has completed.

An external research-only checkout of the official PML library was built in
`/tmp` to investigate a fast PM-basis realization. It is not submission
source and must not be copied into a verifier root.

## Formal replay

```bash
cd /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work
lake env lean -j1 \
  .experiments/Full187PureFaceLeeOSullivanInterface6900.lean
```

The probe compiles and checks the exact field, weight, cap, width, strict
bound, certified fast context, Lee basis constructor, completeness theorem,
and fast-reducer equality theorem. It uses no `native_decide` and introduces
no axiom.

## Decision

```text
GREEN_EXACT_COMPPOLY_LEE_MODULE_AND_COMPLETENESS_INTERFACE
OPEN_FIXED_LINEAR_COEFFICIENT_MEMBERSHIP_AND_MEMORY_SAFE_REDUCTION
```

