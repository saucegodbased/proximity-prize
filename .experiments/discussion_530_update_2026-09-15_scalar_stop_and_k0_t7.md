### 2026-09-15 update: 6811 retarget stopped; scalar chamber closed; K0 t7 correctly scoped

The accepted lower floor is **6811** (`cdb451f`).  There is still no 6900
candidate, build, comparator run, or submission.  The numerical gap is 89
points, but the remaining gap is mathematical rather than mechanical.

#### Accepted-6811 retarget

Commit `b0bc617` replays the accepted 6811 source at the exact 6900 target.
The literal scalar arm `(m,L,s)=(115,159,35)` is short by `508361706`
coefficients (about a 1.063% rank reduction would be needed).  The principal
geometric A/B/T sources and every recorded phase source are also negative.
This rules out a parameter-only retarget of the accepted certificate.

Commit `ff9c2fc` then audits the truncated seedless RCN279/RCN285 escape:

* all 12,497,599 saturated truncated profiles through `m=5000` are negative;
* monotonicity plus the protocol-capacity cutoff reduces every viable
  saturated profile to 617,276 exact frontiers, all negative;
* all clipped profiles with `L<m` are negative by explicit algebra;
* 12,410,311 arbitrary clipped profiles through `m=300` are negative.

The best saturated deficit is `-456472`; the best arbitrary scanned deficit
is `-163462`.  Scope caveat: the unbounded unsaturated chamber `L>=m` is not
yet formally closed, because saturation is not a premise of the consumer.

#### K0 compatible-boundary corrections

The earlier order-six/order-seven generic minors sampled `J!=0`, whereas the
actual compatible fresh boundary has `J=0`.  Commits `20ee01c` and `ebf64ed`
formally retract those rank-four claims.  Every pure weight-seven packet has
boundary rank at most three there; the formerly advertised J-power order-six
gradients all vanish.

A different locator-lifted contact-seven packet does have the correct formal
boundary symbol:

```text
H^37 * (N^6 J, N^5 C1, N^4 C2, N^7 Z).
```

Commit `9490bb6` proves the target-facing top-support bridge.  On the
projective-high same-witness leaf, for each actual seed `gamma`, the canonical
interpolant of `U0+gamma*U1` has degree at least `180413`: its degree is already
above the selected-polynomial cap `131071`, and agreement with `P_gamma` at
`180413` distinct nodes forces the nonzero difference to reach that degree.
Thus its reversed first support is at most `81730`.

This validates choosing coefficient X cap `M=81731`; it does not prove
surjectivity.  Exact small-field falsification found a target-compatible rank
failure at passive cap `K=2`.  The current surviving experimental box is
`(M,K)=(81731,3)`:

```text
unknowns                         1,307,712
top-cancellation row bound        563,050
ambient surplus                   744,662
active weighted-degree slack       18,464
```

Conditioned `K=3` probes have not yet found a fresh-boundary rank failure,
but the probes do **not** yet include the 81,731 error-evaluation rows.  The
actual missing t7 theorem is joint surjectivity after imposing all top rows,
one next-filtration scalar at every error, and four compatible fresh-boundary
rows.

Most importantly, even that theorem would close only error-contact rung 7.
There is no existing target recurrence consuming it.  The linear t8 packet
has only 18,464 active X slack against a 112,609 top overage, and the affine
linear tower is source-illegal from t9 onward (the S lane is already 63,265
over cutoff).  Orders 8--43 and the final-three source equations remain open.
So this is useful structural progress, not near-submission evidence.

#### Current high-information requests

1. A uniform Toeplitz/Popov proof or counterexample for the **joint** t7 map
   at `(M,K)=(81731,3)`, including actual error rows.
2. A parametric shape-changing recurrence that crosses t8--43; isolated rung
   tuning is unlikely to scale.
3. On the benchmark-facing route, a cumulative original-coefficient cover or
   nonidentity eliminant that consumes the exact
   `ProjectiveHighDataElevenHighEClosedIncidenceLeaf` without changing the
   witness.

All new Lean receipts print only `propext`, `Classical.choice`, and
`Quot.sound`; no `native_decide`, `decide`, `sorry`, or added axiom is used.
The public research branch is
`saucegodbased/proximity-prize:codex/6900-live-research`.
