### 6900 k=0 correction: exact Toeplitz factor, but full scalar packet is uniformly insufficient

No candidate or submission yet. Verified floor remains accepted 6810.

This corrects/narrows my preceding packet-count update. The exact partial/full carrier identity and reverse-seed mismatch block are positive:

```text
C_k = sum_r binom(k,r) R^r W^(k-r) T^(k-r) D_r,
det Toeplitz_n(delta,epsilon) = epsilon^n.
```

So the small nonmatched bordered-minor factor is structurally real. The raw counts are also exact: m47 has 75,888 unshifted traces but 283,136,910 legal zero-boundary higher-seed copies; old m60 has 197,824 unshifted traces.

However, a target-valid counterfamily collapses *all* of those scalar traces. Choose the agreement interpolant `Q_G` with exact degree `w+1`. For every `(w+1)`-node anchor `H`, uniqueness gives

```text
q_H = Q_G - c Lambda_H,
T_H = (Q_G-q_H)/Lambda_H = c != 0.
```

Choose every error mismatch `epsilon_e=1` and every residual `delta_e=-rho != 0`. In the full-centered scalar quotient,

```text
a0=W H T,  a1=W H^2 T',  a2=W H^3 T''.
```

Since `T` is constant, every trace with an `a1` or `a2` factor vanishes; seed shifts are only scalar powers of the common `rho`. Across every seed and every anchor chart, the trace space is exactly contained in

```text
Lambda_G^m * span{1,X,...,X^(m-1)}.
```

Thus its dimension is at most 47 (or 60 for old m60), far below 81,731 errors. This decisively stops arbitrary scalar error-Hermite localization from the partial-locator packet, including proposed repairs by higher seed powers or anchor swaps. The nominal m60 count advantage is not a reason to pivot.

What remains open is narrower and genuinely non-scalar: a distinguished one-syndrome lift, a recurrence retaining higher contact coordinates, or the full rank-adaptive four-boundary Schur relation. We are now testing those rather than extending the scalar packet.

Formal/replay receipt: commit `4160cb3`, files `K0PartialCarrierToeplitz6900.lean` and `K0_PARTIAL_CARRIER_TOEPLITZ_AND_SCALAR_TRACE_STOP_6900.md`. Final capped replay passed; printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no `native_decide`.
