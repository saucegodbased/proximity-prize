# k0 critical adjacent-cell commutator and exact Newton tail

Date: 2026-09-14 UTC. Scope: lower-6900, full m47 exact-G source. This is a
compiled local identity and a target window calculation, not the missing
global confluence theorem.

## Result

Let

```text
V = u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T,
W = u0 + u1 Z,
B = X_a S (V-W)^m.
```

Here `B` is exactly the critical `Y^m S` column plus its complete causal
lower staircase. The adjacent-Y and adjacent-Z packets are literally

```text
B_Y = B V,
B_Z = B Z.
```

Therefore

```text
B_Y - u0 B - u1 B_Z = B (V-W)
                       = X_a S (V-W)^(m+1).       (AC)
```

The right side is divisible by `epsilon^(m+1)`. This is a genuine
one-contact-order gain and explains why the finite filtration can choose
its second critical cell on either adjacent axis:

```text
Y^m S, Y^m S Z
```

or

```text
Y^m S, Y^(m+1) S.
```

The Lean proof is a literal identity in the full flattened
`(epsilon,S,T,R,Z)` contact algebra. No dimension argument or selected
projection is used.

## Exact anchor split

At the target minimum stratum, the relevant strict X widths are

```text
W(S Y^47)   = 2,188,005,
W(S Y^48)   = 2,056,934,
W(S Y^46 R) = 2,188,006.
```

On an agreement anchor `H` of size `w+1`, write the exact direction
interpolant as

```text
Q = q + E T,
deg q <= w,
E = locator(H),       deg E = w+1,
deg T < g-(w+1) = 49,341.
```

The three width equalities behind the only plausible globalization are

```text
W(SY47) - w       = W(SY48),
W(SY46R) - (w+1)  = W(SY48),
W(SY48) - (W(SY47)-(g-1)) = g-w-1 = 49,341.
```

Thus:

- the low anchor interpolant `q` fits the entire adjacent-Y window exactly;
- using the full `Q` directly loses exactly 49,341 top multipliers;
- the mixed connector `S Y^46 R` refunds the one extra degree of the anchor
  locator `E`; and
- after that one-degree refund the unresolved loss is 49,340, exactly the
  maximum possible degree of `T`.

This is much sharper than saying “there is a large Q tail.” The obstruction
is exactly the retained-badness Newton quotient, with no slack or rounding.

The connector is target-legal:

```text
2*S+R = 3 <= B=16,
S+Y+R = 48 <= U=64,
z<=1,
X width = 2,188,006.
```

It is not legal in the earlier m5/B2 control (`2*S+R=3>B`), so that control
cannot validate or falsify this repair. A B>=3 faithful discriminator is
required. The generic raw-map/HRS interface can expose the connector, but
the previously frozen `k0CriticalFilteredCarrier` deliberately excluded it;
the connector needs a separate extended-carrier predicate.

## Honest global status

Equation (AC) uses the node scalars `u0_i,u1_i`. Replacing those scalars by
global polynomials introduces their full Hasse translates
`P(x_i+epsilon),Q(x_i+epsilon)`. The extra epsilon tails are precisely the
PC/connection terms that still must be shown to cancel through the complete
raw source. The local identity does not silently prove that step.

The live theorem target is now narrow:

1. lift (AC) on the boundary-compatible dual cone;
2. use `q` through the exact `w` refund;
3. use `S Y^46 R` to absorb the `deg E=w+1` locator;
4. identify and kill the remaining degree-`<49341` T-tail by the exact-G
   quotient pairing or an error test.

Without step 4, the result is not DUAL0 and not a 6900 proof.

## Artifact

```text
.experiments/K0CriticalAdjacentCellCommutator6900.lean
```

Compiled theorems include:

```text
critical_adjacent_YZ_commutator
critical_adjacent_YZ_commutator_eq_next_nilpotent
eps_pow_succ_dvd_critical_adjacent_YZ_commutator
target_anchor_quotient_window_split
m47_reduced_profile_critical_SYR_connector_legal
```

The file compiles in about three seconds under 8 GiB. Printed axioms are
only `propext`, `Classical.choice`, and `Quot.sound`.
