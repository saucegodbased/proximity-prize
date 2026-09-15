# Near-total identity hard branch: syndrome-kernel STOP and algebraic-support GO

Date: 2026-09-15 UTC. Scope: lower 6900, the hard side of
`sharp_identity_node_2_dichotomy` only. This audit used only repository
definitions and artifacts. It changes no candidate or submission.

## Verdict

There are two exact conclusions.

1. **STOP the joint original/quotient ordinary full-minor route in this
   branch.** When at least `262143` of `262144` nodes satisfy the fixed affine
   row identity, the original syndrome rows are polynomial convolutions of
   the quotient syndrome rows, plus at most one common geometric direction.
   The proposed `81732`-column joint matrix consequently has row-span
   dimension at most

   ```text
   49341 + 8328 + 1 = 57670,
   ```

   leaving a deficit of at least `24062`. Its full-column minors are
   identically zero; this branch supplies a faithful rational kernel, not the
   missing transversality.

2. **A precise conditional GO survives:** make the actual agreement support
   algebraic in the scalar seed. If there are node-membership polynomials
   `M_i(gamma)` of seed degree at most

   ```text
   d = 1,005,598,286,444
   ```

   whose zero sets are the exact `180413`-node supports, then root-incidence
   counting and selected-bad support injectivity contradict the retained
   family size. The current leaf has no such algebraic parametrization: its
   `agreement : ExtensionField -> Finset Index` and `selected` are arbitrary
   supplied functions. This is now the earliest missing observable.

The formal receipt is
`NearTotalIdentitySharpFrontierStop6900.lean`. It compiles in under four
seconds with Lean's allocator capped at 3500 MiB. Every printed theorem uses
only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`,
`decide`, or `native_decide`.

## 1. Exact hard-branch provenance

The exact cutoff-two adapter is

```text
TwoSourceSharpIdentityNode2Split6900.sharp_identity_node_2_dichotomy.
```

Its hard branch is `262143 <= |Z|`, where `Z` is the zero set of both fixed
rows

```text
row0(i) = E0(i) U0(i) - a(i) - Q(i)c(i) centre(i),
row1(i) = E0(i) U1(i) - b(i) - Q(i)d(i) centre(i).
```

Since the full node set has cardinality `262144`, there is one fixed node
`e` such that every node other than `e` is in `Z`. The same `e` works for all
seeds; it is not reselected per candidate.

For a seed `gamma`, put

```text
q_gamma = Q * (c + gamma*d).
```

The sharp residual gives

```text
E0 * P_gamma = a + gamma*b + q_gamma * B_gamma.
```

Use exact polynomial division

```text
B_gamma = r_gamma + E0*C_gamma,
a + gamma*b + q_gamma*r_gamma = E0*t_gamma.
```

The second equality is the residue congruence furnished by the residual.
Therefore

```text
P_gamma = t_gamma + q_gamma*C_gamma.
```

At a node in `Z`, write

```text
centre = r_gamma + E0*beta_gamma.
```

The fixed identity row and root-freeness of `E0` on the benchmark nodes give

```text
U0 + gamma*U1 = t_gamma + q_gamma*beta_gamma.
```

Subtracting the selected-polynomial equality yields the exact gauge

```text
e_original = q_gamma * e_quotient
```

on `Z`. At the sole possible outside node it differs by one scalar spike.
The formal theorem `identity_division_error_gauge` checks the pointwise
algebra, including the required nonzero value of `E0`.

## 2. Why this kills the proposed joint minor

For a word `v`, define its weighted power syndrome by

```text
S_v(k) = sum_i weight(i) * v(i) * node(i)^k.
```

If `q_gamma(X)=sum_{t=0}^s q_t X^t`, with `s<=8328`, then the pointwise gauge
expands to

```text
S_original(k)
  = sum_{t=0}^s q_t S_quotient(k+t)
    + weight(e)*spike*node(e)^k.
```

Across a Hankel row, the final term is a scalar multiple of the *same*
geometric vector

```text
(1,node(e),node(e)^2,...).
```

Thus all `49341` original rows lie in the span of quotient rows numbered
`0,...,49340+s` and one geometric row. The first `32391` quotient rows are
already among those shifts because

```text
32391 <= 49341 + 8328.
```

The generator count is therefore `57670`, while the locator has `81732`
coefficients. The formal endpoint theorem

```text
endpoint_joint_hankel_span_ne_top
```

proves that the joint row span is not top. This is stronger than failing to
prove a minor nonzero: it proves every such full-column minor must vanish on
the entire near-total-identity rational family.

## 3. Audit of the exact leaf hypotheses

The hard branch still carries the full sharp/projective/high-E leaf. None of
its other present fields repairs the rank loss.

* **Huge `Good`:** supplies at least `263611557201785350` scalar seeds, but
  repeats the same row dependence at each seed. Cardinality cannot create a
  missing row direction.
* **Scalar injectivity:** distinguishes `B_gamma` as polynomials. It does not
  make the quotient syndrome determine a unique recurrence locator, and it
  does not couple support choices algebraically in `gamma`.
* **Degree bounds:** they are exactly what gives `s<=8328`, hence the explicit
  dependence above. They strengthen the STOP rather than transversality.
* **`180413` agreements:** ensure both original and quotient candidates use
  the same support. Pair and triple intersections are only
  `98682` and `16951`, respectively, below selected degree `131071`; ordinary
  two/three-seed root counting does not fire.
* **Projective-high:** makes the projective residual nonzero and bounds its
  residual degree. It controls constant combinations of `U0,U1`, not the
  polynomial multiplier `q_gamma`, so it does not invalidate the convolution.
* **Selected badness:** by the existing fixed-direction theorem, distinct
  seeds cannot have nested (in particular equal) agreement supports. This is
  support injectivity, but ordinary Sperner counting is astronomically too
  weak and it gives no seed-polynomial description of support membership.
* **Content, grade, conic, cross, and four source identities:** these own the
  construction of `E0,Q,a,b,c,d` and the residual. After those objects are
  fixed, their evaluated consequence is precisely the gauge above. No extra
  independent syndrome row remains in these identities.

The scaled `ZMod 7` control already realizes all fixed identity nodes,
projective-highness, selected badness, locator residuals, cross/source
identities and two scalar fibres. It does not realize target cardinality or
the exact `DataNine/Realizes` provenance, so it is not a countermodel to the
full endpoint; it does show why none of the downstream fields just listed is
individually a missing transversality premise.

## 4. The smallest surviving extra observable

Let `A_gamma` be the exact support and suppose, in addition, that there is a
polynomial `M_i` in the scalar seed for every fixed target node such that

```text
i in A_gamma  iff  M_i(gamma)=0,
deg M_i <= d.
```

Let `Z0={i | M_i=0}`. For `i` outside `Z0`, root counting gives at most `d`
seeds containing `i`. If `|Z0|<A`, double counting moving incidences gives

```text
|Good|*(A-|Z0|) <= (n-|Z0|)*d,
```

and hence `|Good|<=n*d`. If `|Z0|>=A`, exact support size forces every
`A_gamma=Z0`; selected-bad support injectivity then gives `|Good|<=1`.

At the endpoint,

```text
n*d
 = 262144 * 1,005,598,286,444
 = 263611557201575936
 < 263611557201785350
```

with margin `209414`. The theorem

```text
endpoint_bounded_seed_degree_locator_contradiction
```

formalizes this exact contradiction.

The seed type here is exactly `ExtensionField`, and `Good` is a finite set of
those scalar seeds—not pairs `(seed, selected polynomial)`. Arbitrary finite
interpolation does not supply the hypothesis: interpolating an arbitrary
membership indicator on `Good` can require degree `|Good|-1`, about
`2.636e17`, whereas the proved gate allows only about `1.006e12`.

The canonical affine received word `U0+gamma*U1` is algebraic in `gamma`.
The supplied `selected gamma` and `agreement gamma` are not. Likewise, a
row-reduced selector from the ordinary recurrence kernel is rational in
`gamma`, but the kernel has at least `24063` spurious dimensions; the selected
formal kernel vector need not be the actual split-node locator. The exact
upstream theorem still missing is therefore:

```text
construct the actual split agreement locator (or its node-membership zeros)
from the sharp leaf with seed degree <= 1,005,598,286,444.
```

A proof of that statement is a genuine end-to-end GO. A counterexample with
arbitrarily varying split locators while retaining the exact full leaf would
be a decisive STOP for this new lane.

## 5. Endpoint bookkeeping and process decision

The cutoff-two enumerative side has bound

```text
263611056734953625
```

against the core floor

```text
263611557201785348,
```

so it closes with margin `500466831723`. The remaining hard branch cannot be
charged as a small exception. The syndrome calculation above eliminates the
old transversality hope with zero residual uncertainty. Work should now be
restricted to the algebraic-support producer just stated, or to a genuinely
different endpoint consumer; more ordinary row stacking, pair/triple
intersection arithmetic, or generic quotient rank tests cannot improve this
branch.
