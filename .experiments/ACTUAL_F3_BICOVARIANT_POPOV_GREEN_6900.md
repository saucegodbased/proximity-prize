# Actual F3 bicovariant Popov gate: exact GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission roots, claim, score, and radius are unchanged.

## Verdict

The exact partial-locator packet `F3` in the already-successful F101
complete-source chamber has a new explicit **factor-module** lift. This is
not an arbitrary terminal-`C` test and it is not a separated packet family.
It simultaneously uses:

* all three order-1/2/3 agreement covariants;
* all three order-1/2/3 error covariants;
* different agreement/error locator strata and normal degrees; and
* the passive `Z` direction before the strict source projection.

With polynomial shifts `0..7` in both `X` and passive `Z`, exact rank over
`F_101` produces a literal source element with:

```text
source support                                      1768
nonzero complete-contact rows                          0
boundary polynomial degrees                    (26,-1,-1,31)
boundary                                           exact F3
four-packet boundary determinant degree               104
representative sha256
  9f507637f28f5256934ed6f3f802a4bf0ffeb2f3565aa770f27b8eb4c3581253
```

Every surviving source monomial is rechecked against the literal weighted
F101 source predicate, and the complete contact and boundary maps are then
re-evaluated from those surviving coefficients. The result is therefore a
genuine positive mechanism, not just a rank prediction.

The sharp adjacent ablations are RED:

| max X shift | max passive-Z shift | correction rank | augmented rank | result |
|---:|---:|---:|---:|:---|
| 8 | 0 | 540 | 541 | RED |
| 8 | 6 | 2903 | 2904 | RED |
| 6 | 7 | 2940 | 2941 | RED |
| 7 | 7 | 3123 | 3123 | **GREEN** |

Thus passive propagation is load-bearing, and the positive result is not the
already-refuted `K[X]`-only/separated extrapolation.

## The factor module

Write `L=Lambda_G`, split the agreement locator as `L=H*R`, and let
`E=Xi_error`. In the F101 instance the actual agreement direction is `Q`,
the error direction is zero, and the retained anchor interpolant is `q_H`.
Put

```text
V_H = Y-Z*q_H.
```

The agreement covariants are

```text
A0 = Y-ZQ,
A1 = L*(R-ZQ') - L'*A0,
A2 = L^2*(S-ZQ'') - 2LL'*(R-ZQ')
       + (2(L')^2-LL'')*A0.
```

They have literal agreement contact orders `1,2,3`. The error covariants use
the error locator and the actual error graph `(P_E,Q_E)=(1,0)`:

```text
E0 = Y-1,
E1 = E*R - E'*E0,
E2 = E^2*S - 2EE'*R + (2(E')^2-EE'')*E0,
```

and have error contact orders `1,2,3`.

For exponent triples `alpha=(ay,ar,as)` and `epsilon=(ey,er,es)`, set

```text
a = ay+2ar+3as,
e = ey+2er+3es,

G_(alpha,epsilon) =
  H^max(m-1-a,0) R^max(m-a,0) E^max(m-e,0)
    * V_H * A0^ay A1^ar A2^as * E0^ey E1^er E2^es.
```

The three node classes make the contact proof transparent:

```text
H anchors:       (m-1-a) locator + V_H + a agreement order >= m,
R agreements:   (m-a) locator + a agreement order             >= m,
errors:         (m-e) locator + e error order                  >= m.
```

The executable nevertheless checks all 61 F101 generators using the literal
`translated_column` contact implementation. The normalized base is

```text
G_((0,0,0),(4,0,0)) = B*V_H*(Y-1)^4.
```

Since `(Y-1)^4` has constant term one, its linear boundary is exactly `F3`.
Every other error-only generator is made boundary-zero by subtracting its
exact polynomial boundary multiple of the base; every generator containing
an agreement covariant is already boundary-zero. The final task is purely a
shifted coefficient-module problem: cancel all source-illegal coefficients
with `X^i Z^j` multiples of these complete-contact, boundary-zero elements.

The GREEN solve uses 1,802 shifted generators from 58 distinct covariant
factor pairs. Both shift maxima seven are attained. The resulting source has
only derivative shapes `(r,s)=(0,0),(1,0)`.

## Safe-103 deletion audit

The positive witness does **not** borrow any target-forbidden terminal shape.
Its only derivative shapes are pure and first-slope, both in the conservative
103 set. Direct inspection of the final representative finds zero terms on
the terminal deletion face with an unsafe `(r,s)`. Thus this finite GREEN is
unchanged by applying the target safe-103 shape deletion rule.

This does not prove that a target lift exists: it proves that the mechanism's
finite success is not an artifact of columns that the proposed target source
would delete.

## Exact target-scaling interface

The same definitions make sense at the target with

```text
(m,J,L,slope,curvature)=(60,82,2703,21,10),
Q_G = degree-<g agreement interpolant,
Q_E = X^81730 on the error nodes.
```

The error covariants must use the literal `Q_E`; replacing them by `Y-1`
would incorrectly discard the passive direction. Restricting to the same
three derivative shapes `(0,0),(1,0),(0,1)` gives 178 exponent triples and
14,327 agreement/error factor pairs. A literal `0..7` by `0..7` rectangle
would have at most 916,928 shifted columns before structural reduction.

Raw target generators are **not** individually source-legal. The F101 result
works because their illegal high-degree tails cancel, leaving a legal sum.
Consequently the next target certificate is exactly a shifted bivariate
Popov/module membership theorem over `(X,Z)`:

```text
F3 boundary coset intersects every literal Full187 coefficient window.
```

It must certify the combined representative; checking generators one at a
time would reject the mechanism for the wrong reason. A dense target matrix
is also the wrong implementation. The factorized contact proof removes all
contact rows in advance; only the polynomial tail module remains.

An informal saturated-contact lemma in the GitHub discussion
[comment 18427358](https://github.com/proximity-prize/proximity-prize/discussions/530#discussioncomment-18427358)
suggests the right completeness proof: normalized order-1/2/3 covariants with
distinct top monomials form a saturated local basis. Here the triangular top
monomials are `Y`, `L*R`, `L^2*S` on the agreement side and their error-side
analogues. This is encouraging, but the comment explicitly requires a
complete-sector identification and a degree-compatible filtration. Neither
requirement is claimed here.

## Exact scope

GREEN:

* one faithful F101 chamber;
* the actual `F3=B*(Y-Z*q_H)` boundary;
* complete literal contact zero;
* literal source legality after simultaneous cancellation;
* no dependence on unsafe terminal-103 shapes.

OPEN:

* the target shifted-Popov membership;
* a uniform saturated-basis theorem for the exact weighted source;
* the analogous simultaneous representatives for `F0,F1,F2`; and
* integration into `ProtocolClaim 6900`.

## Reproduction

```bash
python3 -B \
  .experiments/f101_actual_f3_bicovariant_popov_gate_6900.py
```

The default exact run uses under 0.8 GiB peak RSS. The executable also accepts
`--max-shift` and `--max-seed-shift` to replay the RED ablations above.
