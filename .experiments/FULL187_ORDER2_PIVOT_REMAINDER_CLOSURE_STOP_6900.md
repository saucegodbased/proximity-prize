# Full187 sharp-pivot remainder closure: simple induction is RED

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

The sharp order-two leading basis is not closed under its own higher-contact
remainders. Therefore the proposed proof

```text
cancel each leading monomial; every remainder has higher contact weight;
repeat with another sharp basis pivot until weight 60
```

is invalid. Higher weight gives termination only after every live successor
has a legal next pivot. Exact target-parameter enumeration finds 70,543
distinct live successor rows without such a pivot.

This does not refute the 103-shape packet route. Those escaping rows may be
handled by the scalar Hermite/capacity branch, and the terminal columns carry
specific packet coefficients rather than arbitrary monomial data. It does
rule out using `fullLayer_remainder` alone as the missing confluence theorem.

## Exact audit

The executable starts from every locally pivoted contact row occurring in all
surviving Hasse orders of the conservative 103 terminal shapes. There are
70,056 pivot origins and 8,164 distinct initial rows. For each row it expands
the literal polynomial

```text
Z^k (E+ZR-Z^2 S/2)^a0
    R^b (E-Z^2 S/2)^rho E^e S^(min(h,10)-e).
```

The selected leading monomial is checked exactly, and every other term is
checked to have strictly greater shifted contact weight. Taking transitive
closure through every still-live sharp successor gives:

```text
transitive sharp-pivot rows                 49,048
live successor edges                    3,444,163
terms truncated at contact weight >=60  7,242,188
distinct live nonpivot successors          70,543
```

The escaping edge occurrences split as:

```text
low-T sharp-pivot failure               1,866,904
E exceeds curvature-basis cap             525,133
R below active-overflow requirement         64,952
```

The first escape is already small and concrete:

```text
(T,E,R,S,passive)=(0,3,0,8,71), weight=9.
```

Thus strict contact-weight growth is real, but the sharp basis is only one
branch of the recurrence. A sound global induction must retain the origin and
external-X coefficient degree, then prove that each escape enters the strong
Hermite/capacity branch with the same multiplier bound. Collapsing to contact
exponents loses exactly the provenance needed for that argument.

## Consequence for the proof plan

The next theorem must be a **mixed** triangular lemma with two cases:

1. a sharp order-two pivot with explicitly bounded multiplier; or
2. a scalar Hermite lift preserving arbitrary error values.

It must carry `(terminal shape, origin, X-degree bound, passive seed)` through
the recursion. The four exact packets should be seeded atomically. Another
support-only closure or a blanket surjectivity claim is stopped.

## Reproduction

```text
prlimit --as=1073741824 --cpu=120 -- \
  python3 -B \
  .experiments/full187_order2_pivot_remainder_closure_6900.py
```

The final run used under 40 MiB RSS and no `decide` or `native_decide`.
