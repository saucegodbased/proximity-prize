# Full187 fixed-degree cross-packet STOP

Date: 2026-09-13 UTC. Scope: lower 6900 research only; no production edits.

## What this tests

The earlier single-packet STOP did not address Pascal cancellation between
several high-`V` packets. This note tests the maximal cancellation available
inside one common error-locator stratum and one homogeneous normal degree.

Let `A=(Omega_N')^-1 H'`, so `L*A = 1 mod H` at every error. A general
homogeneous inverse packet of normal degree `n` is the homogenization of an
arbitrary polynomial `P(T)` of degree at most `n`, evaluated at the two
normal endpoints `V` and `L*A`. Thus this setup already permits arbitrary
cross-`b`/Bernstein cancellation within that degree; it is not restricted to
one monomial `V^s(V-LA)^r`.

After all cancellation, write:

* `j` for the order of `P` at the agreement endpoint `T=0`;
* `r` for the order at the error endpoint `T=1`;
* `a` for the common `H`-adic order.

Then `T^j(T-1)^r | P`, so `j+r <= n`. Contact 60 forces `a+r >= 60`.
The relaxed pure-normal seed cap is `n<=66`.

The first surviving `V^j` coefficient in the homogenized packet contains

```text
H^a A^(n-j).
```

After removing the mandatory agreement-locator head, its literal Full187
pure-seed residual strip has width only `16951*j`. Source legality would
therefore require

```text
81731*a + 81730*(n-j) < 16951*j.
```

The three inequalities above make this impossible. Even the most favorable
relaxed corner leaves a gap of 4,802,094. The polynomial multiplicity fact,
target arithmetic, and `natDegree` conclusion are Lean-checked in
`Full187FixedDegreeCrossPacketEndpointStop6900.lean`, with standard axioms
only.

## Exact scope

**STOP:** every arbitrary cross-`b` combination that remains inside one
common `H^a` stratum and one homogeneous normal degree and uses the natural
derivative inverse `A`.

**Still open:** combinations across different `H`-adic strata or different
homogeneous degrees. Such a construction would have to cancel the actual
polynomial endpoints after reduction modulo successive powers of `H`; it is
a genuine Hermite/Popov system, not a Bernstein packet. This is now the only
honest interpretation of the checkerboard route from the six-family audit.

This obstruction applies before distinguishing the three desired Full187
linear boundary rows `F0/F1/F2`, so none of them can be obtained by the
fixed-degree packet class. It does not establish failure of the full literal
source.
