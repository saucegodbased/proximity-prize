# Hard identity / tiny multiplier countergate (6900)

## Verdict

**RED:** the hard all-node identity, projective-highness, the same-witness
scalar equation, agreement-residual factorization, and literal projected-code
badness do not by themselves force either

* `146 <= max(deg c, deg d) + deg Q`, or
* affine scalar rank at most `31`.

The exact reproducible countermodel is
`hard_identity_small_multiplier_countermodel_6900.py`.

## Exact identity exposed by the hard branch

Write `V0,V1` for the canonical full-domain interpolants of the received
rows, `C` for the interpolant of the common centre, and

```
F0 = E * V0 - a - Q*c*C
F1 = E * V1 - b - Q*d*C.
```

If `Z` is the fixed identity-node set, then its locator `LZ` divides both
`F0` and `F1`.  For every retained seed whose agreement support `A_gamma` is
contained in `Z`, write

```
V0 + gamma*V1 - P_gamma = H_gamma * R_gamma
S_gamma - C             = H_gamma * beta_gamma
LZ                       = H_gamma * K_gamma.
```

Subtracting the sharp scalar identity gives the exact cancelled equation

```
K_gamma * (T0 + gamma*T1)
  = E*R_gamma + Q*(c + gamma*d)*beta_gamma,
```

where `Fj = LZ*Tj`.  This is the smallest honest polynomial consequence of
the near-total identity.  It is a dependence/gauge equation, not a lower
bound on the multiplier degree.  The all-node locator can carry the high
received tail in `T1` even when `Q,c,d` are constant.

## Checked finite-field model

The script works over `F_257` with all 64th roots of unity as the 64 distinct
evaluation nodes.  It uses

```
V0 = X^62,  V1 = X^63,
E = X,      Q = c = b = 1,
a = d = 0, centre = X^63.
```

Thus the two fixed rows vanish on **all** nodes:

```
E*V0 - centre = 0,
E*V1 - 1      = X^64 - 1.
```

In particular the combined multiplier degree is `s=0`.  Nevertheless every
nonzero projective combination of `V0,V1` has degree at least 62.

The script finds and then exactly checks a 34-seed family with:

* selected degree at most 31;
* 33 agreements per seed;
* both received rows outside the degree-31 projected code on every support;
* scalar degree at most 32 and the exact identity
  `E*P_gamma = gamma + S_gamma`;
* every `S_gamma` agreeing with the same centre on its support;
* injective scalar points of affine direction rank exactly 33;
* nonzero `V0 + gamma*V1 - P_gamma`, divisible by the actual 33-node
  agreement locator, with quotient degree at most 30.

Run receipt:

```
GREEN exact countermodel: field=F_257 nodes=64 seeds=34 agreements=33
selected_degree<=31 scalar_degree<=32 affine_scalar_rank=33 s=0
```

## What the model does not satisfy

This is a falsification of the proposed **local structural implication**, not
a counterexample to the benchmark.  It does not reproduce:

* the exact benchmark surplus `180413 - 149486 = 30927`;
* the retained mass at least `263611557201785350`; or
* every upstream `DataEleven` / primitive-conic / aligned-cross source and
  minimality field.

Those are therefore the only legitimate places left for a positive theorem.
In particular, any next proof must visibly use the huge-family incidence and
the full 30,927-node scalar agreement surplus, or an additional upstream
cross/conic equation.  Repackaging the local identity/residual equations, or
using their high coefficients alone, cannot establish `s >= 146` or a
rank-31 carrier.

## Process decision

Stop the local `s >= 146` / rank-31 route.  A future hard-identity attack gets
one gate: state where the exact retained mass or `a-W=30927` enters before
doing any formalization.  If neither enters, this countermodel applies and
the route should be killed immediately.
