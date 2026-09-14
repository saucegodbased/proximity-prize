# Fixed-scalar `s = 0` countergate and actual-incidence audit

Date: 2026-09-14 UTC. Scope: experiment-only, same reciprocal witness. This
note does not claim a full DataEleven leaf or a 6900 submission.

## Kernel-checked result

`FixedScalarSmallSCountergate6900.lean` constructs the literal
`FixedScalarWeightedNoAdjacentHardCornerCondition` with

```text
E0 = X^2049 - theta,
B  = 1,
N0 = -1,
Q  = 1,
c  = 1,
d  = 0.
```

Hence the displayed scalar load is exactly

```text
s = max(deg c, deg d) + deg Q = 0.
```

The retained `Good` is not a singleton. It is the injective image of
`BaseField x BaseField`, and therefore has `2130706433^2` elements. Its
scalar polynomial at `(u,v)` is

```text
-(u + v X^2049),
```

which is Frobenius fixed, has degree at most 2049, and is injective. The
selected polynomial is the constant `-v`. The exact residual identity is

```text
(X^2049-theta)(-v) = (u+v theta) - (u+v X^2049).
```

All pole, properness, conjugate-coprimality, mixed-conjugate, numeric-window,
and cardinality fields of the scalar hard-corner record are proved. The same
reciprocal received rows satisfy the previously proved canonical high-tail
condition; the combined theorem is
`exists_projectiveHigh_fixedScalar_condition_with_s_zero`.

Both new modules compile under the ordinary 8 GiB-capped experiment runner.
Every printed axiom set is exactly
`[propext, Classical.choice, Quot.sound]`.

## Exact scope boundary

The constructed agreement sets are empty. Therefore this model does **not**
satisfy the target assumptions

```text
180413 <= card (agreement gamma)
selected(gamma)(x_i) = U0_i + gamma U1_i,
```

and it is not an inhabitant of `DataElevenHighEClosedLeaf`, its conic leaf,
or any full actual selected-family leaf. It is a counterexample only to an
attempt to derive `s >= 202` from the scalar hard-corner record (or from that
record plus bare canonical-high/aligned-cross data) without using actual
agreement incidence.

## What actual agreement incidence adds

For two actual candidates, each agreement set has at least 180413 elements
inside the 262144-node domain, so their intersection has at least

```text
2 * 180413 - 262144 = 98682
```

nodes. On this intersection their scalar polynomials evaluate to the same
fixed centre. Thus a distinct scalar difference has at least 98682 roots.
For the plane above every difference has degree at most 2049, so the ordinary
polynomial root bound forces that difference to be zero; scalar injectivity
then forces the two seeds equal. Consequently the actual agreement hypotheses
collapse this particular `p^2` plane to at most one member. They decisively
exclude the countermodel once restored.

More generally, actual agreement makes the coefficient block in degrees
`98682,...,W` injective: two scalars with the same block differ in degree at
most 98681 and hence must be equal. This is a useful high-tail separation
fact, but it does not by itself imply `s >= 202`. The parameter `s` belongs to
the multiplier data `(c,d,Q)`, while the pairwise root argument constrains the
scalar-polynomial differences. There remain many possible high blocks when
`W >= 133120`. A valid positive lower bound on `s` therefore still needs an
additional same-witness theorem coupling those high scalar coefficients to
the residual/cross/conic incidence. No such coupling was found in the audited
APIs.

## Wrap clarification

For this reciprocal cross `L=1` and `M=-1`, so the actual wrap parameter is
`ell=max(deg L,deg M)=0`; its nonpolynomial canonical degree lower bound is
therefore compared with 237212, not 237212+2049. The already proved stronger
degree `260095` exceeds either numerical comparison, but `2049` is the
denominator excess, not `ell`.

## Routing verdict

- `s >= 202` from scalar hard-corner data alone: formally false.
- The displayed reciprocal `s=0` plane under full actual agreements: formally
  not claimed and mathematically excluded by the 98682-root argument.
- `s >= 202` for every full DataEleven leaf: still open; the missing input is
  exactly a multiplier-to-high-scalar-tail incidence coupling, not another
  bare aligned-cross or scalar-record inequality.
