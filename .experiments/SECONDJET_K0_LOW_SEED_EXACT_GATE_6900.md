# Zero-reserve low-seed P5 gate for lower 6900

Date: 2026-09-14 UTC. This is an exact arithmetic and architecture receipt,
not a proof, candidate, or submission.

## Exact new arithmetic

The relaxed second-jet source has a substantially smaller target-positive
zero-reserve profile than the first `L=5465` observation:

```text
(m,B,s,U,L,k,n0) = (148,64,30,200,906,0,1)
columns            = 1,738,293,650,805,057
one-node rank      =         6,631,019,551
262144 * rank      = 1,738,281,989,177,344
source margin      =        11,661,627,713
closed-cap slack   =                     3.
```

After the last small-cap transition at `L=210`, the margin is affine in `L`
with slope `36,307,428,310`. An exhaustive exact check of every admissible
integer cap from `200` through `905` is negative, and the preceding cap is:

```text
L=905 margin = -24,645,800,597
L=906 margin = +11,661,627,713.
```

Thus `906` is the first positive integer total/seed cap for this fixed
`(m,B,s,U,k,n0)` shape, rather than a sampled point.

## Sound candidate-major quantifiers

For each exact agreement cardinality `g`, let `V_g` be the common all-node
contact kernel with cutoff `D=148*g`, and let `Gamma_g` be the retained
selected candidates having exactly `g` agreements. For `gamma in Gamma_g`,
define over `K(X)`

```text
beta_gamma : V_g -> K(X)^4
beta_gamma(Q) = grad_(Y,R,S,Z) Q(f_gamma,f'_gamma,f''_gamma/2,gamma).
```

The zero reserve is deliberate: every `Q in V_g` itself vanishes on every
candidate graph, while its first boundary derivatives are not forced to
vanish. The required producer theorem is

```text
forall gamma in Gamma_g, rank(beta_gamma)=4.
```

Only after that pointwise theorem is proved may finite simultaneous selection
choose four common rows in `V_g tensor K(X)` whose Jacobian is nonsingular at
every candidate. Those are four independent, fixed P5 equations in the five
variables `(X,S,Y,R,Z)` (four boundary variables over `K(X)`), not one kernel
row and not a seed-specialized moving P4 equation. One nonzero kernel row
defines only a hypersurface and gives no finite candidate count.

## Consumer and exact-agreement ledger

The four boundary equations have active degree at most `M=200` and seed
degree at most `L=906`. Conditional on the missing rank theorem and the
already-identified component producer, the existing coarse cofactor budget is

```text
40*M^3*L                              =       289,920,000,000 per stratum
81,732 * 40*M^3*L                    =    23,695,741,440,000,000
target MCA allowance                 =   254,684,620,614,660,120
conditional slack                    =   230,988,879,174,660,120.
```

Hence it is arithmetically safe to retune the cutoff separately for all exact
agreement strata; the fixed-cutoff high-agreement determinant obstruction is
not a budget obstruction. The sharper unavailable multihomogeneous count is
`4*M^3*L = 28,992,000,000` per stratum. The factor-40 path still needs the
packed-compatible component/allocation producer recorded in the Full187
consumer audits.

## Prior-work comparison and honest blocker

The qualitative conormal idea is not new. It is the same route isolated in
`GLOBAL_O2_REVERSE_INCLUSION_AND_HIGH_AGREEMENT_SPLIT_AUDIT_6900.md` and
`GLOBAL_O2_FIXED_MINOR_COVER_AND_DUAL3_AUDIT_6900.md`. Small exact controls
for the present relaxed source reproduce the expected dichotomy: a legal
degree-`w` agreement direction gives rank three because
`(h,h',h'',1)` is a pencil tangent, whereas every tested degree-`>w`
direction gives rank four. This evidence is recorded by
`secondjet_candidate_major_function_field_rank_gate_6900.py`; it is not a
uniform theorem.

The load-bearing statement remains exactly

```text
rank(beta_gamma)<4
  -> u1 on the agreement set has an interpolant of degree <= w,
```

equivalently the first extra Newton divided difference must vanish. Merely
centering by the automatic degree-`<g` agreement interpolant costs
`g-w-1` per active factor and repeats the stopped terminal-CRT argument.
Neither the `11.66e9` nullity margin nor the smaller seed cap proves this
reverse inclusion. The smaller profile is a useful arithmetic simplification,
but until the fixed symbolic bordered minor / three-dimensional dual
continuation calculation proves rank-defect recovery, this is not closer to a
submission in theorem completion.

## Reproduction

```sh
env PYTHONPATH=.experiments \
  python3 .experiments/secondjet_k0_low_seed_exact_6900.py
```

The checker performs only exact integer arithmetic and uses negligible
memory; it has no `decide` or `native_decide` computation.
