# m69 rational two-power / actual-leaf gate: RED with a target-specific seam

Date: 2026-09-14 UTC

## Verdict

The unqualified assertion that

```text
C_a + W*C_l1 + W^2*C_l2 (+ higher powers) = F^262144
```

for every reduced, domain-root-free rational `W=N0/E0` allowed by the
DataEleven leaf is **RED**.  The one-coordinate countergate in commit
`cb97180` is decisive: at `127730` numerator-zero nodes every positive-power
channel vanishes, while the low-fringe base channel has rank at most
`127729`.

This does not falsify the literal *first* defect, whose base fringe is
`258898`; it kills the promotion from that defect to all m69 defects.  The
first-defect cyclic rank problem remains GREEN only in the no-wrap subrange
`deg N0 <= 129449` and open in the exact band `129450..149776`.

The actual four source equations expose one narrower continuation: at
common-factor roots their four RHS values are zero, and at live numerator
roots their four RHS values lie in a pointwise rank-one locus.  No current
theorem turns that locus into the image of the shared m69 base source.

## Exact profile and first defect

```text
(m,slope,curvature,J,L) = (69,24,10,94,2369)
source-count margin       = 396574005663
first Pascal defect       = (A,n,H,j,s)=(63,44,24,14,10)
omitted (y,r,s,q)         = (39,14,10,15)
width                     = 4191058 = 15*262144 + 258898
a                         = 258898 = 262144-3246
l1                        = 127827
l2                        = 258900 = 262144-3244
```

For this one defect the proposed source is therefore

```text
C_258898 + W*C_127827 + W^2*C_258900.
```

The low-fringe hostile shape used below is the separately enumerated m69
shape `(y,r,s)=(0,0,0)`, with fringes

```text
127729, 258802, 127731, 258804, ...
```

It is not the first descending defect.  Conflating these two shapes would
incorrectly report the first defect itself as refuted.

## Smallest hostile control

`M69NumeratorZeroSetRankCountergate6900.lean` proves:

```lean
not_surjective_of_restriction_factors_through_low_rank
nodalLocator_127730_certificate
target_m69_numerator_zero_arithmetic
```

Choose `Z` consisting of `127730=127729+1` NTT nodes, let `N0` be its nodal
locator, and take a domain-root-free

```text
E0 = X^2151 - C(theta).
```

Then `deg N0=127730`, `IsCoprime E0 N0`, and all positive powers of
`W=N0/E0` vanish on `Z`.  Restriction of the combined source to `Z` factors
through `C_127729`, so its rank is at most `127729<127730`.  The exact current
degree inequalities still hold:

```text
deg N0 = 127730 <= 131071+2151+0
0+0+2151 <= deg E0
deg E0 < 18415.
```

The same arithmetic works at the older excess `2049`.  This is a defect-one
counterexample, and adding arbitrarily many positive powers of `W` cannot
repair it.

The construction satisfies the advertised rational and numerical premises;
it is not a constructed `DataElevenHighEClosedLeaf`.  The exact surviving
question is whether the *actual* leaf/source equations forbid its zero-set
behavior or constrain the required target there.

## GREEN first-defect core and its exact limit

`M69RationalTwoPowerGate6900.lean` proves the dual-kernel implication

```lean
short_square_nodal_relation_forces_zero
    (hcop : IsCoprime E N)
    (2049 <= E.natDegree)
    (E.natDegree <= 129449)
    (N.natDegree <= 129449)
    (H.natDegree < 3246)
    (H2.natDegree < 3244)
    (forall i,
      (N^2*H).eval (nodes i) = (E^2*H2).eval (nodes i)) :
    H = 0
```

This is the corrected physical normalization.  The multiplier is exactly
`W=N0/E0`, so clearing the square channel introduces no extra `X^2`.  The
earlier `X^2*E^2*H2` premise was an underived experimental normalization and
must not be used as a source adapter.  Removing it does not change the
no-wrap degree cutoff because the `N^2*H` side remains binding.

The proof upgrades the nodal congruence to a polynomial equality and uses
`IsCoprime E N` to force `E^2 | H`.  Its arithmetic boundary is exact for
this proof:

```text
2*129449 + 3245 = 262143 < 262144
2*129450 + 3245 = 262145.
```

Thus the square channel proves the first-defect rank kernel is zero whenever
`deg N0<=129449`.  The DataEleven adapter proves only
`deg N0<=149776`, leaving exactly `20327` possible degrees.  The middle
`W*C_127827` channel is the sharp next discriminator for the literal first
defect in that band.  Rational-function parameter dimension is not an
evaluation-rank proof in the cyclic quotient.

## Exact DataEleven ledger

`M69DataElevenRationalGate6900.lean` proves
`high_E_closed_leaf_m69_rational_parameters`.  For every exact high-E-closed
leaf it exports witnesses `B,E0,N0,Q` satisfying:

```text
E = B*E0,  N = B*N0
B != 0, E0 != 0, N0 != 0
IsCoprime E0 N0
E0(domain i) != 0 for every i
max(deg c,deg d)+deg Q+2049 <= deg E0 < 18415
deg N0 <= 149776
deg B+deg N0+max(deg L,deg M) <= 156003
deg B+2*max(deg c,deg d)+deg Q+max(deg L,deg M) <= 22883.
```

The `149776` numerator cap is the exact bound from `R.N_degree` and the leaf
excess/low-sum inequalities; the older loose `157813` figure is stale.

The existing content live set has exact size

```text
|Live| = 262144 - deg(content),
deg(content) <= 24932,
|Live| >= 237212.
```

Hence a `127730`-node hostile zero set fits entirely inside `Live`.  Merely
puncturing content nodes does not remove the numerator-zero obstruction.

## Content/common-factor seam

Cancellation of `B` is valid wherever `B(domain i)!=0`, including content
nodes which are not roots of `B`.  It is invalid at a `B`-root.  The theorem
`factored_cross_vacuous_at_one_B_root` is the smallest exact countercontrol:
the factored cross is true at the root while the normalized identity is
false.  Also,

```lean
nodal_root_card_le_natDegree
```

charges at most `deg B` such roots.

The actual source equations are more informative than an arbitrary-value
adapter.  The newly proved theorem

```lean
aligned_cross_source_constants_vanish_at_E_root
```

says that at every root of `E` (therefore at every `B`-root),

```text
C00(i)=C10(i)=C01(i)=C11(i)=0.
```

So an all-node extension must not charge four arbitrary values at those
nodes.  Zero source values already meet the actual RHS there.

The existing selected-quotient exporter deliberately uses the smaller set
`univ \ contentNodes`.  Its retained regular seeds have agreement sets
contained in that live set, so its current counting theorem does not require
arbitrary extension to all `262144` coordinates.  If one nevertheless fixes
all live values and asks the base code `C_(N-3246)` alone to repair `z`
omitted coordinates, its residual dimension is

```text
max(0,z-3246),
```

leaving exactly `min(z,3246)` arbitrary extension directions unresolved.
This is a rank/codimension statement, not permission to subtract `z` from a
seed-count margin.

## Actual numerator-root implication

`high_E_closed_leaf_m69_nodal_target_split` proves the exact split:

```text
B(i)=0  => all four C-values vanish;

B(i)!=0 and N0(i)=0
  => d(i)*U0(i)-c(i)*U1(i)=0
  => AlignedSourceRankOneAt R i.
```

Here `AlignedSourceRankOneAt` is the four-equation pointwise condition

```text
d*C00 = c*C10
d^sigma*C00 = c^sigma*C01
d^sigma*C10 = c^sigma*C11
d*C01 = c*C11.
```

This is all that follows from current leaf fields.  In particular:

* `CanonicalHighTailDirectionIndependent` controls nonzero **constant**
  projective directions; it does not bound zeros of the variable-coefficient
  wedge `d(i)U0(i)-c(i)U1(i)`.
* root-freeness is proved for `E0`, not `N0`;
* `IsCoprime E0 N0` does not bound domain zeros of `N0`;
* no field says the rank-one RHS restriction lies in the shared m69 base
  image.

## Single next discriminator

For the full m69 route, the maximum-throughput question is now target
specific.  Let

```text
LiveB = {i | B(domain i) != 0}
ZN    = {i in LiveB | N0(domain i)=0}.
```

Prove either the numerical exclusion

```text
|ZN| <= 127729,
```

or, more plausibly, the honest shared-source image statement

```text
restriction to ZN of every actual m69-required four-RHS tuple
  belongs to the range of the shared C_127729 base-source map.
```

A per-output interpolation assertion is not enough if the four outputs use
shared source coefficients.  The theorem must use the actual source map and
prove joint membership.  After that, a punctured rational-rank theorem is
still needed on `LiveB \ ZN`, followed by simultaneous confluence across all
`140153` deficient coefficients.

For the first defect alone, the narrower discriminator is whether the middle
channel eliminates every cyclic dual kernel in the numerator band
`129450..149776`.  Solving only that question cannot revive the full m69
profile after the low-fringe counterexample.

## Kill / continue rule

* **Kill** every unqualified arbitrary-rational or arbitrary-value m69
  surjectivity claim.  The `127730` locator is an exact one-dimensional
  cokernel witness.
* **Continue** the full m69 route only after a GREEN theorem on the actual
  `ZN` restriction: either `|ZN|<=127729` or joint base-image membership for
  the rank-one four-RHS target.  A random rank scan, parameter count, or
  first-defect-only proof is not that theorem.
* **Continue** the literal first-defect subproblem through the exact middle-
  channel band test; kill that subroute upon one leaf-compatible nonzero
  cyclic dual in `129450..149776`.

The route is therefore not yet grinding at the leaf-specific seam, because
the rank-one restriction is a new, exact discriminator.  The universal
arbitrary-rational branch is finished and should not be revisited.

## Inflation and hidden-hypothesis audit

The `396574005663` source-count margin cannot pay `24932` omitted evaluation
coordinates, a rank defect, or `140153` simultaneous coefficient obligations
without a theorem converting those objects into disjoint seed exceptions.
Treating that margin as fungible here is percentage/count inflation.

Likewise, the reciprocal interval statement covers all listed windows for a
monomial unit numerator, but it does not establish arbitrary-rational rank or
simultaneous allocation of shared source variables.  Reporting its coverage
percentage as an endpoint rank would be stale-baseline inflation.

## Build receipt

Both new Lean files compile with standard axioms only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `native_decide`, unsafe declaration, broad scan, or literature
rerun is used.
