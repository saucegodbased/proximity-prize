# Actual split locator in `(u,v)`: finite-projection STOP

Date: 2026-09-15 UTC. Scope: the surviving lower-6900 near-total-identity
branch and its literal prime-field split error locator. This is a bounded
repository-only audit. It does not use or revisit the ECCC paper, change a
submission, or claim a target-sized counterexample.

## Decision

**STOP the proposed mechanical rescue.** Writing the quadratic-extension
seed as independent prime-field coordinates `(u,v)` is a real degree saving:
it avoids substituting `v=u^p`. If one can produce a nonzero bivariate seed
equation of total degree at most

```text
Dplane = 118980103,
```

the existing Schwartz--Zippel consumer closes the retained period-two
family. What fails is production of that equation from the actual split
locator. The extra near-total identity is a dependence, not a gauge fixing;
`q | N` makes `q | rem_N(q*f)` automatic; and requiring the coefficients of
`q` to lie in `Fp` imposes no extra condition at an `Fp^2` seed point.

There is also an important coordinate correction to the proposed fallback.
The advertised node-membership degree

```text
1005598286444
```

is the **one-variable extension-field** budget. A bivariate polynomial of
total degree `d` has as many as `p*d` zeros on `Fp^2`. Therefore the analogous
bivariate node-membership budget is only

```text
d <= 471,
```

not `1005598286444`. Equivalently, converting a bivariate expression back to
one extension-field variable through the linear formulas in `gamma` and
`gamma^p` can cost the same factor `p`.

An exact full-seed-plane split-locator model below retains all the qualitative
ingredients under discussion, including an all-node identity stronger than
the near-total one. It proves that those ingredients alone need not cut out
even one proper bivariate seed locus or one degree-one membership function at
the scaled sharp budget. Hence a GO now requires a new target-specific
classification/coverage theorem for compatible split locators; it cannot be
obtained by merely changing seed coordinates.

## 1. Exact target degree ledger

Let

```text
p    = 2130706433,
n    = 262144,
mass = 253511670984674103.
```

For a nonzero bivariate polynomial `H(u,v)` of total degree `D`,
Schwartz--Zippel gives at most `p*D` points of `Fp^2`. The exact last usable
degree is

```text
p * 118980103 = 253511670861102599
              < 253511670984674103,

mass - p*118980103 = 123571504.
```

Thus the bivariate counting **consumer** is green. No Frobenius-graph
substitution is needed once a nonzero `H` is actually available.

For exact support membership the current near-total branch has

```text
bigMass = 263611557201785350.
```

If `M_i(u,v)` has total degree at most `d`, each nonzero `M_i` vanishes at at
most `p*d` seeds. The same moving-node double count as in
`NearTotalIdentitySharpFrontierStop6900` therefore gives

```text
|Gamma| <= max(1, n*p*d).
```

At the endpoint,

```text
p*471 = 1003562729943 <= 1005598286444,
1005598286444 < p*472 = 1005693436376,

n*p*471 = 263077948278177792
          < 263611557201785350,
263611557201785350 <= n*p*472 = 263636500185350144.
```

So `471` is the last certified bivariate total degree. The larger number
`1005598286444=floor((bigMass-1)/n)` is usable only for a nonzero polynomial
in one extension-field variable, where the root bound is `d` rather than
`p*d`. Comparing a bivariate cofactor degree directly with that larger number
would mix two incompatible counting theorems.

The Lean file
`ActualSplitLocatorBivariateCoordinateStop6900.lean` formalizes both finite
grid consumers, including the bivariate node-incidence theorem and the exact
`471/472` transition.

## 2. Why the actual split locator is still not canonical

Write the fixed node polynomial as

```text
N(X) = product_i (X-x_i),
```

and the exact error locator as a monic `Fp` polynomial `q` of degree `81731`
dividing `N`. Put `s(q)=rem_N(q*f)`. The identity

```text
s(q) = q*f - N*quo_N(q*f)
```

shows immediately that

```text
q | N  ==>  q | s(q).
```

This is the compiled theorem `dvd_modByMonic_mul_of_dvd` in
`SplitLocatorComponentEliminantStop6900`. Hence `q|N` and `q|s(q)` are not two
independent cuts. The nontrivial conditions are the high-degree cutoff on
`s(q)` and the rational residual congruence.

The sharp terminal ledger for those conditions is

```text
columns                         = 81732,
high-tail + residual rows       <= 57669,
relaxed kernel dimension        >= 24063,
monic free coordinates          >= 24062.
```

The all-but-one-node identity does not add transverse locator rows.
`NearTotalIdentitySharpFrontierStop6900` proves that original syndrome rows
are convolutions of shifted quotient rows plus one common geometric row. Its
joint row span has at most

```text
49341 + 8328 + 1 = 57670
```

generators, still leaving deficit `81732-57670=24062`. Thus the rational
identity strengthens the known kernel instead of selecting one error
locator.

The fact that `q` has `Fp` coefficients does not repair this over the finite
seed grid. At each `(u,v) in Fp^2`, the specialized recurrence/residual matrix
has entries in `Fp`; its at-least-24063-dimensional kernel already consists
of `Fp` vectors. Frobenius-fixedness therefore removes zero dimensions
pointwise.

In the optimistic full-row-rank fixed-anchor picture, killing the remaining
monic freedom requires `24062` fixed nodal anchors. This leaves

```text
81731 - 24062 = 57669
```

seed-dependent rows in the old locator determinant. By
`OldLocatorGraphDegreeCountergate6900`, one such chart has bivariate
coefficient degree at most `57669`. That is cheap **for one chart**, but no
present theorem says that one fixed set of 24062 roots is contained in every
actual error support, or that at most a few such charts cover the family.
Lower rank asks for still more anchors and does not create a common anchor
set.

At the worst `e=18414`, paying the regular minor first leaves

```text
118980103 - 2*18414 = 118943275.
```

A product can then pay at most 2062 worst-degree old charts:

```text
57669*2062 = 118913478 <= 118943275
                           < 57669*2063 = 118971147.
```

Nothing in the current leaf bounds the anchor cover by 2062. Moreover a
degree-57669 bivariate membership coefficient becomes a one-variable bound
as large as

```text
p*57669 = 122875709284677,
```

over 122 times the allowed one-variable membership degree. The compiled
one-anchor-exchange countergate also shows that chart transition scalars can
carry genuine seed divisors, so projective gluing cannot simply declare these
costs common.

## 3. Exact full-plane split-locator countermodel

The deterministic verifier
`period_two_split_locator_full_plane_countermodel_6900.py` constructs the
following model.

Take

```text
Fp = F13,
K  = F13(alpha), alpha^2=2,
nodes = F13^*,
N=X^12-1,
error size=5,
agreement size=7,
selected degree=5.
```

Use the fixed centre polynomial, written low coefficient first,

```text
f = [7,5,6,11,5,6,1,10,7,0,4,1].
```

For every five-node error set `E`, define

```text
q_E = product_(x in E) (X-x),
a_E = N/q_E,
B_E = f mod a_E.
```

Then `q_E,a_E,B_E` lie in `Fp[X]`, `q_E` is monic and split, and

```text
deg B_E <= 6,
rem_N(q_E*f) = q_E*B_E.
```

The last equality is exact because `a_E | f-B_E` and
`deg(q_E*B_E)<=11<12`. Exhaustion of all

```text
choose(12,5)=792
```

split locators finds that the residues

```text
gamma_E = B_E(alpha)
```

cover **every one of the 169 elements of `F13^2`**. Choose the
lexicographically first `E` for each residue. Distinct seeds have distinct
locators, supports and scalar polynomials.

Now put

```text
P_gamma = (B_gamma-gamma)/(X-alpha),
U0(x)   = f(x)/(x-alpha),
U1(x)   = -1/(x-alpha).
```

Because `B_gamma(alpha)=gamma`, `P_gamma` is a polynomial of degree at most
five. On every chosen seven-node agreement support,

```text
P_gamma(x) = U0(x) + gamma*U1(x).
```

The fixed rational identity holds at **all twelve nodes**, stronger than the
target branch's all-but-one premise:

```text
(x-alpha)U0(x)=f(x),
(x-alpha)U1(x)=-1,
(X-alpha)P_gamma=B_gamma-gamma.
```

The fixed `U1` direction is bad on every selected support at degree five. If
a degree-at-most-five polynomial agreed with `-1/(X-alpha)` at seven nodes,
then `(X-alpha)P+1` would have degree at most six and seven roots, hence would
vanish identically; evaluation at `alpha` gives the contradiction `1=0`.

The fixed two-word plane is also projective-high on all twelve nodes. For a
nonzero pair `(lambda0,lambda1)`, multiplying a hypothetical degree-five
interpolant of `lambda0*U0+lambda1*U1` by `X-alpha` either forces the
degree-eleven `f` down to degree six (`lambda0 != 0`) or again gives a nonzero
constant at `alpha` (`lambda0=0`). The verifier checks all 168 nonzero pairs.
The selected scalar family has full affine coefficient rank seven.

Finally, because the seed projection is the complete `13 x 13` grid, no
nonzero bivariate polynomial of total degree at most

```text
floor((169-1)/13)=12
```

vanishes on it. The verifier independently checks rank 169 of the reduced
monomial evaluation matrix. This is the exact scaled analogue of the
`118980103` seed-eliminant budget.

The scaled node-membership budget is

```text
floor((169-1)/(12*13))=1.
```

The twelve node-incidence counts in the chosen supports are

```text
(26,70,87,116,107,110,110,117,107,110,107,116).
```

A nonzero affine polynomial on `F13^2` has exactly 13 grid zeros (a nonzero
constant has zero, and the zero polynomial has 169). None of these support
fibres can therefore be represented by a degree-at-most-one membership
polynomial. Thus the scaled membership fallback fails at precisely its sharp
counting threshold as well.

This model is not target-sized and does not realize the full `DataEleven`
provenance or target affine rank 40. It is a countermodel only to the claimed
formal implication from:

```text
prime-field split q
+ q|N and prescribed remainder
+ all-node rational identity
+ exact moving supports
+ fixed bad direction/projective-highness
=> proper affordable bivariate seed projection or canonical membership map.
```

That implication is false.

## 4. Exact GO condition for re-entry

Do not continue this route by constructing another relaxed kernel section or
by substituting the old bivariate cofactor bound into the univariate
membership budget. Re-enter only after proving, for the literal target word
and actual compatible split locators, one of:

1. a single nonzero `H(u,v)` vanishing on the retained seed projection with
   total degree at most `118980103` (including all chart/singular costs);
2. exact node-membership polynomials of bivariate total degree at most `471`
   with support injectivity; or
3. one-variable extension-field membership polynomials of degree at most
   `1005598286444`, together with an honest construction that does not hide a
   `p`-factor from `(u,v)` conversion.

Any chart approach must additionally prove a global cover/canonical split
section. Per-chart degree is not the blocker; uncontrolled split-component
and anchor-chart selection is.

## 5. Reproduction and trust

Run the exact model:

```text
python3 .experiments/period_two_split_locator_full_plane_countermodel_6900.py
```

Canonical output:

```text
PASS exact split-locator full-plane countermodel
field=F_13, extension=F_13(alpha), alpha^2=2
nodes=12, locators=792, selected_seeds=169
seed_projection=13x13=full, reduced_evaluation_rank=169
scalar_affine_rank=7
agreement_incidence_by_node=(26, 70, 87, 116, 107, 110, 110, 117, 107, 110, 107, 116)
seed_eliminant_total_degree_floor=12: impossible
bivariate_node_membership_degree_floor=1: impossible
```

Compile the formal degree/incidence interface with the repository's capped
library shim. Every printed theorem uses only `propext`, `Classical.choice`
and `Quot.sound`; there is no `sorry`, `decide`, or `native_decide`.

