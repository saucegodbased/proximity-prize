# Projective residual canonical chart versus the shallow cycle

Date: 2026-09-15. Scope: the exact post-`W=133226` sharp same-witness leaf.
This is a research gate, not a `ProtocolClaim 6900`, production edit,
candidate, comparator run, submission, or score claim.

## Decision

The projective residual tail contains a genuine new same-witness affine
coordinate, but it does **not** attach to the archived shallow-Chow count.
The two smallest attachment tests are now Lean-checked and both are decisive:

1. **GREEN producer.** There is one fixed `k>=133120` and fixed `A,B`, with
   `B!=0`, such that every retained seed has a nonzero residual `R_gamma` of
   degree at most `81730` satisfying

   ```text
   coeff_k(H_gamma R_gamma)=A+gamma B.
   ```

   The right side is injective in `gamma`.

2. **RED attachment.** Monicity makes `R_gamma` unique and removes Cramer
   denominators, but top-down division can make its coefficients degree
   `81731` in the moving locator coordinate. This is `80002` beyond, and
   `47.27` times, the shallow source cap `1729`. The full product can still be
   affine in a parameter `gamma`; therefore affine product dependence does
   not imply a cheap regular quotient chart.

Adding `gamma` as an explicit degree-one source coordinate also does not cure
either archived exceptional branch. A Lean countergate has `T=X` and
`B=X^2` over `ZMod 2`: `T'!=0` while the nonconstant graph coordinate has
`B'=0`. Thus a separable affine label does not imply separability of the
graph coordinate. On a coefficient-null seed component, the shallow rows
remain coefficientwise zero after adjoining a label, so the vertical
`Y x P1_B` component remains vertical.

No new whole-family cap follows. The old conditional shallow cap remains

```text
6,260,443,024,818,645
  < 263,611,557,201,785,350 = |Good| lower bound,
```

with a factor `42.10` of numerical room, but its p-closed, vertical,
normalized-height, and one-spend cycle premises remain unproved.

## 1. Exact theorem and exact leaf fields

The generic, axiom-clean adapter is

```text
ProjectiveHighSameWitnessAffineResidualTailCoordinate6900
  .exists_same_witness_affine_residual_tail_coordinate
```

with inputs

```text
hhigh : CanonicalHighTailDirectionIndependent nodes U
hresidual : forall gamma in Good, exists R_gamma != 0,
  deg R_gamma <=81730 and
  forall k>131071,
    coeff_k(H_gamma R_gamma)
      =coeff_k(V0)+gamma*coeff_k(V1).
```

On `TwoSourceSharpProjectiveHighEIncidenceLeaf`, those inputs are supplied
without changing witnesses by:

```text
leaf.projectiveHigh
leaf.sharpPackage.toSharpProjectiveResidualPackage.Good
leaf.sharpPackage.toSharpProjectiveResidualPackage.good_subset
projectiveHigh_incidence_leaf_residual_high_coefficients
  leaf.toIncidenceLeaf
```

Take `k=natDegree(V1)`. Projective highness in direction `(0,1)` gives
`k>=133120`, and the leading coefficient `B=coeff_k(V1)` is nonzero. Hence
`gamma |-> coeff_k(V0)+gamma B` is injective. This is stronger and cleaner
than merely reusing the already-known scalar injection: it labels an actual
coefficient of the same locator-residual product.

The direct exact-leaf instantiation currently trips an unrelated cached-module
collision in the experimental runner:

```text
Valuation.Integers.integralClosure
  already present from ProximityPrize.SubmissionLower.V6
```

The generic adapter itself compiles in about four seconds and has only
`propext`, `Classical.choice`, and `Quot.sound`. No production module was
changed to work around the cache problem.

## 2. The canonical monic-division gate

Write `m=deg H_gamma>=180413` and `r=81730`. Since `H_gamma` is monic, the
top `r+1` product coefficients recursively determine all coefficients of
`R_gamma`; the triangular determinant is literally one. Thus Cramer
denominators are not the issue.

The exact recurrence obstruction is formalized in
`ProjectiveResidualMonicDivisionDegreeGate6900.lean`. Define

```text
inverseTail(h,z,0)=z,
inverseTail(h,z,r+1)=X*inverseTail(h,z,r)+z*(-h)^(r+1).
```

Lean proves

```text
(X+h)*inverseTail(h,z,r)
  =z*X^(r+1)-z*(-h)^(r+1),

coeff_0(inverseTail(h,z,r))=z*(-h)^r.
```

After multiplying by any fixed prefix `G`, put
`gamma=(-h)^(r+1)`. The complete product is

```text
((X+h)G)*inverseTail(h,1,r)
  =G*X^(r+1)-gamma*G,
```

which is affine in `gamma`, while the quotient still contains the degree-`r`
coefficient `(-h)^r`. This falsifies the proposed implication

```text
affine product tail + monic locator
  => quotient coefficients regular of shallow degree.
```

It is not an artifact of label collisions. Lean checks

```text
gcd(81731,p-1)=1, p=2130706433.
```

So `h |-> h^81731` permutes the nonzero base-field labels. The dimensions
also match the exact one-moving-root frontier:

```text
180412 common locator roots +81732 possible extra roots=262144 nodes.
```

This is the algebraic core of the familiar fixed-core/one-varying-node
allowance family, now aimed specifically at the canonical quotient chart.
It is not a large counterexample to the benchmark: one such core has at most
`81732` labels and is already within existing pencil/allowance bounds. It is
enough to refute a **local low-degree chart theorem**, which is the premise
needed to insert `R_gamma` into the shallow cycle cheaply.

## 3. Exact shallow interface and why no term changes

The archived shallow route's moving-horizontal theorem needs an integral
component with a graph coordinate `b` satisfying

```text
db != 0 over k(X).
```

Only then do the paid seed derivatives imply the first `173` `B` derivatives,
`M^173 | Q`, and finally `deg_B M=1`. The new residual-tail coordinate proves
that an auxiliary label `T=A+gamma B0` is separable. There is no identity in
the exact leaf equating `dT` to a nonzero multiple of `db`. The Frobenius
countergate `T=X`, `b=X^2` shows the missing implication is false even on a
smooth affine line.

The vertical stop is even more direct. `R_gamma` exists only after choosing
an actual agreement locator at an actual retained point. It is not a
coefficient of the paid shallow source row. If every coefficient of every
paid row vanishes on a seed child `Y`, adjoining `(gamma,T)` does not make any
of those coefficients nonzero; `Y x P1_B` remains a source-base component.

Finally, treating all `81731` quotient coefficients as auxiliary regular
coordinates is not cheap. The monic product equations are bilinear and the
eliminated chart has coordinate degree as high as `81731`, versus the
shallow height `1729`. Therefore neither the source divisor class nor the
cycle-height term `h=10` in the conditional count is preserved. There is no
honest modified cap to report.

## 4. Process consequence

Freeze both of these claims:

```text
one affine residual-tail coefficient repairs p-closed motion;
monic division makes the residual a low-degree shallow coordinate.
```

The affine producer remains a useful exact invariant for a future consumer,
but that consumer must control the locator-support choice globally (or give a
cycle degree that pays the `81731` recurrence). It cannot be obtained by
adding the label or the quotient coordinates to the existing shallow cycle.

The next viable structural route must use a relation coupling the actual
shallow graph coordinate itself to the projective residual, or count the
fixed-domain locator choices without first parameterizing their quotient.

