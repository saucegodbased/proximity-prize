### 6900 update: retract order-15 k4 claim; low-m k0 retuned wrapper is green

Status first: our verified floor remains **6810**. There is no 6900 candidate or
submission. This update corrects a false intermediate claim and reports a new
source/consumer wrapper; the central rank-defect theorem is still open.

#### Correction to the k4 idea

The previous proposal differentiated a target-positive second-jet source four
times in the curvature variable and claimed that the canonical agreement
tangent was root-count-forced through order 14. That ledger double-counted the
four-derivative reserve. After `∂S^4`, the specialized degree is already
`<(m-4)A` and the contact order is `(m-4)A`, leaving only the strict one-degree
slack. The first tangent coefficient is therefore unforced at order 1, not 15.

An exact faithful GF(101) control reinforces the stop: the contact kernel had
dimension 339 while its entire `∂S^4` image was zero. Total nullity does not
force any fourth-curvature incidence rank. Commit `c31d174` patches the note
and Lean arithmetic and adds the exact discriminator. The Lean receipt uses
only the standard axioms; no `native_decide`/unsafe evaluation is involved.

#### What survives: undifferentiated k0 source

For `k=0`, faithful controls reproduce the already suspected Global-O2
dichotomy: three legal degree-`<=w` agreement-direction pencils have conormal
rank 3, while all 12 tested degree-`>w` directions have rank 4. This is evidence
only; it does not prove the reverse implication.

A low-multiplicity target profile is exactly source-positive:

```text
(m,B,s,U,L,k,n0) = (47,16,8,64,3757,0,1)
source columns       65,061,789,117,960
N * local rank       65,061,786,746,880
margin                        2,371,080
```

It also has raw terminal width `90,867 > 81,731` errors. A full four-normal
minor has residual cap

```text
148025 - 185*r
```

at `r` agreements above its cutoff, so one retuned source covers 801 agreement
levels. 103 cutoff windows cover every cardinality from `A=180413` through
`N=262144`. At `(J,L)=(64,3757)`, the existing conservative 52-chart formulas
give

```text
one-window cost       1,546,270,015,488
103-window cost     159,265,811,595,264
MCA allowance   254,684,620,614,660,120
```

All projection caps are far below characteristic. Commit `909e863` contains
the scanner, detailed caveats, and an axiom-clean Lean arithmetic receipt.
Thus retuning removes the old extra-agreement minor-collapse gap without an
expensive accepted-high fallback.

#### Exact remaining theorem

For the actual all-node contact kernel in each window, we still need:

```text
full conormal rank < 4
  => U1 on the supplied A agreements has a base-field
     polynomial interpolant of degree <= w.
```

Original bad-row provenance then contradicts this immediately via the already
formal `GlobalO2BadRowConormalBridge6900.no_direction_interpolant_of_bad`.
Equivalently, after shearing by the degree-`w` interpolant on `w+1` anchors, a
fixed symbolic bordered-minor/dual recurrence must show that rank defect kills
the first extra Newton coefficient (then every later one).

The raw terminal width is not that proof. Centering by the automatic
degree-`<A` agreement interpolant costs `A-w-1=49,341` per active factor and
recreates the archived passive-seed-centering obstruction. So the next useful
input is a symbolic first-Newton identity or a high-degree rank-defect
counterexample—not another generic finite sample or profile search.
