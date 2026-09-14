# k0 exact-G / three-border / quadratic-escape gate for lower 6900

Date: 2026-09-14 UTC.  Scope: lower target **6900 only**.  This is a
source-and-consumer theorem audit, not a candidate, build, comparator result,
or submission change.

## Verdict

The retuned profile

```text
(m,slope,curvature,J,L)=(47,16,8,64,3757)
```

makes the **exact-G rank-four wrapper** numerically viable and makes all four
literal locator normals source-legal.  It does not prove either the
filtered-shell recurrence or T2.

There is a useful three-border alternative: corrected `F0,F1,F2` already
give Y/R/S conormal rank three, so they give a regular height-three route
without invoking abstract T2.  Moreover those three rows remain legal in
the 103 width-801 fixed-cutoff windows.  The fourth row `F3` does not.
Conditional on the still-open three-border correction and geometric joins,
the existing dense height-three ledger fits over the 103 windows.

T2 is not the shortcut to the current Fin3 consumer.  The exact ideal

```text
I=(Y,R,S^2)  subset K[Y,R,S,Z]
```

has the rank-two-plus-quadratic escape and radical height three, but **every**
triple of rows in `I` has ordinary three-Jacobian determinant in
`P=(Y,R,S)`.  Thus height three from a possibly doubled quadratic cut does
not imply the nonzero-minor premise of the existing regular-point aggregate
consumer.  This obstruction is Lean-checked for arbitrary generator
combinations in `K0T2HeightThreeConsumerCounterexample6900.lean`.

The scheduling consequence is:

1. the shortest live path is exact-G weak rank four / four-border correction;
2. the honest fallback is fixed-window three-border correction;
3. abstract T2 is strictly longer unless a multiplicity-aware height-three
   consumer is added.

## 1. Exact theorem/counterexample: T2 does not feed the regular consumer

Take

```text
R=K[Y,R,S,Z],   I=(Y,R,S^2),   P=sqrt(I)=(Y,R,S).
```

The first two generators have independent linear parts and the third has the
nonzero intrinsic quadratic class `S^2`.  Hence this is the literal T2 local
model: two smooth cuts plus a quadratic escape.  Also
`R/P = K[Z]`, so `P` is a height-three prime.

However an arbitrary element of `I` is

```text
f=a*Y+b*R+c*S^2.
```

Modulo `P`, its `S` derivative is zero:

```text
partial_S(f)
 = partial_S(a)*Y + partial_S(b)*R + partial_S(c)*S^2 + 2*c*S
 = 0 mod P.
```

Consequently, for any three rows in `I`, the whole `S` column of the ordinary
Jacobian is zero modulo `P`, and its determinant belongs to `P`.  This is not
a bad choice of generators; it survives every three-row change inside `I`.

The Lean theorem

```text
all_generated_triples_jacobian_det_mem
```

proves exactly that statement.  Its axiom audit is

```text
[propext, Classical.choice, Quot.sound].
```

The fixed triple itself has determinant `2*S`.  In characteristic two this
becomes zero, which only strengthens the obstruction; the target
characteristic is odd.

This separates two statements that previous route notes sometimes placed
too close together:

```text
T2  -> local component height >= 3                         valid;
height >= 3 -> existing ordinary-minor Fin3 consumer       false.
```

The target boundary ideal may contain extra rows such as `S*Z`, which can
make the radical component generically reduced.  The counterexample does not
say target T2 is false.  It says **T2 alone** cannot discharge `hminor` in
`Fin4ActualCoordinateDegreeAggregate6900` or
`Fin4ActualCoordinateDegreeTwoPlusSeedAggregate6900`.

## 2. Why three lifted borders are stronger and sufficient for height three

The exact locator normals `F0,F1,F2` have lower-triangular Y/R/S normal
matrix with nonzero diagonal.  If each agreement-side row admits a
complete-contact correction with zero Y/R/S jet, subtracting the corrections
produces three complete-kernel rows with independent Y/R/S jets.

This implication is already formal, not evidence:

```text
GlobalO2ExactGThreeRHSYRSBridge6900
  .completeKernel_YRSDualIndependent_of_threeCorrections

GlobalO2ExactYRSThreeRHSIffAndZSplit6900
  .completeKernel_firstThreeJet_surjective_iff_threeCorrections
```

Thus three lifted borders yield conormal rank three directly and avoid the
nonreduced quadratic example above.  They do **not** yield rank four or an
isolated point.  The remaining Fin4-to-Fin3 component ownership, common-row
selection, generic-fibre, and chart-cover joins are still premises in the
experimental consumers; this audit does not claim those joins assembled.

## 3. Exact source legality: exact-G versus fixed cutoff

Let `g=B+r`, `w=131071`, and use `D=47*B` in a fixed window.

For `F0,F1,F2`, the largest weighted term is bounded by

```text
46*g+w.
```

Hence all six literal weighted-degree guards are strict whenever

```text
46*r < B-w.
```

For the 103 proposed windows, `0<=r<=800` and `B>=180413`, so

```text
46*800 = 36800 < 49342 = 180413-131071.
```

Therefore `F0,F1,F2` are genuinely source-legal throughout every width-801
window for the m47 source.

The exact fourth row uses an anchor set `H` of size `w+1` and

```text
B_H = Lambda_H^46 * Lambda_(G\H)^47,
F3  = B_H * (Y-P-(Z-gamma)q_H).
```

Its top weighted degree is exactly `47*g-1`.  Consequently:

```text
D=47*g     (exact-G): F3 is legal;
D=47*B, r>0 (window): F3 is illegal.
```

The same distinction applies to the full-G centered shell: its exact-G
legality does not transport to a smaller fixed cutoff.  This is why the
three-border fixed-window fallback is meaningful, while a four-border
fixed-window claim is not.

At exact-G cutoff `D=47*g`, all four rows are legal for every
`180413<=g<=262144`: the six F0--F2 bounds use only `w<g`, and F3 has weight
`47*g-1`.

## 4. Retuned filtered-shell status

The following are exact arithmetic/structural facts for m47:

```text
first centered shell grade                 J+1 = 65
centered carrier seed exponent          J+1-m = 18
conjectural terminal grade             J+slope = 80
seed cap                                      L = 3757
top R^2 chain                           y+z = J-2 = 62
zero-depth R^2 tail                     y=47,...,62 (16 equations)
last R^2 X width at g=180413       47*g-64*w+2 = 90869
maximum error count                               81731
terminal width slack                                9138
```

The pure centered carrier

```text
(Y-P-(Z-gamma)Q_G)^47 * (Z-gamma)^18
```

is exact-G source-legal: `deg Q_G<g`, `w<g`, boundary degree is at most 47,
and total centered grade is 65.  This gives the same unit lowest-error-seed
coefficient as the archived shell calculation.

These facts improve the recurrence geometry: the terminal derivative tail
has only 16 layers and its last literal strip is wider than all errors.  They
do not prove controllability.  A known earlier strip still has

```text
W(y=63)=47*180413-63*131071=221938 < N=262144
```

with deficit `40206`, so a proof that silently interpolates arbitrary
all-node data on every same-grade `u1` edge is invalid.  The archived
adjacent-depth audit also proves that deleting HRS strips independently loses
a same-grade `u1` term.  A coupled reversed-Hasse/filtered recurrence remains
necessary.

The finite evidence remains evidence only:

* slope-one exact F101 chambers close F0--F3 at `J+1`, including arbitrary
  error-direction offsets;
* one slope-two chamber is red at `J+1` and green at `J+2`;
* exact Smith controls show bad data can saturate the fourth normal module.

None proves the m47 slope-16 target.  Retuning makes the hoped-for theorem
shorter; it does not turn it into a mechanical width lemma.

## 5. No fixed T2 coefficient has emerged

The osculating self-quadratics give a useful theorem-level reduction.  On a
rank-two first conormal image, at least one of

```text
q_i = a_i * (a_i-2*w_i*Z),   i=0,1,2,
```

is nonzero in the intrinsic quadratic quotient.  This is the domain argument
in `FIXED_B_OSCULATING_QUADRATIC_BORDERED_BREAKTHROUGH_6900.md`; it is a
three-way chart statement and does not select one uniform `i`.

For each `i`, one still needs the source-specific bordered correction
`(BQ-i)`.  It is green in the frozen F7/F17 controls and red by exactly one
rank in the F47 control.  Thus low `m`, full cutoff, source positivity, and
quadratic legality do not imply it.  The F7 factorization of a witness as
`A * unit` is specific to that finite rank-two determinantal scheme and is
not a fixed target coefficient.

For the four-border route, `T=(Q_G-q_H)/Lambda_H` can have its first nonzero
coefficient at an arbitrary index.  Coefficientwise Fitting-ideal membership
would suffice because some coefficient is a field unit, but no one fixed
coefficient is nonzero uniformly.  The honest endpoint is a polynomial
minor proportional to nonzero `T`, or all-coefficient containment, not a
preselected scalar coefficient.

## 6. Hidden consumer arithmetic

The newly observed exact-G rank-four total is correct:

```text
81732 * allChartCost(64,3757)
 = 81732 * 1546270015488
 = 126379740905865216
 < 254684620614660120.
```

It leaves `128304879708794904` of MCA allowance.  This is a rank-four
isolated-point wrapper.  It cannot be reused after proving only CS3 or T2.

For the retuned height-three ledger, the exact projected flags are

```text
omit Y/R/S/Z = (2158400,10722368,20005120,31232),
proper raw   = 152680336126464.
```

Merely charging that raw value once for each exact cardinality gives

```text
81732 * 152680336126464
 = 12478869232288155648
 > MCA.
```

Using the full existing exact height-three incidence formula makes the
all-exact-G total `19551995210644238311`.  Therefore the exact-G m47 wrapper
is green only if the source conclusion is rank four (or a new direct
multiplicity-aware isolated-point theorem is supplied).

In contrast, applying the same height-three formulas once per width-801
fixed source gives, over 103 windows,

```text
exact specialized flags total      24683226535256824
current dense flags total         214887267829583436
MCA allowance                     254684620614660120
dense slack                        39797352785076684.
```

All exact and dense projected degrees and separator degrees are below the
target characteristic.  These are exact integer replays of the existing
height-three formulas, but remain conditional on the unassembled geometric
consumer premises.

## 7. Route decision

```text
exact-G m47 source positivity                              GREEN / exact
exact-G legality F0,F1,F2,F3                              GREEN / exact
exact-G all-cardinality rank-four chart arithmetic         GREEN / exact
filtered-shell F0--F3 complete-contact correction          OPEN
weak rotating rank four                                    OPEN

fixed-window legality F0,F1,F2                            GREEN / exact
three corrected rows -> Y/R/S rank three                  GREEN / formal
103-window dense height-three arithmetic                    GREEN / exact
target three-border correction                             OPEN
geometric/common-row/aggregate joins                       OPEN

T2 quadratic class existence                               GREEN / algebraic
T2 bordered source correction                              OPEN; generic RED
T2 -> local height three                                   GREEN / formal interface
T2 -> current ordinary-minor consumer                      RED / exact counterexample
candidate/build/submission                                 none
```

Do not spend more time on generic T2 samples or another profile search.  For
the primary exact-G route, attack the coupled F0--F3 filtered-shell/Fitting
statement at m47.  If that stalls, the genuinely smaller fallback is the
fixed-window **three-RHS** correction theorem, because it avoids both F3's
fixed-cutoff illegality and T2's nonreduced-consumer gap.

## Reproduction

The only new proof computation is tiny (about four seconds in this checkout;
no finite matrix is built):

```sh
LEAN_PATH=.experiments lake env lean \
  .experiments/K0T2HeightThreeConsumerCounterexample6900.lean
```

