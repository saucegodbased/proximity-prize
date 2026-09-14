# Accepted-6810 source threshold and Full187 adapter gate

Date: 2026-09-14 UTC.  Target: lower 6900 (`agreement = 180413`).

## Binary verdict

**RED for a direct retarget of the accepted P4 source.**  Every one of the ten
literal source kernels in accepted commit `09d8a2a` has negative signed
coefficient-minus-rank excess at the target agreement (so the corresponding
natural-number nullity lower bound is zero).  Each is already in the chamber
where the signed excess is affine in total cap `L`, and its target slope is
negative, so increasing `L` only makes the failure worse.

**GO for source dimension, but RED for the adapter, for Full187.**  The
existing one-extra-curvature-variable source at

```text
(m,M,slopeCap,curvatureCap,seedCap) = (60,82,21,10,2703)
D = 60*180413
```

has exact target margin `+9,757,693`.  It is the smallest already-formalized
source change that demonstrably crosses the dimension threshold.  However it
does not inhabit the ordinary `ConstraintKernel` required by the accepted
Higher phase, and the two obvious coercions back to that kernel are false.
Thus no existing theorem simultaneously supplies the new positive source and
the accepted Higher consumer.

The action implied by this gate is unambiguous: stop tuning `m,s,L` in the
accepted P4 source.  Either finish an actual-divisibility P5-to-phase adapter,
or make the factor phase native to the Full187 polynomial.  A scalar
specialization or first-two-helper shortcut is not a valid bridge.

## 1. Exact accepted-profile failure

The checker

```text
.experiments/accepted6810_source_slope_threshold_6900.py
```

evaluates the literal `RCN119.coefficientCount` and `localRankBound` formulas
with exact integers.  It reproduces every accepted signed excess in
`HigherKernels80850.lean`, then changes only `D=m*181294` to `D=m*180413`.

| kernel | accepted signed excess | target signed excess | accepted L-slope | target L-slope |
|---|---:|---:|---:|---:|
| A | 2,415,525 | -76,612,802,872,130 | 3,464,475 | -482,231,575 |
| B | 14,080,615 | -22,658,732,083,671 | 17,439,226 | -565,193,304 |
| T | 1,575,567,595 | -32,756,551,753,835 | 942,296,810 | -2,822,631,875 |
| Source00 | 112,368,330,339,950,765,247,528 | -220,090,056,863,886,727,062,784 | 44,009,595,957,267,554 | -43,684,927,597,335,735 |
| Source01 | 13,986,869,220,384,145,651,984 | -20,726,846,964,163,996,398,886 | 5,475,573,901,047,327 | -5,455,965,401,118,023 |
| Source02 | 12,234,685,572,049,001,011,984 | -18,980,938,035,806,229,038,886 | 5,475,573,901,047,327 | -5,455,965,401,118,023 |
| Source03 | 502,972,248,297,244,942,575 | -930,640,210,049,624,524,047 | 681,584,000,624,865 | -684,047,863,829,196 |
| Source04 | 31,126,202,584,300,507,075 | -58,495,105,198,091,600,080 | 84,615,720,487,095 | -86,127,167,413,056 |
| Source05 | 9,873,296,301,718,971 | -19,550,893,759,173,647 | 148,947,874,404 | -184,888,376,958 |
| Source06 | 1,507,744,192,739,885,167,111 | -1,775,385,389,804,909,385,811 | 449,603,508,027,916 | -455,009,375,948,556 |

This is an exact RED for these callers, not a heuristic slope extrapolation.
In Lean's `Nat` subtraction every displayed negative target excess becomes
zero, so none proves a nonzero kernel.  The negative target slope additionally
rules out repairing any of them by raising its total cap.

## 2. Exact slope formula and threshold

Once all weighted columns have appeared, the coefficient of `L` is

```text
C(m,s,A) = sum_{j=0}^s sum_{i>=0}
             max(m*A - w*i - (w-1)*j, 0),       w=131071.
```

For `T_j=m*A-(w-1)j` and `q_j=floor((T_j-1)/w)`, one row is exactly

```text
(q_j+1)*T_j - w*q_j*(q_j+1)/2.
```

The exact contact-rank slope, valid for every `0 <= s < m`, is

```text
R(m,s) = (s+1)*m*(m+1)/2
         - sum_{k=1}^{min(s,floor(m/2))}
             (s+1-k)*(m+1-2k).
```

Hence the nullity slope is `C-262144*R`.  Exhaustion of every
`1 <= s < m <= 1200` gives:

```text
A=180413: no positive profile; best = -293014 at (m,s)=(2,1)
A=180893: no positive profile; best = -288214 at (m,s)=(2,1)
A=180894: 160 positive profiles; best = 561573060 at (1200,371)
```

This finite statement is deliberately scoped to the displayed box.  It is
not presented as an exhaustive theorem for every finite `m`.

There is also a symbolic asymptotic obstruction.  Put `alpha=A/w` and
`s/m -> beta`.  For `0 < beta <= 1/2`, after removing the positive factor
`beta*m^3/6`, the leading nullity slope is

```text
F_A(beta) = (w-2n)*beta^2 + 3*(n-A)*beta
            + 3*(A^2/w-n),                     n=262144.
```

At `A=180413`, this concave quadratic has its maximum at

```text
beta = 245193/786434
max F = -663688416451941/206157381628 < 0.
```

For `1/2 <= beta < 1`, the leading rank becomes
`n*m^3*(beta/4+1/24)`.  The leading nullity is maximal at the left endpoint:

```text
H(1/2)  = -8991469861/6291408 < 0
H'(1/2) = -15931592423/1048568 < 0,
```

and its derivative decreases through this chamber.  The kernel-checked file

```text
.experiments/Accepted6810SourceAsymptoticGate6900.lean
```

formalizes strict negativity in both rational-beta chambers without
`decide`, `native_decide`, or enumeration.  The first integer agreement for
which the low-chamber asymptotic maximum becomes positive is `180852`; the
finite `m<=1200` transition is later, at `180894`.  This explains why the
accepted agreement `181294` supported the architecture while `180413` does
not: the target is below the structural P4 threshold, not merely below one
unlucky parameter choice.

Scope caveat: this proves all fixed positive-density asymptotic rays and the
stated finite box, plus exact failure of all accepted profiles.  It does not
claim an exhaustive finite no-go for arbitrary `m>1200` with sublinear `s`.

## 3. Smallest existing positive source

`OriginalPassiveSeedSource6900.lean` defines

```text
PassiveSourceIndex D w M slopeCap curvatureCap seedCap
```

with inner variables `X,Y,R,S` and an outer passive-seed variable.  Relative
to the accepted `X,Y,R,Z` P4 box, the essential new freedom is the curvature
exponent `S`; the contact substitution tracks the second-order expression
`Y-X*R+X^2*S`.  `Order2ContactCurvatureElimination6900.lean` records the
triangular curvature elimination and the full 187-derivative-pair receipt.

At the literal target profile:

```text
columns                 162963415163901
one-node rank                621656057
262144 * one-node rank  162963405406208
margin                           9757693
```

`PassiveSourceExactContact6900.exists_exact_contact_source` is the semantic
source constructor.  `PassiveSourceActiveFactor6900.
exists_source_with_irreducible_active_factor_rule` and its strong variant
show that the resulting flattened polynomial still supports irreducible
factor ownership.  Thus Full187 is not merely a spreadsheet dimension: the
source/contact/factorization front end is formalized.

## 4. Exact caller and endpoint mismatch

The accepted call chain is:

```text
HigherKernels80850.{Source00,...,Source06}.finrank_gap
  -> HigherSourceSound6810.SourceXX.sound
  -> HigherRouting6810.PhaseKernelRealization.gap_le_finrank
  -> HigherRouting6810.stateLocalRegularBoundOn_onePhase
  -> exists_strict_helper_split_of_batch_source_thin
```

The endpoint type in `PhaseKernelRealization` is literally

```text
gap <= finrank (ConstraintKernel D 131071 totalCap slopeCap m domain u0 u1)
```

for the ordinary four-variable source.  Full187 produces a `SeedPoly` whose
flattening has the extra curvature coordinate.  It therefore cannot be
dropped into this field, even though it has a positive source margin and an
active irreducible factor.

Two candidate adapters have exact countergates:

1. **First two graph helpers.**  The accepted strict phase needs actual
   divisibility of every current row by each universal factor so that
   `universalProduct_dvd` and `kernelQuotient_regularProduct_nested` can divide
   by the common squarefree product.  `P5WeakHelperCounterexample6900.lean`
   takes `row=S^2+R`, `carrier=R`: helper values of orders zero and one are
   carrier-divisible, but the row is not.  Low-helper universality cannot feed
   the accepted quotient consumer.
2. **Scalar curvature evaluation.**  At one node let
   `E=Y-X*R+X^2*S` and `P=X^58*E^30`.  P5 contact is 148, while any displayed
   scalar shear gives `X^58*(Y-X*R)^30`, whose ordinary contact is only 118.
   Fixed-curvature contact is not the uniform hidden-curvature condition in
   `ConstraintKernel`.

The only semantically sound reuse of the accepted quotient mechanism is to
define universality by **actual divisibility of the whole P5 row**, divide
the common factor coefficientwise in `S`, and retain the original multiplied
row.  Existing audits show that route is structurally compatible, but its
known retained charge is a target phase no-op and no complete
`PhaseKernelRealization`/strict-split theorem has been built from it.

## 5. Reproduction and process decision

```text
python3 .experiments/accepted6810_source_slope_threshold_6900.py
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Accepted6810SourceAsymptoticGate6900.lean
```

Both pass.  The Lean audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the two inequality theorems, and only `propext` for the
Full187 arithmetic receipt.

The next useful theorem is not another P4 profile search.  It is one of:

* a Full187/P5 actual-divisibility strict-subset plus quotient theorem whose
  output has the exact data consumed by `stateLocalRegularBoundOn_onePhase`; or
* a native P5 analogue of that phase consumer.

Until one of those is green, Full187 is a positive source, not an assembled
6900 Higher proof.
