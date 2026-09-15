# W=133226 extended L-shape: full-node GREEN

## Decision

**GO**, uniformly for every identity-node cardinality at most `262144`.

The initial cutoff-three idea is arithmetically viable, but it is unnecessary.
A more precise terminal partition closes even the zero-exception case.  The
key is not to enlarge the old L rectangle.  Keep the old arms and make the two
small regions responsible for the failed helper bands into skinny terminal
branches.

No literature is used in this audit.

## Fixed source data

All worst-case calculations use

```text
N = 262144, A = 180413, W = 133226
q = 1453806, v = 68769, p = 2130706433
retained core floor = 263611557201523206.
```

The primary source is

```text
(k,m,B,M,D,T) = (61,550,99227150,744,244,122)
target rank    = 1503271269
column lower  = 394074801989406
kernel lower  = 1258448670 > 0.
```

The single helper source is

```text
(k,m,B,M,D,T) = (1312,11810,2130677530,15993,5248,2624)
target rank    = 314478446061020
column lower  = 82571120962332601259
kernel lower  = 132483198112574379.
```

The helper global flag is `(10745,2624,2624)`.  Thus every exit can use one
identical helper interface; no heterogeneous-box aggregation is needed.

## Why the old helper looked red

At `W=133226,N=262144`, the old one-dimensional bands are indeed red:

```text
J >= 213, derivative only known >= 2: deficit 825300383556963
D >= 56, jet only inferred >= 28:     deficit 1119660030451889.
```

Moving the whole terminal to `(J,D)=(212,56)` is the wrong repair.  Even after
joint primary retuning its worst ledger is

```text
277935362066347310,
```

which exceeds the retained floor by `14323804864824104`.

Dropping an identity node while also dropping one agreement is worse: at
`N=262141,A=180412`, an exhaustive necessary-band scan has no `D55` helper
survivor.  The lost source width costs far more than the refunded target row.

## Extended terminal

Use the predicate

```text
(J <= 211 and derivative <= 55)
or (J <= 212 and derivative <= 54)
or derivative <= 3
or J <= 32.
```

Its negation, together with the old L-shape complement, has exactly three
helper cases:

```text
(J >= 213 and derivative >= 4)
or (J >= 33 and derivative >= 56)
or (J >= 212 and derivative >= 55).
```

The final disjunct is the isolated old corner once the first two disjuncts
have been excluded.  The corresponding *relaxed* stage-band sums, i.e. the
actual upper bounds already supported by the Lean fibre theorem, are

```text
profile              relaxed band          margin below kernel lower
J213 + derivative4   131697390021082959     785808091491420
J33  + derivative56  132414068905236615      69129207337764
J212 + derivative55   90686016876092931   41797181236481448.
```

The smallest margin is still `69,129,207,337,764`, so this is not relying on
the stronger exact-column-difference band.

## Why the skinny count is semantically valid

Two deliberate loosenings are load-bearing.

1. `derivativeDegree <= 3` sharply gives `RT <= 3,T <= 1`.  Using `T=1`
   directly would make the reduced agreement's `all` coordinate zero, so the
   small-family absorption gate would fail.  Instead embed this product in
   the valid loose nested box

   ```text
   (J,RT,T)=(744,7,7), source flag=(737,0,7),
   agreement flag=(196241899,133226,1598712).
   ```

   This is still a true box bound, has `1 <= T <= RT < J`, and clears both
   absorption inequalities uniformly for every node set of cardinality at
   least the agreement cutoff: `agreement.all=1598712 >= small=1453806`.
   Its projection cost is only `23314550<p`.

2. `J <= 32` directly implies `RT,T <= 32`.  Embed it in

   ```text
   (J,RT,T)=(33,32,32), source flag=(1,0,32),
   agreement flag=(133227,133226,8260012).
   ```

   The extra one in the J cap supplies the strict `RT<J` hypothesis of the
   honest reduced-cut support theorem.  Its projection cost is
   `532904000<p` and both absorption gates are far inside the boundary.

These two box implications and every numeric gate are already formalized in
`WeightedIdentityExtendedLShapeArithmeticW1332266900.lean`.

## Full count ledger

The uniform shortened-Johnson inequality at the worst node count is positive
by

```text
RHS - LHS = 40353814003.
```

The primary cleanup is

```text
15607077754697448.
```

The old arms still use the tight shared terminal/exit resource aggregation:

```text
terminal                 active cap            with cleanup           headroom
old arm A             247945303343219481    263552381097916929       59176103606277
old arm B             244053597157924510    259660674912621958     3950882288901248.
```

For the skinny branches there is so much slack that no coupled LP is needed.
Charge the terminal rest by its skinny flag and charge every exit by the full
primary flag independently.  The common helper-exit cap is
`788423032100813`:

```text
terminal                 rest+exit+cleanup       headroom
derivative <= 3 loose      37326710447254461    226284846754268745
J <= 32 loose              23584483773907223    240027073427615983.
```

Thus every possible terminal is strictly below the retained core floor.  All
figures use `N=262144`; smaller actual identity sets follow by max-node
monotonicity.  The derivative-skinny absorption itself is cardinality-safe
because its agreement `all` coordinate already dominates `small`.

## Formal state and remaining work

Compiled and axiom-audited now:

* conservative source-dimension arithmetic;
* all three relaxed helper margins;
* exact complement of the extended terminal;
* both skinny nested-box implications;
* worst-cardinality shortened Johnson;
* old-arm shared-resource dominance and exact coupled caps;
* skinny rest/exit caps, cleanup, absorption, and characteristic gates.

Remaining mechanical modules for an end-to-end W133226 theorem are:

1. port the primary/helper target and column lower receipts to W133226;
2. formalize the three relaxed band sums above;
3. instantiate generic certified terminal selection with the extended
   predicate;
4. add the two skinny regular-family consumers and case-split the terminal;
5. connect the result to the existing support-core retention theorem.

There is no remaining arithmetic or semantic-design uncertainty in this
architecture.  The most delicate point—the zero `all` coordinate at sharp
`T=1`—is explicitly avoided rather than assumed away.

## Reproduction

```bash
g++ -std=c++17 -O2 -fopenmp \
  .experiments/weighted_w133226_cutoff34_full_audit_6900.cpp \
  -o /tmp/weighted_w133226_cutoff34_full_audit_6900
/tmp/weighted_w133226_cutoff34_full_audit_6900 133226

LEAN_PATH=.experiments lake env lean \
  .experiments/WeightedIdentityExtendedLShapeArithmeticW1332266900.lean
```

The Lean audit prints only `propext`, `Classical.choice`, and `Quot.sound`.
It contains no `decide`, `native_decide`, `sorry`, or new axiom.
