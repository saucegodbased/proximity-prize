# m69 arbitrary-rational rank: numerator-zero-set RED

Date: 2026-09-14 UTC

## Verdict

The proposed universal statement

```text
C_f0 + W*C_f1 + W^2*C_f2 + ... = F^262144
```

for every reduced rational `W=N0/E0` satisfying the current DataEleven
degree, root-free, and coprimality bounds is **false**.  The obstruction is
not cyclic wrap: `N0` is allowed to vanish on more nodes than the smallest
m69 base fringe can control.  At those nodes every positive power of `W`
vanishes simultaneously.

This is a RED result for an abstract arbitrary-rational rank theorem.  It is
not a construction of a complete `DataElevenHighEClosedLeaf`; the actual
incidence and four aligned-source equations may still exclude the hostile
numerator.  Any such exclusion is now a precise missing source theorem.

## Literal m69 shape

The exact census in
`m69_reciprocal_all_defect_interval_gate_6900.py` includes the deficient
shape

```text
(y,r,s) = (0,0,0).
```

For `(M,D,W)=(69,69*180413,131071)`, its residual prefix fringes are

```text
t=0: 127729
t=1: 258802
t=2: 127731
t=3: 258804
t=4: 127733
t=5: 258806
...
```

All powers through `t=68` exist in the local predecessor envelope.  Their
number is irrelevant to the counterexample: every channel with `t>=1`
vanishes on the same numerator-zero set.

## Exact countermodel to the advertised rank hypotheses

Choose a set `Z` of `127730` NTT nodes and put

```text
N0 = product_{i in Z} (X-domain(i)).
```

Thus `deg N0=127730` and `N0` vanishes on all of `Z`.  Choose a non-Frobenius
fixed extension-field element `theta` and

```text
E0 = X^2151-C(theta).
```

Every NTT node is Frobenius-fixed.  The existing power-denominator lemmas in
`TZeroReciprocalResiduePlaneCountergate6900.lean` therefore give that `E0`
is root-free on the domain and coprime to its first conjugate, with the
required second-or-third-conjugate alternative.  Since every root of `N0`
is an NTT node and `E0` is nonzero there, `gcd(E0,N0)=1`.

Take the degree ledger `s=max(deg c,deg d)=0` and `q=deg Q=0`.  Then all
numerical premises proposed for the universal rational gate hold:

```text
deg E0 = 2151
s+q+2151 <= deg E0
s+q <= 8328
deg E0 < 18415
deg N0 = 127730 <= 131071+deg E0+s = 133222
```

There is `5492` degrees of numerator slack.  The hostile zero set is not an
endpoint rounding artifact.

On `Z`, `W=N0/E0=0`.  Restrict the putative source map to `Z`.  Every
positive-power channel is zero, so its image factors through the sole base
prefix `C_127729`.  That prefix has rank at most `127729`, whereas the
function space on `Z` has dimension `127730`.  Hence the restricted map, and
therefore the all-node map, is not surjective.  The defect is at least one.

`M69NumeratorZeroSetRankCountergate6900.lean` proves the generic finite-rank
factorization obstruction and the exact target arithmetic.  It builds with
`LEAN_NUM_THREADS=1`; its printed axiom sets are exactly the standard
`[propext, Classical.choice, Quot.sound]`.  No `decide`, `native_decide`,
`sorry`, or unsafe declaration is used.

The executable receipt is
`m69_numerator_zero_set_rank_countergate_6900.py`.  It recomputes the shape
from the complete m69 defect census, checks all displayed inequalities, and
emits the exact restriction defect.  Its bounded run used under 40 MiB RSS.

## Full-leaf audit and exact missing lemma

No current full-leaf field bounds the number of domain zeros of `N0` below
`127730`:

* `ActualAdjacentFilteredHardCornerElimination6900` stores
  `IsCoprime E0 N0` and root-freeness of `E0`, not root-freeness of `N0`.
* `ActualProperSelectedQuotientFamily6900` proves only
  `deg N0 <= 131071+deg E0+s`.
* `M69DataElevenRationalGate6900` exports the weaker uniform cap
  `deg N0 <=149776`.
* `ProperNodalDenominatorRootFree6900` proves that the normalized
  **denominator** is root-free; it has no corresponding numerator theorem.
* The normalized cross identity is currently available only off the content
  roots until the separate common-factor adapter is handled.

Therefore the minimum new premise needed even to reopen a universal m69
rank argument is

```text
#{i | N0(domain(i))=0} <= 127729,
```

or a source channel independent of positive powers of `N0` on that zero set.
This bound would remove the present counterexample but would not by itself
prove arbitrary-rational surjectivity.

## Route decision

Do not spend more time proving the unqualified arbitrary-rational rank map.
The rational route must split on the nodal zero count:

1. **many numerator zeros:** use the actual relation
   `d*U0-c*U1=0` on those live nodes together with projective highness,
   agreements, or the four aligned source equations to count/exclude this
   branch;
2. **few numerator zeros:** puncture the zero set and prove a rank theorem on
   the remaining coordinates, charging the punctures explicitly;
3. keep the common-factor/content-root adapter as a separate charge, rather
   than silently cancelling `B` at all nodes.

The earlier reciprocal-monomial interval GREEN remains correct in its stated
scope because its numerator is a unit and has no nodal zeros.  It cannot be
promoted to arbitrary rational functions without this new split.
