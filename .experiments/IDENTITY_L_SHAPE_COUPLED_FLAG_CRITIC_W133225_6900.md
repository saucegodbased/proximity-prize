# W=133225 L-terminal coupled rest/exit audit: GO at the consumer seam

## Verdict

**GO** for the L-shaped terminal, strict factor descent, common helper-box
upgrade, and coupled rest/exit count algebra.  I found no counterexample or
invalid inference in those consumer-side steps.

This does **not** turn a product-band inequality by itself into a complete
helper certificate.  The first load-bearing producer seam is still:

```text
band < source kernel
  -> nondivisible low-power quotient G
  -> choose an original prime factor F and complement C
  -> H = C^j G is nonzero, F-proper, in the advertised helper box,
     and vanishes on every regular solution of F
  -> factor-level CommonCertificate F.
```

The W=133224 modules prove exactly this chain at the old parameters, so the
W=133225 work is a parameter port rather than a missing mathematical idea.
Nevertheless, until that port is checked, the global `hstep` remains an
explicit premise and the full 6900 proof is not closed.

## Exact L-shape call graph

Define

```text
Terminal(J,D) := (J <= 211 and D <= 55)
              or (J <= 212 and D <= 54).
```

Its negation has the exact exhaustive form

```text
D >= 56
or (D <= 55 and (J >= 213 or (J = 212 and D = 55))).
```

Thus:

1. `D>=56` uses the D-heavy producer;
2. otherwise `J>=213` uses the J-heavy producer;
3. the only remaining point is `(J,D)=(212,55)`, which uses the joint corner
   band and exits a factor; and
4. `(0,0)` is terminal, so a nonterminal current set is nonempty.

The corner is deliberately **not** a cheap terminal.  This avoids the red
full-rectangle agreement flag.  It is safe for both singleton and
nonsingleton products: strict descent only needs one certified member of the
current set, then removes that member.  For a singleton the complementary
product is `1`, and the usual deflated helper is simply `G`.

The generic theorem to instantiate is

```text
WeightedHeavyBatchPartitionW1332246900.exists_certified_terminal_subset
```

with the L-shaped predicate.  The specialized theorem
`heavy_products_partition` must **not** be reused unchanged: it hardcodes the
old rectangle `J<=211,D<=55`.

Certificates retained by the induction are stable.  Although a witness may
contain the current subset, complement, stage, and helper, its exported
factor-level semantic statement no longer depends on future recursive sets.
The recursion removes a genuinely certified member, so it is strictly
cardinality-decreasing.

## Why the common helper-box upgrade is sound

For the two-producer version the J-helper box has

```text
(B,M,D,T) = (1,894,156,087, 14,217, 4,688, 2,344)
```

and the D-helper box has

```text
(B,M,D,T) = (2,023,512,208, 15,188, 4,960, 2,480).
```

Every J coordinate is at most the corresponding D coordinate.  Membership in
`globalOrder2CoefficientBox` is monotone in all four caps.  Enlarging the box
does not change the polynomial, nonzeroness, `not F | H`, or its solution
vanishing theorem.  Hence all exits may be aggregated with the common flag

```text
(10228,2480,2480).
```

The newer one-source profile

```text
(m,B,W,D,T,M,jmax,delta)
  = (11810,2130677530,133225,5248,2624,15993,2624,47190)
helper flag = (10745,2624,2624)
```

removes even this heterogeneous-box bookkeeping.  The coupled proof below is
formally checked for both envelopes.

## The coupled resource algebra

For a direct flag `p=(z,y,s)`, use nested resources

```text
T(p) = z+y+s,   M(p) = y+s,   S(p) = s.
```

For fixed second and third flags, `flagMixed` has the exact expansion

```text
flagMixed(p,q,r)
  = cT(q,r)*T(p) + cM(q,r)*M(p) + cS(q,r)*S(p),

cT = flagMixed((1,0,0),q,r),
cM = flagMixed((0,1,0),q,r) - cT,
cS = flagMixed((0,0,1),q,r) - flagMixed((0,1,0),q,r).
```

All three marginals are nonnegative.  Let `rx,ex,Px,Ax` be the rest, exit,
primary, and terminal-cap amount of any one nested resource.  The partition
and terminal hypotheses are exactly

```text
rx + ex <= Px,   rx <= Ax,   Ax <= Px.
```

If the scaled exit marginal `ce` is at most the scaled rest marginal `cr`,
then

```text
cr*rx + ce*ex <= cr*Ax + ce*(Px-Ax).
```

Apply this once to each of `T,M,S`.  This is the complete LP argument; it does
not assign the full primary flag to either side twice.  Note that the
hypotheses are cumulative.  It would be invalid to infer direct componentwise
bounds on the exit flag merely by subtracting the direct rest flag.

The factor partition supplies these hypotheses exactly: disjoint rest and
exit sums add to the one ambient exact-flag sum, while the terminal product
supplies the three smaller rest caps.

## Endpoint arithmetic

Here

```text
n-v = 193380,   a-v = 111650,
primary direct flag = (496,122,122),
primary resources   = (740,244,122).
```

Arm A uses

```text
rest flag/resources = (156,28,27) / (211,55,27),
exit complement     = (340,94,95) / (529,189,95),
agreement flag      = (41432976,7593825,6927700).
```

Arm B uses

```text
rest flag/resources = (158,27,27) / (212,54,27),
exit complement     = (338,95,95) / (528,190,95),
agreement flag      = (41965876,7327375,6927700).
```

With the common D-helper envelope, the exact coupled ceilings are

```text
arm A active cap = 247893461599917381
arm B active cap = 244001988473045789

arm A + cleanup  = 263416184855619655
core floor       = 263611557201785349
arm A headroom   =    195372346165694.
```

The arm-A common numerator is

```text
3090171101868976092117810000.
```

With the single-source helper envelope they are

```text
arm A active cap = 247924633751427236
arm B active cap = 244033198200074653

arm A + cleanup  = 263447357007129510
arm A headroom   =    164200194655839.
```

The smaller single-source headroom is still strict.  Arm B is green by more
than four quadrillion after cleanup in either envelope.

## Exact integration requirements

The final consumer must preserve these four steps in this order:

1. retain every factorwise two-incidence inequality on the terminal rest;
2. retain every factorwise one-incidence inequality on the exits;
3. derive the combined and terminal-only cumulative sums from the exact
   disjoint factor partition; then
4. couple the two groups and divide by `(a-v)^2` only once.

Calling an already aggregated `armA_remainder_scaled` and independently
calling a full-primary exit aggregate loses the shared-resource information
and reintroduces the old double charge.  The per-factor theorem inside the
arm-A proof must be exposed/reused before aggregation.  Arm B is the same
construction with `J<=212,D<=54,T<=27` and its own agreement flag.

## Remaining shortest theorem chain

Consumer side:

```text
generic L-terminal strict partition
 -> per-rest-factor cheap inequalities
 -> per-exit-factor common-helper inequalities
 -> exact six cumulative budgets
 -> coupled_flagMixed_le
 -> one common ceiling
 -> add minimum primary cleanup.
```

Producer side (the first presently load-bearing seam):

```text
hard_lshape_product_band_lt_kernel
 -> exists_low_power_quotient at fuel 2624
 -> positiveT_subset_escape
 -> W133225 deflated capacity/box/properness/vanishing adapter
 -> CommonCertificate
 -> L-terminal hstep.
```

## Formal receipt

`IdentityLShapeCoupledFlagCriticW1332256900.lean` proves:

* the cumulative expansion of `flagMixed`;
* the scalar exchange lemma;
* the generic three-resource coupled inequality;
* the exact nonterminal L-shape case split;
* arm-A and arm-B coupled bounds for both helper envelopes; and
* all four endpoint caps and both tight arm-A headrooms.

It compiled under the local 6 GiB allocator cap in 7.2 seconds.  Printed
axioms are only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorry`, `decide`, or `native_decide`.
