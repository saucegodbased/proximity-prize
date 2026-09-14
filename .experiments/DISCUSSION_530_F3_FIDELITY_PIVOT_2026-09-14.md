### Lower 6900 update: actual-F3 factor lift found, then target-error fidelity gate rejects its scaling

This is a self-contained update on the Full187/order-two line. It changes no
submission or claim. The live benchmark floor is now 68.10; this checkout's
accepted production baseline remains 68.06. There is no 69.00 candidate.

#### What was proved exactly

After the complete-depth Pascal/Hermite projection, earlier work had proved:

* 17,793,064 of 20,415,725 terminal provenance occurrences cancel in complete
  blocks (87.15%);
* all 9,482 first-fringe adjacent pairs have full row rank, including all
  eleven q=26 shapes;
* an isolated second-fringe defect of dimension 7,797 is removed on two named
  *physical aggregate rows* by adjacent-slope q=0 pivots, giving an exact
  unitriangular block. This is not whole-frontier closure: each pivot still
  exports large nonprincipal and positive-u0 tails.

The separated candidate family was then stopped completely. For

```text
K_i = H^(59-i) R^60 E^i V^(i+1) W^(60-i),  0 <= i < 60,
```

even arbitrary polynomial mixing cannot satisfy the source taper: the top
Y^61 coefficient forces a polynomial identity whose reduction modulo E gives
H^59=0, contradicting gcd(H,E)=1. So any successful F3 lift must be genuinely
nonseparated.

Commit `7b9734c` found such a mechanism in the established F101 chamber. It
uses order-1/2/3 covariants on both agreement and error strata. For exponent
triples alpha and epsilon, with contact weights a and e, its factorized
generators are

```text
H^max(m-1-a,0) R^max(m-a,0) E^max(m-e,0)
  * (Y-Z*q_H) * A0^ay A1^ar A2^as * E0^ey E1^er E2^es.
```

Every generator is checked against the literal complete-contact map. Exact
F_101 elimination with X,Z shifts <=7 gives a 1,768-term representative with:

```text
complete-contact rows: 0
boundary: exact F3 = B*(Y-Z*q_H)
boundary degrees: (26,-1,-1,31)
all source monomials legal: true
unsafe safe-103 face terms: 0
representative sha256:
  9f507637f28f5256934ed6f3f802a4bf0ffeb2f3565aa770f27b8eb4c3581253
```

Both adjacent ablations are RED by rank one: X<=6,Z<=7 and X<=7,Z<=6. Thus
the passive direction is load-bearing; this is not the previously rejected
K[X]-only construction.

#### The target-fidelity check is RED

The positive chamber used zero direction on the error nodes. Full187 instead
uses the nonzero error word delta(X)=X^81730. Commit `2de9bee` reruns the same
literal packet and factor module with the exact small analogue delta=X^2,
centered in all three error covariants and in the received contact map.

Every generator remains complete-contact zero, but source-tail membership is:

| max X shift | max passive-Z shift | correction rank | augmented rank |
|---:|---:|---:|---:|
| 7 | 7 | 3135 | 3136 |
| 8 | 7 | 3303 | 3304 |
| 7 | 8 | 3506 | 3507 |
| 8 | 8 | 3691 | 3692 |

All four are RED by exactly one. We are therefore freezing rectangle widening
for this module. The matched-error GREEN explains the earlier dense F101 lift,
but it is not positive evidence for the actual target error word.

There is also a degree-ratio mismatch:

```text
F101:   g = e+w = 8
Full187: g-(e+w) = 180413-(81731+131071) = -32389.
```

So the original chamber was not ratio-faithful in the load-bearing
error-degree/active-weight balance.

#### Current decisive gates

The first gate is the exact target pure-Y specialization. Any legal F3 lift
would induce

```text
K(X,Y) = B(X)Y + sum_(n=2)^82 A_n(X)Y^n,
deg A_n < 60*g - n*w,
G^(60-n) | A_n                       (2 <= n < 60),
E^(60-j) | sum_(n=j)^82 binom(n,j)A_n (0 <= j < 60),
```

where `B=H^59 R^60=G^59 R`, `deg G=180413`, `deg E=81731`, and
`GE=X^262144-1`. Including A1 as a variable leaves 122,266,337 dimensions
after agreement divisibility against 149,567,730 error conditions, a raw
deficit of 27,301,393. Ratio-faithful N=64 controls are RED for m=3..12, but
counts and controls are not a target proof. We are seeking an exact
target-specific shifted-Pade/Popov remainder or dual. A target RED here stops
*every* Full187 F3 source-containment approach, including larger bicovariant
modules.

In parallel, the second gate aggregates the entire first later-Z frontier
exported by the two cross-slope P59 pivots, including every same-key physical
origin, curvature collision, and higher jet. The required outcome is either a
closed SCC/rank defect (STOP) or legal sections under one common well-founded
order (GO), not another hand-picked row.

The saturated-conic lemma in the earlier discussion comment is structurally
suggestive, but it does not yet identify this complete sector or certify the
global weighted X/Z filtration. We are not using it as evidence until those
hypotheses are supplied.

Exact research receipts: `9276998`, `500026a`, `91265f0`, `7b9734c`,
`2de9bee`, and process audit `2196af9`.
