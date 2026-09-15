# K0 all-node weighted osculants: rung six GREEN, rung seven RED

Date: 2026-09-15 UTC. Scope: lower 6900, corrected low-head recurrence.
This is a source/contact breakthrough receipt, not a completed 6900 theorem,
candidate, build, or submission.

## Verdict

There is a genuine cap-legal rank-four packet at error contact order six.
It removes the first `Y/R/S` multiplier cliff in the common-`J` recurrence.
The packet is

```text
H^38 J^6,
H^38 J^4 C1,
H^38 J^3 C2,
H^38 Z J^6.
```

Here `H` is the degree-180413 agreement locator, `N=H*Q` is the
degree-262144 full-node locator (`Q` is the degree-81731 error locator), and

```text
J  = Y - U0(X) - U1(X) Z,
V  = R - U0'(X) - U1'(X) Z,

C1 = N' J - N V,

C2 = N^2 (2 S - U0''(X) - U1''(X) Z)
       - 2 N N' (R - U0'(X) - U1'(X) Z)
       + (2 (N')^2 - N N'') J.
```

`C1` has contact order at least two and `C2` contact order at least
three at **every** old node.  The four displayed sources have agreement
contact at least 44 and error contact at least six.  They have a rank-four
fresh-boundary symbol and all fit the literal target K0 box.

This does **not** continue as a monomial semigroup recurrence.  Every
individual order-seven monomial in `J,C1,C2` already exceeds the strict X
cutoff by 30,871 before charging an active-variable weight.  Its boundary
gradients do not collapse; the obstruction is source cost.  Thus this result
advances the structural recurrence exactly one rung, from five to six, but
does not close orders 7 through 43.

## 1. Exact all-node contact algebra

At an old node write the local parameter as `epsilon`.  Literal K0 contact
gives

```text
J' = V - 2 epsilon S + 3 epsilon^2 T,
J'' = (-2 S - U0'' - U1'' Z) + 6 epsilon T.
```

Both `N` and `J` are divisible by `epsilon`.  For arbitrary polynomials
vanishing at epsilon zero, define the ordinary transvectants

```text
T1 = N J' - N' J,
T2 = N T1' - 2 N' T1.
```

Writing `N=epsilon*A` and `J=epsilon*B` gives, identically,

```text
T1 = epsilon^2 (A B' - A' B),
T2 = epsilon^3 (A C' - 2 A' C),  where T1=epsilon^2 C.
```

The raw first osculant differs from `-T1` by

```text
-N (2 epsilon S - 3 epsilon^2 T),
```

which is also divisible by `epsilon^2`.

For the second raw osculant, the exact difference from `T2` is

```text
(N^2 - epsilon N N') (4 S - 6 epsilon T).
```

If `N=epsilon*A`, then

```text
N^2 - epsilon N N' = -epsilon^3 A A'.
```

This proves third contact without truncating a Taylor expansion and explains
the otherwise surprising `+4*N^2*S` correction.  After combining that term
with `N^2*(-2S-U'')`, one obtains the displayed `N^2*(2S-U'')` formula for
`C2`.

These identities are node-independent.  Translating each old node to
epsilon zero proves the claimed orders at every node; no generic-rank or
finite-field experiment is being substituted for the contact proof.

## 2. Why the four sources carry the boundary themselves

At the fresh compatible boundary, use coordinate order `(S,Y,R,Z)`.  Ignore
the data-dependent last coordinate temporarily.  The gradients of
`J,C1,C2,Z` have the triangular form

```text
dJ  = (0,       1,          0, *),
dC1 = (0,      N',         -N, *),
dC2 = (2 N^2, 2(N')^2-NN'', -2NN', *),
dZ  = (0,       0,          0, 1).
```

Their determinant is `-2*N^3`.  The four order-six powers have derivatives

```text
d(J^6)       = 6 J^5 dJ,
d(J^4 C1)    = 4 J^3 C1 dJ + J^4 dC1,
d(J^3 C2)    = 3 J^2 C2 dJ + J^3 dC2,
d(Z J^6)     = 6 Z J^5 dJ + J^6 dZ.
```

Elementary row operations therefore give determinant

```text
-12 * N^3 * J^18.
```

Multiplication by the common `H^38` contributes the harmless nonzero factor
`H^152`.  Over the generic fresh-point coefficient field, `N` is nonzero.
For a genuine non-perfect candidate, `J` is also nonzero.  Characteristic
`2130706433` kills neither 2 nor 3.  Hence the packet has rank four.  The
perfect-fit branch (`J=0`) is separate and does not represent an
81731-error candidate.

This is the key saving: the old packet used a scalar order-six carrier and
then multiplied it by `Y`, `R`, or `S`, costing about 131071 weighted
degrees.  `C1` and `C2` already contain the slope and curvature boundary
directions, while `Z*J^6` supplies the fourth direction at weight zero.

## 3. Exact target cap ledger

Use

```text
n=262144, g=180413, e=n-g=81731,
w=131071, D=47g=8479411,
(B,s,U,L)=(16,8,64,3757).
```

Assume the full received interpolants have their honest worst degree
`deg Ui <= n-1`.  The maximum weighted degrees inside the osculants are

```text
C1:
  N'Y             (n-1)+w       = 393214
  NR               n+(w-1)      = 393214
  data-only tail    2n-2         = 524286   [maximum]

C2:
  N^2 S             2n+(w-2)     = 655357
  NN' R             (2n-1)+(w-1) = 655357
  (2N'^2-NN'')Y     (2n-2)+w     = 655357
  data-only tail     3n-3         = 786429   [maximum].
```

Consequently all three order-six constructions have exactly the same worst
weighted degree:

```text
H^38 J^6:       38g + 6(n-1)       = 8428552
H^38 J^4 C1:    38g + 4(n-1)+2n-2 = 8428552
H^38 J^3 C2:    38g + 3(n-1)+3n-3 = 8428552.
```

The strict-cutoff slack is

```text
D - 8428552 = 50859.
```

Multiplication by `Z` has weight zero.  The non-X envelopes are tiny:

```text
J^6 or ZJ^6: s=0, r=0, total degree <=7;
J^4 C1:      s=0, r<=1, active degree <=5, total <=6;
J^3 C2:      s<=1, r<=1, active degree <=4, total <=5.
```

Thus `2s+r<=16`, `s<=8`, `s+y+r<=64`, and total degree `<=3757` all hold
with enormous room.  The Lean receipt includes a literal `rawShapeLegal`
envelope theorem, not just the weighted-X comparison.

The top data coefficients are not artifacts of a loose degree bound.  On
the extremal branch `N=X^n-1`, `U=X^(n-1)`, the leading coefficients of the
data-only parts of `C1,C2` are respectively `-1,-2`.  They survive in the
target characteristic.

## 4. Semigroup audit after rung six

Give `J,C1,C2` contact weights `1,2,3`.  A monomial

```text
J^a C1^b C2^c,   a+2b+3c=t,
```

has an extremal data-only branch of exact degree

```text
a(n-1)+b(2n-2)+c(3n-3)=t(n-1).
```

After the necessary `H^(44-t)` factor, its degree is

```text
rungX(t)=(44-t)g+t(n-1)=44g+t(e-1).
```

At `t=6`, this is the green 8428552 above.  At `t=7`, every individual
semigroup monomial has

```text
rungX(7)=8510282=D+30871.
```

This includes all eight order-seven profiles and, in particular, the
suggested packet

```text
J^5 C1, J^4 C2, J^3 C1^2, J^2 C1 C2.
```

The standard rank-four choice

```text
J^7, J^5 C1, J^4 C2, ZJ^7
```

still has boundary pivot product `-14*N^3*J^22`, so the leading gradients
do **not** collapse.  Every individual source is simply too wide.  The Lean
theorem proves the same strict failure for every `7<=t<=44`.

There is one honest caveat.  Carefully chosen linear combinations of
same-order semigroup monomials can cancel finitely many leading
coefficients (for example the standard transvectant syzygy begins with
`J*C2-2*C1^2`).  The present receipt does not prove that every such
data-dependent combination is impossible.  A cancellation would have to
remove at least 30,872 consecutive top X coefficients at rung seven while
retaining four boundary gradients.  The elementary transvectant identities
save only derivative-scale degrees, but a full Popov/syzygy lower bound is a
separate obligation.  Therefore the exact classification is:

- **GREEN:** literal global contact, source caps, and rank four at rung six;
- **RED:** every individual `J,C1,C2` semigroup monomial from rung seven on;
- **OPEN:** a large, boundary-rank-preserving cancellation among many
  order-seven covariants.

## 5. Split-locator comparison

The cheaper-looking error-locator shape `Q*J` raises error order while
preserving one agreement order, but it does not beat the osculant packet:

```text
39g+5(n-1)+e=8428553,
```

one degree worse than the new rung.  Adding the old boundary multipliers
misses by 80213 (`Y`), 80212 (`R`), or 80211 (`S`).  Thus the improvement is
specifically the use of the internal raw `R/S` gradients, not merely writing
the full locator as `H*Q`.

## Replay and trust

```bash
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/\
K0AllNodeWeightedOsculantRungSix6900.lean
```

The replay is under five seconds with the capped runner.  Printed axioms are
only `propext`, `Classical.choice`, and `Quot.sound`.  There is no `sorry`,
`admit`, `decide`, `native_decide`, explicit axiom, or unsafe declaration.

