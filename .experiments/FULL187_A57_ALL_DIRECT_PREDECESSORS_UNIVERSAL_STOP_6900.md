# Full187 A57 complete direct-predecessor universal STOP

Date: 2026-09-14  
Scope: universal high-direction discriminator; experiments only  
Decision: **STRUCTURAL STOP for the complete direct `u0`-free predecessor
rescue**

## Executive result

The frozen-target A57 Hankel repair at `8b1b1fc` cannot be promoted to the
universal high-received-direction theorem, even after adding every further
legal direct physical predecessor.

The corrected compiled low/high split is

```text
natDegree(u1) <= 133119   versus   natDegree(u1) >= 133120,
```

from `LowReceivedDirectionScalarSplit1331196900.lean`, SHA256

```text
6852d3896d787c2cd9502aafe5ca69a9faecace833744ed8702cb768f7443501.
```

Use the exact legal hostile direction

```text
u1 = X^133120.
```

It has degree exactly 133120 and is nonzero at every nonzero NTT node.  For
this direction the sum of all 24 direct predecessor images is exactly the
coefficient prefix

```text
span{1,X,...,X^255162}.
```

It misses the complete suffix

```text
span{X^255163,...,X^262143},
```

of dimension

```text
262144 - 255163 = 6981.
```

In particular coefficient `X^255163` is a kernel-checked obstruction even
after enlarging every actual Hasse image to its whole allowed residual
window.

No coefficient-independent/full-node predecessor exists in this physical
family, and no already-present theorem confines the actual universal packet
RHS away from this suffix.

## Why this supersedes the stale hostile control

Commit `49afff4` correctly identified the universal-quantifier failure of the
frozen Hankel argument, but used `X^132103`, the boundary exposed by an older
endpoint cut.  The fully compiled scalar split raises the surviving branch to
degree 133120.  This receipt recomputes the complete predecessor map at that
actual boundary.  It does not retain any conclusion whose only hostile
witness is below the compiled branch.

The shift arithmetic changes materially because

```text
133120 = 262144/2 + 2048.
```

Thus the difference from 132103 accumulates with the frozen-`U` power; it is
not a one-time endpoint translation.

## Completeness of the physical census

The committed A57 scalar dual kills every A57/n38 raw coordinate except

```text
(contact f,r,s,q,target z)=(36,11,10,12,2625).
```

Any grouped physical source contribution to that quotient is a scalar times
this complete raw contact column.  To be `u0`-free, a source `Y^y` selecting
`h` frozen copies of `U` must satisfy

```text
y=f+h=36+h,
source z+h=2625.
```

Correction polynomials have `0<=y<60`, so this gives exactly

```text
h=0,...,23,
(y,r,s,q,z,A)=(36+h,11,10,12,2625-h,57+h).
```

There is no 25th correction polynomial.  The terminal `C` source is not an
additional `u0`-free source at this target `z`: its fixed terminal `z` and
`y` do not satisfy both displayed equations.

The source scalar is the nonzero field element

```text
binom(36+h,36).
```

The executable reconstructs the exact prefix selected before each source
kernel.  Writing `h=2k` or `h=2k+1`, the depth and residual dimensions are

```text
d_(2k)   = 12-k,    rho_(2k)   = 208036+2k,
d_(2k+1) = 12-k,    rho_(2k+1) =  76965+2k,
0<=k<=11.
```

Every `rho_h` is strictly below `N=262144`.  Hence none of the 24 physical
families supplies an arbitrary all-node coefficient or a constant-multiplier
unit channel by itself.

The exact 24-record census hash is

```text
073cdc3855beff6fd4d768344b1fcaae8b28f39fd7e04761ef817bace4442865.
```

## Exact Hasse normalization

Let `Omega=X^N-1` and let the free source variation after its preserved prefix
be

```text
delta P_h = Omega^d_h C_h,    deg C_h < rho_h.
```

For a coefficient monomial `C_h=X^j`, expand `Omega^d` and take Hasse order
12 at an NTT root `alpha`:

```text
X^12 H_12(Omega^d X^j)(alpha)
 = X^j(alpha) *
   sum_(ell=0)^d (-1)^(d-ell) binom(d,ell) binom(N*ell+j,12).
```

After division by the irrelevant common `N^12` unit, this is diagonal in the
coefficient monomial `X^j`.  The script evaluates all

```text
sum_h rho_h = 3420276
```

weights exactly modulo `p=2130706433`.  Every weight is nonzero.  Their packed
u64 SHA256 is

```text
df51951c7566457fd6d25d97c42ce46612db1b7851fe9d0975e12aee55b08077.
```

The nonvanishing proves that the interval union below is not merely an upper
bound: it is the exact image support/rank for the hostile monomial.

## Hostile monomial interval calculation

Multiplication by the `h` frozen copies of `u1=X^133120` shifts coefficient
support cyclically by

```text
h*133120 mod 262144.
```

No resulting interval wraps around `X^N-1`.  For `0<=k<=11` the exact
intervals are

```text
h=2k:   [4096k,        208035+4098k],
h=2k+1: [133120+4096k, 210084+4098k].
```

The last odd interval, `h=23`, ends at 255162.  Together the 24 intervals
form exactly one prefix:

```text
[0,255162].
```

Exact receipts:

```text
interval-record SHA256
  0c86fdc65b5b2e27a5150efbc74367a02911ffb630773460cf3c321d6a6d9b4e
image-support SHA256
  f11f0cf353961207be5353c6b11653a22a65ea47bac54c8174177553ec2da439
exact rank     255163
exact defect     6981
missing suffix 255163..262143
```

This tests an adversarial envelope stronger than the physical map: each
normalized Hasse channel is allowed to be an arbitrary polynomial throughout
its complete residual window.  Therefore a missing coefficient of the
envelope is necessarily missing from the actual source.

## Kernel-checked obstruction

`Full187A57AllDirectPredecessorsMonomialStop6900.lean` defines

```text
hostileShift(h)      = h*133120 mod 262144,
predecessorFringe(h) =
  if h even then 208036+h else 76964+h.
```

It proves by exact finite interval arithmetic that, for every `h<24`,

```text
hostileShift(h)+predecessorFringe(h) <= 255163.
```

Consequently, for arbitrary field polynomials `V_h` satisfying the physical
degree windows,

```text
coeff_255163(sum_(h:Fin 24) X^hostileShift(h) V_h) = 0.
```

It separately proves that `X^133120` has degree 133120 and evaluates nonzero
at every nonzero node.  The file compiles with no `sorry`; its axiom audit is

```text
[propext, Classical.choice, Quot.sound].
```

This Lean theorem needs only the enlarged-window containment.  Exact
attainment of all lower coefficients is independently certified by the
Python Hasse-weight replay.

## Compensation does not add a hidden direct direction

Preserving an earlier diagonal may require changing selected prefix jets on
other physical shapes.  Such a compensator can have arbitrary canonical
higher jets, but its A57 contribution is still a scalar raw contact column.
The committed normalized dual annihilates every physical shape other than
the unique `(f,r,s,q)=(36,11,10,12)` family enumerated above.  Adjusting
sections therefore cannot create a 25th direct quotient-visible multiplier.

Intermediate diagonal compensation can correlate or shrink the 24 displayed
images; it cannot enlarge the adversarial direct-sum envelope used for this
STOP.

## Actual universal packet RHS audit

I searched the existing A57 actual-residual factorization, the n38/q12
receipts, and the compiled universal high-direction endpoint interface.
There is no theorem asserting either

```text
coeff_255163(RHS)=0
```

or membership of the RHS in the displayed 255163-dimensional prefix.  The
universal endpoint hypotheses quantify arbitrary received rows, seeds,
agreement sets, and selected low-degree polynomials; they contain no Hankel,
support, or A57-quotient premise.

That does not prove that an RHS-confinement theorem is impossible.  It means
such confinement is a new mathematical obligation and cannot be inferred
from a frozen target instance or from the currently compiled caller.

Per the requested narrow audit, work stops here rather than inventing that
invariant.

## Honest scope and next strategic options

This result kills the **entire direct `u0`-free physical predecessor rescue**
as a universal-surjectivity route.  It does not prove the 6900 theorem false,
and it does not rule out:

1. a separate count/dichotomy for received directions whose A57 map is
   deficient;
2. a genuinely indirect source mechanism outside the dual-visible physical
   predecessor family;
3. a newly proved actual-packet RHS confinement theorem.

The frozen-target local GREEN at `8b1b1fc` remains an exact regression result
for that one target coefficient sequence, but it is not a theorem-facing
universal step.

## Replay

Python exact census/rank, under 3 GiB:

```bash
ulimit -v 3145728
python3 .experiments/full187_a57_all_direct_predecessors_universal_stop_6900.py
```

Lean kernel proof:

```bash
LEAN_NUM_THREADS=1 lake env lean \
  .experiments/Full187A57AllDirectPredecessorsMonomialStop6900.lean
```

Frozen receipt:

```text
Python canonical SHA256
  aa3575a29419928112c9d8a86e48375b2b3bb58071a686fa48b3f84061e09ed3
Python peak RSS
  <=70724 KiB across recorded replays
Python source SHA256
  a097ea850115a0c5d2c667ba9684a5832e9dc6ec551d8d99954afbce8748183f
Lean source SHA256
  7672e7b22a67a46cdd490d1c0be184d805660f62417e02c561e62c495ff96f70
```
