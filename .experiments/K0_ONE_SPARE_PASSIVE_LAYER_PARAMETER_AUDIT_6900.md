# k0 one-spare-passive-layer parameter audit

Date: 2026-09-15 UTC. Scope: lower 6900, exact arithmetic and existing generic
source/consumer interfaces. No production candidate, score, or claim changes.

## Verdict

**GREEN as a fully affordable parameter move; OPEN as a source theorem.**

Use the conservative profile

```text
(m,B,s,U,L,k,n0) = (47,16,8,64,3758,0,1).
```

This is one passive layer above the first-positive `L=3757` profile. It is
preferable to jumping immediately to the consumer endpoint `L=7595`: it gives
the exact structural feature now under test--a legal passive successor for
every old source monomial--while leaving enormous consumer slack.

## Exact GREEN gates

The literal source/rank formulas give

```text
source columns                         65,079,223,811,319
262144 * one-node relaxed rank         65,079,198,351,360
source surplus                                 25,459,959
surplus gained over L=3757                     23,088,879
```

The existing 52-chart consumer is generic in `(J,L)`. At `(64,3758)`:

```text
active ordinary projection cap            139,321,344
inactive-shear projection cap              141,680,640
field characteristic                     2,130,706,433
one-stratum 52-chart cost               1,546,678,960,128
all 81,732 strata cost            126,413,164,769,181,696
MCA allowance                     254,684,620,614,660,120
remaining consumer slack          128,271,455,845,478,424
```

The inactive chart's only passive-cap change is the already-formalized shear
`L -> L+J`; its projection cap is the second number above. The terminal X
width remains `90,867 > 81,731` errors because it is independent of `L`. The
cutoff/active-cap premise is also independent of `L`.

The full exact-strata consumer theorem therefore has no numeric,
characteristic, or support-ledger objection to `L=3758`. The arithmetic is
kernel checked in `SecondJetK0OneSpareLayerArithmetic6900.lean` using only
`norm_num`; it contains no `decide` or `native_decide`.

## What the move actually buys

For every raw shape legal at cap 3757, multiplication by the passive variable
is legal at cap 3758. In particular, the formerly terminal target analogue

```text
X^2 Y^48 Z^3709
```

now has the legal successor `X^2 Y^48 Z^3710`. This removes the literal
terminal-face taper from a one-step passive recurrence.

It does **not** prove the recurrence. Contact after multiplying by the global
passive variable is multiplication by the local passive variable, and that
new contact trace need not lie in the old contact image. Moreover, shifting
an old contact-kernel vector cannot create the new normal: the exact-G
root-count theorem makes its value trace zero, so its shifted boundary stays
inside the old normal range.

The remaining theorem is still the relative repair:

```text
d in Source(3758), p in Source(3757),
contact(d) = contact(p),
residual(boundary(d) - boundary(p)) != 0.
```

Equivalently, the connecting map from the liftable part of the new passive
face to `Boundary / oldNormal` must have rank one. Small exact controls now
show that the strongest known knife-edge defect is repaired by one passive
layer, but that is finite evidence rather than the uniform target theorem.

## Process decision

Continue on `L=3758`, not `L=7595`, until the relative rank-one statement is
proved or falsified. A counterexample at one-spare depth is a fast STOP and
would justify testing more layers. A GREEN theorem at one-spare depth gives
the cheapest, highest-slack production profile and minimizes verifier risk.
