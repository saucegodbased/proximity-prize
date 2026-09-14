# q:t=2:1 safe first-shell connector RED

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, radius, and the accepted 6806 result are unchanged.

## Verdict

**RED for a one-shell `{pure,R,S}` connector once the derivative weights are
raised to `q:t=2:1`.**  In the smallest m6 geometry with a genuinely unsafe
strong-affine terminal slice, the entire first post-prefix shell is injective
modulo the prefix.  Consequently:

```text
every proper subset of {pure,R,S}   packet defects (1,1,1,1), joint 4
all three {pure,R,S} together       packet defects (1,1,1,1), joint 4
all other safe q=2 shapes included  packet defects (1,1,1,1), joint 4
unsafe slice restored as well       packet defects (1,1,1,1), joint 4
```

The failure happens before the seven-column deletion matters.  This is a
clean STOP for extrapolating the q=t=1 first-shell pattern directly to the
target derivative profile.  It does not stop a deeper passive-shell or
multi-grade connecting map; the actual target has `L-J=2621`.

This is finite structural evidence, not a Full187 theorem or a 6900
candidate.

## 1. Parameter selection and legality before rank

The chamber was fixed as

```text
F_101
(n,w,g,m,D,q,t,J,L) = (10,4,6,6,36,2,1,8,9)
n = 2w+2
J/m = 8/6 = 1.3333...       target 82/60 = 1.3666...
D = m*g
```

Multiplicity six was retained from the immediately preceding green connector
control, so this run changes the derivative profile and deletion rather than
conflating them with an m-change.  Within that m6 family, the geometry is
minimal for a nonvacuous strong deletion:

* `deg Q=g-1>w` requires `g>=w+2`;
* positive curvature weight requires `w-2>0`;
* at the only smaller geometry `w=3,n=8,g=5`, all five shapes are safe;
* `w=4,n=10,g=6` is the first geometry producing an unsafe shape.

Before computing any matrix rank, set

```text
H = {0,...,4}, G = {0,...,5}, E = {6,...,9}
q_H = 1+X
Q = q_H + Lambda_H.
```

Then `deg Q=deg(Q-q_H)=5=g-1>w=4`.  Agreement values are evaluations of
`Q`; only error values receive the fixed offsets `(3,5,7,11)`, giving
`(23,8,70,92)`.  All actual `U1` values are nonzero.

All exact packets `F0,F1,F2,F3` are source-legal, with support sizes

```text
57,82,109,54
```

and literal error-contact support sizes `96,95,107,95`; their agreement
contacts vanish identically.  The compact centered heads are also legal in
this finite chamber:

```text
(Y-QZ)^6 Z^3,
R (Y-QZ)^6 Z^2,
S (Y-QZ)^6 Z^2.
```

Thus the RED is not caused by an illegal packet or missing centered head.

## 2. Exact nonvacuous safe deletion

Using required error margin `n-g=4`, the strong corner calculation gives

```text
safe shapes     (0,0),(1,0),(2,0),(0,1)
unsafe shape    (1,1)
```

The unique unsafe local occurrence is

```text
(f,a_E,c_S)=(1,0,1).
```

Its exact capacity values are

```text
lower coefficient width                27
contact depth                           4
width - g*depth                          3
required arbitrary-error margin          4
shortfall                                1
```

On the first shell `y+r+s+z=L=9`, the unsafe terminal face is exactly

```text
(y,r,s,z)=(6,1,1,1),  X-degree 0,...,6.
```

It therefore deletes seven literal source columns.  Full/restricted source
sizes are `4891/4884`; this is a real deletion, not a vacuous safe audit.

## 3. Coefficientwise screen

The grade-at-most-`J=8` prefix has 4,140 columns and exact rank 4,140.  The
four packets have quotient rank four.  First-shell group sizes are

| shape `(r,s)` | columns |
|---|---:|
| `(0,0)` | 180 |
| `(1,0)` | 152 |
| `(0,1)` | 160 |
| `(2,0)` | 126 |
| `(1,1)` | 133 before deletion, 126 after deletion |

The script tests all eight subsets of candidate shapes
`{(0,0),(1,0),(0,1)}` in three predeclared backgrounds:

| background | background columns | background rank mod prefix | result for every candidate subset, including all three |
|---|---:|---:|---:|
| none | 0 | 0 | individual `(1,1,1,1)`, joint 4 |
| safe q=2 nuisance shapes `(2,0),(1,1)` after deletion | 252 | 252 | individual `(1,1,1,1)`, joint 4 |
| full nuisance shapes, unsafe seven restored | 259 | 259 | individual `(1,1,1,1)`, joint 4 |

For the isolated triple, its 492 columns have quotient rank 492.  With all
nuisance shapes and the unsafe slice restored, all 751 shell columns have
quotient rank 751.  Equivalently,

```text
rank(prefix + complete first shell) = 4140 + 751 = 4891.
```

There is no grade-nine contact cycle at all, so no grade-nine boundary
connector can exist.  The seven unsafe columns are themselves independent
modulo the safe source; restoring them cannot repair the packet.

## 4. Process consequence

The q=t=1 discovery remains exact in its scope: at m6 through m8, the raw
`pure/R/S` groups jointly close the packets in the tested chambers.  This
q:t=2:1 replay shows that the mechanism is not stable under the first increase
in derivative depth when only one post-prefix shell is exposed.

Do not run another parameter grid.  The next mathematically distinct gate
must expose a second passive shell or construct the actual multi-grade
mapping cone.  Its first acceptance criterion is that some source relation
survives the connecting map; a one-shell proof is impossible in the present
control because the relevant map has zero domain.

## 5. Reproduction

```text
prlimit --as=3221225472 --cpu=900 -- \
  python3 -B \
  .experiments/f101_m6_q2t1_safe_first_shell_gate_6900.py
```

Recorded optimized run:

```text
elapsed        232.083027 seconds
peak RSS       440,104 KiB
canonical SHA  429020c2c42bbae5929ea9c94dbc95a4a3c1c02ceaf00a236586712297214eeb
script SHA     a07024fe0b1fc5b83ede7245cb1c1dc35c8e0290cfae6e6dc925aa19c5d23839
```

The first implementation redundantly rebuilt a shell echelon once per target
and was stopped before completion.  The recorded run uses one exact source
echelon per subset and reduces all four targets through it, cutting the screen
by roughly fivefold without changing the mathematics.  No `decide`,
`native_decide`, production, or submission artifact is involved.
