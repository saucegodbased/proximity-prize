# Full187 F101 low/high relay minimization

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Exact finite verdict

In the faithful primary F101 control

```text
(n,w,A,m,D,s,t,J,L) = (11,5,8,4,32,1,1,6,10),
Q = Xi_E^2,
```

the source was split at boundary degree `d=Y+R+S=2`. The 1,515 high
columns are independent and leave the three honest locator RHS with exact
joint quotient defect three. Adding all 1,192 omitted `d=0,1` columns gives
rank 2,572 and kills the joint defect.

The low columns were grouped before minimization by

```text
(boundary degree, passive-seed exponent, R exponent, S exponent).
```

There are 41 such groups. Four deterministic delta-deletion orders starting
from all 41 groups gave the following one-group-deletion-minimal repairs:

| deletion order | retained groups | retained columns | total rank |
|---|---:|---:|---:|
| lexicographic | 34 | 986 | 2501 |
| reverse lexicographic | 34 | 985 | 2500 |
| small groups first | 33 | 958 | 2472 |
| large groups first | 34 | 985 | 2500 |

Every listed repair has joint defect zero. Deleting any one of its retained
groups restores positive defect; in each ordering, 31 or 32 deletions restore
the full defect three and the remaining one to three deletions restore defect
one or two.

Those four runs are **not** cardinality minima: deletion-locality depends on
the starting set.  As an explicit guard, the invariant grade-seven low shell
`boundary degree + passive seed <= 7` is already a feasible 29-group start.
Deleting from that start leaves a 27-group, 784-column feasible set of rank
2,292.  Each of its 27 one-group deletions is infeasible (joint-defect
histogram `1:2, 2:6, 3:19`).  Thus the earlier 33-group result is neither a
global lower bound nor the smallest feasible relay discovered.

The four full-start minima share 26 groups: six boundary-zero seed groups and
twenty boundary-one groups. Their union contains 40 of all 41 groups. These
intersection/union statistics describe only those four deletion paths. The
stronger honest observation is that both the full-start and structured-shell
starts reduce to broad inclusion-minimal completions (27--34 groups), while
the separate forced-head computation proves coordinate-level necessities.
No global minimum over group subsets was computed.

## Interpretation after the independent dual audit

The observed breadth has a precise role. The independent forced-head receipt proves
that the `d=1,z=0` normal head is fixed coordinate-by-coordinate (69 union
positions for `F0,F1,F2`). Boundary-zero columns have no `J` coordinate and
cannot directly break the locator-normal obstruction. They become useful
only after the normal head is present, by cancelling its complete contact
residual. Thus the result points to a translation-stable seed recurrence:

```text
forced d=1,z=0 head
  -> broad d=1 positive-seed completion
  -> broad d=0 passive-seed residual relay
  -> high d>=2 closure.
```

It does **not** provide a theorem excluding every cleverly chosen tiny group
set. Together with the forced-head and high-only dual receipts, however, it
does not support another unguided search for a tiny autonomous high-V packet
or a single low actuator. The target-scale proof should seek a closed
generating-function / Hermite recurrence for the full seed ladder, with the
three prescribed heads retained, rather than extrapolate any particular
finite minimal set.

## Scope and process guard

This is exact finite evidence, not a target theorem. Group-minimality is not
column-minimality, and the four minima depend on deletion order. In
particular, neither the 26-group intersection nor the 40-group union may be
asserted necessary at the target. What is robust is the falsification of the
small-relay hypothesis in this faithful control and its agreement with the
separate coordinate-level forced-head theorem.

The corrected compact run used 458 distinct exact rank tests and 190,780 KiB
maximum RSS under a
4 GiB address-space cap. It is reproduced by

```text
prlimit --as=4294967296 python3 \
  .experiments/f101_full187_low_high_relay_minimizer_6900.py --compact
```

Receipts:

```text
script sha256
  eb4469ca7ebc98be2bd4caff6eb476ed6cecdddfe445fe16aaa9f25ea8598157
compact canonical payload sha256
  4908ffe0be646c31cf8c1d70e590bea465088b83062fad8b01cbdcbcad6d4aa0
```
