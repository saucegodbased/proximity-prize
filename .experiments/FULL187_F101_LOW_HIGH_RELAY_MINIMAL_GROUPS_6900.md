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

There are 41 such groups. Four deterministic delta-deletion orders gave the
following one-group-deletion-minimal repairs:

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

The four minima share 26 groups: six boundary-zero seed groups and twenty
boundary-one groups. Their union contains 40 of all 41 groups. Therefore
this exact control decisively rejects a repair consisting of one or a few
isolated low groups. Even the smallest discovered inclusion-minimal relay
uses 80.5% of the low groups and 80.4% of the low columns.

## Interpretation after the independent dual audit

This breadth has a precise role. The independent forced-head receipt proves
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

It does **not** support another search for a tiny autonomous high-V packet or
a single low actuator. The target-scale proof should seek a closed
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

The compact run used 404 exact rank tests and 190,588 KiB maximum RSS under a
4 GiB address-space cap. It is reproduced by

```text
prlimit --as=4294967296 python3 \
  .experiments/f101_full187_low_high_relay_minimizer_6900.py --compact
```

Receipts:

```text
script sha256
  eeccafb326283712ad35ed92f1e4e98be954d17404f7f7405ef61951a666981e
compact canonical payload sha256
  f88ea74d069982b8d53486a97adb75a347f5b620d6d4ee8a5a1da75aaabb354d
```
