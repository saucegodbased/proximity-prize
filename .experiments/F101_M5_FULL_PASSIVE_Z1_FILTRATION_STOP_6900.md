# m5 complete passive filtration: coefficientwise Z1 STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, `score.txt`, `radius.txt`, and the accepted 6806 result are
unchanged.

## Verdict

Descending farther through the passive-seed tower does **not** rescue Z1 in
the exact faithful m5 control. Grade 8 makes all three prescribed locator
RHS reachable, but constant Z1 remains defect one at grades 8, 9, 10, and 11,
where 11 is the last legal combined grade. Each of grades 9--11 adds exactly
75 complete-contact kernel dimensions and exactly zero coefficientwise
boundary rank.

This is a decisive finite STOP for the suggestion that the previously
untested passive grades automatically turn the m5 localized rank-four result
into filtered Z1. It is not a target counterexample: a target-only coupling
among the active/derivative safe-105 shapes could still create Z1.

## Exact gate

The frozen control is

```text
F_101,
(N,w,g,m,D,s,t,J,L)=(10,4,7,5,35,1,1,7,11),
error-direction offsets=(3,5,7).
```

For every centered total-grade prefix from 7 through 11, the script builds
the complete literal contact matrix, row-reduces its transpose, and retains
every legal coefficient position in Y/R/S/Z. It tests the three locator
columns and pure constant Z directly over `F_101`. No polynomial is inverted,
no `F_101(X)` containment is used, and no ambient kernel/cokernel basis is
materialized.

| max grade | source prefix/terminal/full | contact rank/nullity | individual F0/F1/F2 defects | joint RHS defect | boundary rows/image rank | Z1 defect |
|---:|---:|---:|---:|---:|---:|---:|
| 7 | 1841/455/2296 | 2296/0 | 1/1/1 | 3 | 131/0 | 1 |
| 8 | 2296/455/2751 | 2680/71 | 0/0/0 | 0 | 131/12 | 1 |
| 9 | 2751/455/3206 | 3060/146 | 0/0/0 | 0 | 131/12 | 1 |
| 10 | 3206/455/3661 | 3440/221 | 0/0/0 | 0 | 131/12 | 1 |
| 11 | 3661/455/4116 | 3820/296 | 0/0/0 | 0 | 131/12 | 1 |

After the grade-8 birth, nullity increments are `(75,75,75)`, while boundary
image-rank increments are `(0,0,0)`. Thus the full extra passive depth adds
225 kernel directions, none of which supplies the missing coefficientwise
constant-Z class.

The distinction from the earlier localization is essential. At grade 8 the
packed four-polynomial image has rank four over `F_101(X)`, yet the legal
coefficientwise Y/R/S/Z image has rank 12 and excludes pure Z1. Grades 9--11
show that the missing polynomial multiplier cannot be recovered merely by
waiting for more passive degree within this source.

## Structural interpretation and target scope

Multiplication by the centered passive variable naturally propagates many
high-grade contact cycles without creating a new first-order boundary at the
center. The repeated 75-dimensional increments are consistent with exactly
that passive tower. The calculation itself establishes only the rank facts
above; it does not elevate this interpretation to a universal theorem.

For Full187, the live target question is therefore sharper:

```text
Can the safe 105 active-grade-82 derivative shapes, together with their
legal lower active/positive-passive connecting corrections, create a
zero-YRS row with constant Z=1?
```

Evidence from m5 says that passive depth after the first successful
THREE-RHS shell is not enough. A target proof must use an active/derivative
coupling that is absent in this `(s,t)=(1,1)` control, or prove a genuinely
target-specific coefficient-window effect. Fraction-field rank and raw
kernel surplus are both invalid substitutes.

## Reproduction

```text
prlimit --as=4294967296 --rss=4294967296 -- \
  python3 -B \
  .experiments/f101_m5_full_passive_z1_filtration_stop_6900.py
```

The exact run took 50.66 seconds and peaked at 761,628 KiB RSS under the
explicit 4 GiB address-space/RSS cap.

```text
canonical payload SHA-256
  a30caac11bab076049213b0b3e9e05888cf4f221d9542abd355d7ffc83b05150

script SHA-256
  e245351a7a2a053b4289d1dc14bd9a19d6a1b10413ee269e819afea194974c87
```

Final decision:

```text
STOP  infer filtered Z1 from the localized four-rank;
STOP  hope that grades 9--11 rescue Z1 by passive depth alone;
GO    test exact active/derivative safe-corner coupling, coefficientwise.
```
