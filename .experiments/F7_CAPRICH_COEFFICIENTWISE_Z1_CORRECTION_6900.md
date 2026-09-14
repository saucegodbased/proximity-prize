# Cap-rich F7: exact F3 is green while naive Z targets are red

Date: 2026-09-14 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or accepted-6806 artifact was changed.

## Verdict

The coefficientwise fourth target must be the source-legal partial-locator
packet `F3`, not pure constant Z and not a bare agreement-locator times Z.
This distinction completely resolves the apparent contradiction in the
small cap-rich control:

```text
pure constant Z                              defect 1
(Lambda_G/Lambda_G(0))*Z                     defect 1
exact F0,F1,F2,F3 packets jointly            defect 0
```

The last result is checked in the nonzero domain `F_7^*`, matching the
structural fact that the actual multiplicative NTT domain excludes zero.
All four packets are source-legal, have zero complete agreement contact, and
their nonzero error syndromes have simultaneous coefficientwise corrections
in the complete contact kernel.

This is a positive finite control for treating `C_E(F3)` as the fourth RHS.
It is not a target theorem and does not show that the target safe-105
terminal subsource performs that correction.

## Exact shifted control

Use

```text
field F_7,
domain=(1,2,3,4,5,6),
G=(1,2,3,4),
H=(1,2,3),
(N,w,g,m,D,s,t,J,L)=(6,2,4,3,12,2,1,5,5),
u0=0 on G and 1 off G,
u1=Lambda_H.
```

The full source has 617 columns, contact rank/nullity `545/72`, and a
9-dimensional coefficient boundary image. Let `q_H` be the degree-at-most-w
interpolant of `u1` on H. Here `q_H=0`. Put

```text
B  = Lambda_H^(m-1) * Lambda_(G\H)^m
   = Lambda_H^2 * Lambda_(G\H)^3,
F3 = B*(Y-Z*q_H) = B*Y.
```

Together with the standard centered `F0,F1,F2`, the exact results are

```text
individual coefficientwise defects (F0,F1,F2,F3) = (0,0,0,0),
joint coefficientwise defect                      = 0,
joint direct stacked-system defect                = 0,
agreement contact supports                        = all zero,
error contact support sizes                        = (14,14,18,16).
```

The direct stacked-system calculation independently solves all contact and
boundary equations at once, so the result is not inferred from a generated
kernel orientation.

## Why the naive Z audit was misleading

In the original zero-containing toy domain, the older polynomial-boundary
calculation reported localized ranks `YRS/full=3/4`. A strict coefficient
audit instead gives boundary/YRS ranks `9/9`; pure constant Z remains defect
one. The same pure-Z defect survives affine translation to the nonzero
domain, and even the normalized polynomial

```text
(Lambda_G/Lambda_G(0))*Z
```

has defect one. These facts do not contradict the four-packet GREEN.

The fourth normal is relative to the first locator packet. Its determinant
uses

```text
U1-q_H = Lambda_H*T,
```

and its error correction is an atomic packet equation. Replacing it by a
standalone Z polynomial discards the Y component and the exact multiplicity
profile `Lambda_H^(m-1)*Lambda_(G\H)^m`. That replacement asks a different,
strictly stronger question.

For reference, the original zero-containing grade filtration is:

| max grade | contact rank/nullity | coefficient boundary/YRS rank | pure Z defect | localized YRS/full rank |
|---:|---:|---:|---:|---:|
| 1 | 57/0 | 0/0 | 1 | 0/0 |
| 2 | 150/0 | 0/0 | 1 | 0/0 |
| 3 | 275/6 | 4/4 | 1 | 3/3 |
| 4 | 412/28 | 9/9 | 1 | 3/4 |
| 5 | 545/72 | 9/9 | 1 | 3/4 |

This table remains a valid STOP for interpreting localized rank four as a
pure coefficient-Z lift. It is not a STOP for the correct F3 fourth RHS.

## Target consequence

The safe-105 target gate should now be stated as four error-syndrome
containments:

```text
C_E(Fi) belongs to C_E(W),  i=0,1,2,3,
```

where W is the literal agreement-contact kernel with zero four-packet
boundary correction. Equivalently, seek complete-kernel representatives of
the four exact packet boundaries. Do not seed the transition with pure
constant Z. The small control shows this correction can exist even when every
standalone naive Z test is red.

## Reproduction

```text
prlimit --as=4294967296 --rss=4294967296 -- \
  python3 -B .experiments/f7_caprich_coefficientwise_z1_filtration_6900.py
```

Final run: 3.89 seconds, peak 60,016 KiB RSS.

```text
canonical payload SHA-256
  ae526c686ef2c131115360cb90c9e4dcd654e33cc4f3093f166d142eeaff7254

script SHA-256
  6d8d587e779eaad6ba3155531dcec8fda58d36c489a0361cdcd3f54944830d81
```

Decision:

```text
STOP  pure constant Z or bare Lambda_G*Z as the fourth target;
STOP  localized rank four as a coefficientwise proof;
GO    exact F3 as the fourth RHS in the safe-105 target recurrence.
```
