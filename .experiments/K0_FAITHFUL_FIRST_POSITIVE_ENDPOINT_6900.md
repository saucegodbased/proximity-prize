# Faithful target-ratio first-positive endpoint gate

## Verdict

**GREEN finite mechanism gate for the direct full-kernel endpoint.**  In the
small exact chamber satisfying all three target parameter relations and the
target error/agreement inequalities, the complete contact kernel acquires
boundary rank four at exactly the first passive cap with positive global
dimension margin.

This simultaneously rejects a process mistake: complete-face strictness is
not needed.  At `L=U` every one of the 62 associated top-kernel directions is
obstructed, but the complete source at the first positive cap nevertheless
has four-dimensional boundary image.

This is one exact finite profile, not a target theorem.

## Faithful chamber and receipt

The profile over `F_101` is

```text
(n,w,g,e,m,B,s,U) = (16,7,11,5,5,2,1,8).
```

It has all of the structural relations used at the target:

```text
m = 3B-1,       2s = B,       U = 4B,
2e < g < e+w,  2g-w < n.
```

Take nodes `0,...,15`, agreements `A={0,...,10}`, and errors
`E={11,...,15}`.  Let

```text
Xi_E(X) = product_{a in E} (X-a),
Q(X)    = Xi_E(X)^2.
```

Thus `deg Q=10` and `w < 10 < g`, so the agreement direction is genuinely
retained-bad.  The candidate has degree exactly `w=7`.  On agreements set
`u1=Q`; at every error node use a deterministic value different from `Q`, so
the received direction is genuinely nonmatched off the agreement set.  With
`gamma=0`, set `u0=P` on agreements and a deterministic nonzero error away
from them.  The script checks that the actual agreement set is exactly `A`
and that interpolation of agreement `u1` values recovers `Q`.

Contact is the literal formal substitution

```text
X = x + eps,
Y = u0 + u1 Z + eps R - eps^2 S + eps^3 T  (mod eps^5).
```

Boundary gradients are evaluated at `X=16` with the formal convention

```text
(Y,R,S,Z) = (P,P',Hasse_2(P),gamma),  Hasse_2(P)=P''/2.
```

## Exact endpoint ranks

| cap `L` | source margin | columns | contact rank | nullity | boundary image |
|---:|---:|---:|---:|---:|---:|
| 8 | -172 | 4,836 | 4,836 | 0 | 0 |
| 9 | -110 | 5,634 | 5,634 | 0 | 0 |
| **11** | **+14** | **7,230** | **7,216** | **14** | **4** |
| 12 | +76 | -- | -- | -- | 4 by source inclusion |
| 15 | +262 | -- | -- | -- | 4 by source inclusion |

Cap 11 is the first positive-margin cap.  The augmented contact-plus-boundary
rank there is 7,220, exactly four above contact rank 7,216.  Once the image is
all four-dimensional, later complete sources retain it by inclusion; the
reported caps 12 and 15 therefore need no additional matrix reduction.

At the misleading `L=8 -> 9` complete-face transition, the new face has 798
columns, associated top rank 736, top kernel dimension 62, and connecting
obstruction rank 62.  In other words, none of that associated kernel lifts at
that step.  This does **not** prevent later complete-kernel boundary rank four.

## Correct inference and next gate

The live invariant is now the complete source margin, not vanishing of every
face connecting obstruction.  The next useful scaled tests should ask whether

```text
first cap with (#source - n * localRankBound) > 0
```

already has four-dimensional formal boundary image in independent faithful
receipts.  A failure is a real endpoint counterexample; a nonzero face
obstruction alone is not.

The target has `L=3757 >> U=64` and positive complete-source margin, so this
control is directionally relevant.  It still supplies no uniform proof that
positive margin forces boundary rank four.

## Reproducibility

```bash
python3 .experiments/k0_eventual_passive_strictness_sweep_6900.py \
  --profile target_faithful_m5 --family locator_square --endpoint-only
```

- Canonical output SHA-256:
  `1f399f9dfd3cafd25c586eb473f3f8de86bc3bbc8d4020c217c8d0ea9b2e52ff`
- Script SHA-256:
  `13aba9202431f6c79e09727e61c32ad410a14706c598f215865301a8d852843a`
- Runtime: `188.454s`
- Peak RSS: `2,273,924 KiB`
- Per-process address-space cap: `4,200,000,000` bytes

The experiment uses exact finite-field ranks throughout.  No sampled floating
point ranks, boundary oracle, or compressed second-derivative convention is
used.
