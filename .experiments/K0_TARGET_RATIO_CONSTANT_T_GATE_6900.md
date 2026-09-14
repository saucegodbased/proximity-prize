# k=0 target-ratio constant-T complete-source gate

Date: 2026-09-14 UTC. Scope: lower 6900 only. This is a bounded exact
falsifier/mechanism receipt, not target transport, a candidate, or a
submission change.

## Result

The earlier two-error controls used active caps somewhat richer than the
target m47 ratios. The new deterministic chambers retain the exact target
shape relations at the first nontrivial scale:

```text
target:  m=47, B=16, s=8, U=64;  m=3B-1, s=B/2, U=4B
exact:   m=5,  B=2,  s=1, U=8;   m=3B-1, s=B/2, U=4B
ceiling: m=6,  B=2,  s=1, U=8.
```

Both use `(n,w,g,L)=(11,5,8,8)` over `F_101`, candidate polynomial and seed
zero, and

```text
Q=C(X,6)=prod_(i=0)^5 (X-i)/6!.
```

Thus `deg Q=w+1`, every size-`w+1` anchor has a constant nonzero Newton
quotient, and all three error nodes have the same nonzero value residual
`delta=1` and direction mismatch `epsilon=3`. This is the adversarial family
which collapses every scalar anchor packet.

The literal complete-source matrices give:

| chamber | columns | contact rank | nullity | published margin | boundary rank |
|---|---:|---:|---:|---:|---:|
| exact m5 | 3,604 | 3,418 | 186 | +161 | 4 |
| ceiling m6 | 4,764 | 4,635 | 129 | +45 | 4 |

At each of the three checked boundary values `X=11,12,13`, the complete
kernel has gradient rank four. The true high-degree tangent pairs nontrivially
with 182 of the 186 m5 kernel rows and 128 of the 129 m6 rows. Hence the
constant-T/equal-ratio adversary which kills the scalar packet does **not**
produce a complete-source rank defect after matching the target `B/s/U`
ratios.

## What this resolves and what it does not

This is useful positive evidence because a prior complete-source negative
control used much richer derivative caps and could not distinguish an
intrinsic failure from a profile-ratio failure. Here both source-dimension
gates are positive and the exact target shape relation survives.

It is still finite evidence. It does not prove that the target m47 contact
dual is zero, does not identify a uniform minor, and does not justify
extrapolating ranks. The contact ranks differ from the published sum-of-local
caps, so a fixed-pivot argument remains invalid. The exact remaining theorem
is still the rank-adaptive full-source dual recurrence.

## Reproduction

```text
prlimit --as=6442450944 --cpu=900 \
  python3 -B .experiments/k0_target_ratio_constant_t_gate_6900.py
```

The run took 58.0 seconds with peak RSS 962,360 KiB. Receipt hashes:

```text
canonical SHA-256  9ef1d556c2bd8b3389f1528117966c2fcf43d52473a759d8c00dfa8de30a3429
script SHA-256     983b84b1af38028b99da9515f18217e5e94cd08576c5aa8a684dfa305ea45383
```

