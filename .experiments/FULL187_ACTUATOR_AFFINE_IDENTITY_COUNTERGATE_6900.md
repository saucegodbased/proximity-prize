# Full187 pure-endpoint actuator: affine-identity correction

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, or claim file was changed.

## Correction

The earlier two-ratio actuator receipt is **retracted**. Its premise

```text
J2 - BZ = d0 + dE E + dP(TR) + ...,
d0 = -B a unit,
```

is false in the literal shifted coordinates. Direct substitution gives the
exact identity

```text
J2 - BZ = (2(L')^2 - L L'')Y - 2 L L' R + L^2 S.     (AFFINE)
```

There is no scalar `d0=-B`: the pure `B Z` term cancels completely. Thus the
claimed value/E and value/TR determinant `L^47 d0^2`, and the inferred
`A36,A37` GO, do not apply.

## Independent literal derivation

Put

```text
V = Y-H^2Z,
W = R-2HH'Z,
P = S-(2(H')^2+2HH'')Z,
J2 = L^2P - 2LL'W + (2(L')^2-LL'')V,
B = -2L^2(H')^2 - 2L^2HH'' + 4LL'HH'
    -2(L')^2H^2 + LL''H^2.
```

Expanding `J2-BZ` cancels every `Z` term and leaves (AFFINE). This was
checked in an exact commutative polynomial implementation and formally by
ring normalization.

## Corrected local actuator jet

For

```text
A_b(q)=q L^(60-b)V^b(J2-BZ),
c=2(L')^2-LL'',
```

restrict the error base to `H=0, Y=1+E, R=S=0`. Then

```text
A_b / (q L^(60-b)) = c(1+E)^(b+1).
```

So the actual `E` two-jets of the nominal actuators are

| row | value | `E` | `E^2` | `S` coefficient at base |
|---|---:|---:|---:|---:|
| `A36` | `c` | `37c` | `666c` | `L^2` |
| `A37` | `c` | `38c` | `703c` | `L^2` |

They are not the earlier `d0,36d0,630d0` and
`d0,37d0,666d0` rows. In particular, `c` has not been established as a unit
at every error.

## Exact value/S countergate

For a finite actuator packet, let `A` be the sum of its normalized
amplitudes at the error base. By (AFFINE), its value and `S` boundary
coefficient are exactly

```text
value = A c,
S      = A L^2.
```

Matching a nonzero `F0` value requires `A c=L^59`; zero `S` boundary requires
`A L^2=0`. At an error `L` is a unit, so the latter forces `A=0`, contradicting
the former. Therefore this pure-endpoint actuator sector cannot itself
realize any nonzero `F0` value while preserving the required zero `S` jet.

The ratio-59/60 relay has no `S` component, so it cannot cancel this actuator
boundary coefficient. Hence an integration that asks this actuator sector to
furnish a nonzero `F0` value is impossible. This does not claim a global
no-go for every possible low-relay recurrence; it precisely removes the
incorrect actuator premise.

## Checked artifacts

`full187_actuator_affine_identity_countergate_6900.py` verifies (AFFINE) in
an exact polynomial ring and emits the corrected jets. The Lean receipt
proves (AFFINE), its actuator substitution, and the field-generic
value/nonzero-`S` contradiction without `sorry`.

```text
python3 -m py_compile .experiments/full187_actuator_affine_identity_countergate_6900.py
prlimit --as=4294967296 --cpu=120 -- python3 -B \
  .experiments/full187_actuator_affine_identity_countergate_6900.py
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187ActuatorAffineIdentityCountergate6900.lean
```
