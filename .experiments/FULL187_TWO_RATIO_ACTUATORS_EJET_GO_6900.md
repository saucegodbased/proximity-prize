# Full187 two-ratio pure-endpoint actuators: local first-jet GO

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, or claim file was changed.

## Result

There is an explicit source-legal pair which breaks the old rank-one
`V^60` error jet.  On the normalized error chart (`Z=1`), define

```text
V = 1 + E + T R + O(2),
A_b(q) = q L^(60-b) V^b (J2 - B Z),
```

where `B` is the literal pure-seed coefficient of `J2`.  The two actuators

```text
A_36(q36),   A_37(q37)
```

are each zero at the pure endpoint and every literal source term is strictly
legal even after charging `deg q_b <= e-1`.  Their minimum strict margins are
respectively `4220` and `21171` degrees.  The preceding `b=35` member is
red by `12731`, so the pair starts at the exact first legal two-ratio seam.

At every simple error, the two value/first-`E` columns have determinant
`L^47 d0^2`, a unit.  Thus degree-`<e` CRT multipliers can match the value
and first `E` jet of `F0=L^59 V` exactly.  The same determinant holds for
the value/first-`T R` matrix, with a separately selected CRT pair.

This is a real local GO under the requested criterion (an explicit pair and
value plus `E` match).  It is not a completed `C_E` correction: matching
both `E` and `T R` simultaneously, the remaining normal directions, and the
higher contact rows still require a larger relay.

## General `H=0` normal-shell jet matrix

Use the centered normal error coordinates

```text
V  = 1 + E + P + O(2),
J1 = a1 E + p1 P + O(2),
J2 = a2 E + p2 P + O(2),       P := T R.
```

For a general normal-shell row `M_(b,c,d)=V^b J1^c J2^d`, its
`(value,E,P)` jet is

| condition on `(c,d)` | value | `E` | `T R` |
|---|---:|---:|---:|
| `(0,0)` | `1` | `b` | `b` |
| `(1,0)` | `0` | `a1` | `p1` |
| `(0,1)` | `0` | `a2` | `p2` |
| `c+d >= 2` | `0` | `0` | `0` |

This is the requested general shell matrix.  It makes the prior binomial
ladder's rank-one defect transparent: its terms with positive explicit `H`
die at `H=0`, leaving only `V^60` and ratio `60`.

## The endpoint factor and two actuator ratios

Put the pure seed in literal fixed coordinates:

```text
V = -H^2 Z,
W = -2 H H' Z,
P = -(2(H')^2+2 H H'') Z,
J2 = L^2 P - 2 L L' W + (2(L')^2-L L'')V.
```

Direct expansion gives

```text
J2 = B Z,
B = -2 L^2(H')^2 - 2L^2HH'' + 4LL'HH'
    - 2(L')^2H^2 + LL''H^2.
```

So every `A_b(q)` vanishes identically at the pure endpoint.  At a simple
error, `B=-2L^2(H')^2` after setting `H=0`; it is a unit in the target's odd
characteristic.  Write the normalized error expansion

```text
J2-B = d0 + dE E + dP(T R) + O(2),
```

where `d0=-B` is a unit.  Then

```text
jet(A_b/q) = L^(60-b) (d0, b*d0+dE, b*d0+dP).
```

For `b=36,37`, the two value/`E` and value/`T R` matrices are

```text
        [ L^24 d0                 L^23 d0                 ]
E:      [ L^24(36d0+dE)          L^23(37d0+dE)           ]

        [ L^24 d0                 L^23 d0                 ]
T R:    [ L^24(36d0+dP)          L^23(37d0+dP)           ],
```

and both determinants are `L^47 d0^2`.  The two logarithmic first-jet
ratios differ by one, rather than being locked to 60.

For the `E` solve, prescribe at each error node

```text
q36 = (36d0+dE)L^35/d0^2,
q37 = -(35d0+dE)L^36/d0^2.
```

Then `A_36(q36)+A_37(q37)` has value and `E` coefficient both equal to
`L^59`, exactly the first two coefficients of `F0=L^59(1+E+...)`.  Since
there are `e` simple error nodes, CRT supplies unique representatives
`deg q36, deg q37 < e`.  Replacing `dE` by `dP` gives a separate value plus
`T R` solve.

## Literal source-strip audit

Use

```text
(m,g,e,w) = (60,180413,81731,131071),
deg q <= e-1 = 81730,
deg B <= 2(g+e-1) = 524286.
```

Expanding `J2` and then all binomial terms of `V^b` produces six literal
families:

```text
- B Z V^b,
  L^2 S V^b,
  L^2(2(H')^2+2HH'') Z V^b,
- 2LL' R V^b,
- 2LL'(2HH') Z V^b,
  (2(L')^2-LL'') V^(b+1),
```

all multiplied by `q L^(60-b)`.  For literal shape `Y^yR^rS^sZ^z`, the
strict X cutoff is

```text
60g - w y - (w-1)r - (w-2)s.
```

The smallest margin occurs at the fully seeded tail of the `BZ`, `P`, `W`,
or final `V` family and is exactly

```text
b(g-2e) - [2(g+e-1)+(e-1)] = 16951b - 606016.
```

Therefore

| `b` | minimum margin | status |
|---:|---:|---|
| 35 | `-12731` | red |
| 36 | `4220` | legal |
| 37 | `21171` | legal |

All expanded rows have active degree at most `b+1 <= 38`, passive degree at
most one, curvature at most one, and seed degree at most `b+1 <= 38`, so
the 82/21/10/2703 caps are also strict.

## Checked artifacts

`full187_two_ratio_actuators_6900.py` expands the pure identity with an
exact in-file commutative polynomial implementation and audits every literal
binomial source term.  `Full187TwoRatioActuators6900.lean` proves the pure
identity, both determinants, the explicit local `E` solve, and the exact
target arithmetic with standard axioms only.

Reproduce under the requested cap:

```text
python3 -m py_compile .experiments/full187_two_ratio_actuators_6900.py
prlimit --as=4294967296 --cpu=120 -- python3 -B \
  .experiments/full187_two_ratio_actuators_6900.py
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187TwoRatioActuators6900.lean
```
