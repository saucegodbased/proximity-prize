# Full187 low relay: complete intrinsic order-2/3 jet gate

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Local coordinate and the two-block failure

The literal local value coordinate is exactly

```text
V = 1 + E + T R - T^2 S/2.
```

Here `T` is horizontal contact order one, `E` has contact weight three, and
`R,S` are the two passive normal coordinates.  Up to contact weight three,
the normalized target `F0=L^59 V` has, after suppressing the scalar Taylor
series of `L^59`, the intrinsic normal vector

| term | `1` | `E` | `T R` | `T^2 S` | `T^2 R^2` | `T^3 R S` | `T^3 R^3` |
|---|---:|---:|---:|---:|---:|---:|---:|
| target `V` | 1 | 1 | 1 | `-1/2` | 0 | 0 | 0 |

For a reduced relay class `A_n V^n`, the corresponding row is

```text
(1, n, n, -n/2, C(n,2), -C(n,2), C(n,3)) A_n.       (1)
```

The original two blocks are

```text
R60 = q60 (U V^60 - H^3 Z V^58 J1),
R59 = q59 L (U V^59 - H^3 Z V^57 J1).
```

At each error, set `q60 U=-58f`, `q59 L U=59f`.  This gives the already
reported value/first-jet solve, but (1) gives the exact obstruction

```text
-58 C(60,2) + 59 C(59,2) = -1711.
```

Thus the two-block relay has an unavoidable `-1711 f T^2 R^2` term.  The
target characteristic is `2130706433`, so `1711=29*59` is nonzero.  Scalar
CRT derivatives and the `H^3 J1` tail cannot change `T^2R^2`: the former
first enter that monomial one horizontal order later and the latter starts
in horizontal order three.  Therefore the first-jet GO does **not** extend
to complete order two with only its two actuators.

## Smallest legal binomial extension: degree 58

For every `n` define the staggered two-row block

```text
Rn = qn L^(60-n) (U V^n - H^3 Z V^(n-2) J1).        (2)
```

It has exact pure-seed cancellation for

```text
V=-H^2Z, J1=HUZ.
```

The next source-legal block is `R58`.  With effective error amplitudes in
the order `(V^60,V^59,V^58)`,

```text
(1653, -3363, 1711),
```

the binomial moments are

```text
sum A_n = 1,
sum n A_n = 1,
sum C(n,2) A_n = 0,
sum C(n,3) A_n = 32509.
```

So the 6-row packet `1653 R60 - 3363 R59 + 1711 R58` matches the complete
intrinsic `V` sector through order two, including `E`, `TR`, `T^2S`, and
`T^2R^2`.  It fails at order three by the exact residual

```text
32509 f T^3 R^3.
```

## Order three: degree 57 is legal and sufficient in the V sector

Add the final source-legal staggered block `R57`.  The four amplitudes in
degree order `(60,59,58,57)` are

```text
(-30856, 94164, -95816, 32509).
```

They are Lagrange evaluation weights at `n=1`, so their moments against
`C(n,k)` for `k=0,1,2,3` are exactly

```text
(1, 1, 0, 0).
```

Consequently their reduction agrees with `V` through contact weight three:
it matches all seven displayed components, not merely the `E` and `TR`
ones.  This is an exact intrinsic **order-three V-sector GO**.

## Literal strips and exact endpoint cutoff

All rows in (2) use degree-`<e` CRT multipliers.  Their lead/shifted row
coefficient degrees, windows, and margins are:

| `n` | lead degree / window | shifted degree / window | common margin |
|---:|---|---|---:|
| 60 | `343873 / 1017060` | `326923 / 1000110` | 673187 |
| 59 | `524286 / 1000109` | `507336 / 983159` | 475823 |
| 58 | `704699 / 983158` | `687749 / 966208` | 278459 |
| 57 | `885112 / 966207` | `868162 / 949257` | 81095 |
| 56 | `1065525 / 949256` | `1048575 / 932306` | **-116269** |

Thus `R57` is the last legal member of this specific lower-normal binomial
ladder; a fifth `R56` actuator is source-red before any contact condition is
used.  The 8-row `R60,R59,R58,R57` packet is therefore the smallest legal
extension of this family which clears the intrinsic cubic `V` jet.

## J1/J2 and the first remaining condition

The displayed vector is the complete contribution which is determined solely
by the `H=0` reductions.  It includes the literal `TS` term from the value
coordinate.  The subtracted part of each block,

```text
H^3 Z V^(n-2) J1,
```

begins at horizontal order three.  It can alter only the remaining
longitudinal `T^3`/`T^3R` columns at this order; it cannot repair the
`T^2R^2`, `T^3RS`, or `T^3R^3` moment defects above.  No `J2/S` row is
needed for the V-sector result, and the earlier three-row same-stratum
`J2` checkerboard remains zero through first normal order.

More explicitly, write `h=H'(x)`, use `Z=1` in the affine error chart, and
write the order-zero part of `J1=L W-L'V` as `-L'+L R`.  If
`a_n=q_n(x)L(x)^(60-n)`, then the complete weight-three tail is

```text
-a_n h^3 T^3(-L' + L R)
= a_n h^3 L' T^3 - a_n h^3 L T^3 R.                 (3)
```

It contains neither `R^2`, `RS`, nor `R^3`; this is why the two- and
three-block obstructions above are exact even before resolving (3).  Since
`U=-2LH'` and the value equations give `sum A_n=f`, the aggregate of (3) is
fixed by `f` up to the scalar Taylor conventions.  It is precisely the
remaining `T^3,T^3R` Hermite compatibility described next.

The **first unproved condition** is now precise: after the CRT values

```text
qn(x) L(x)^(60-n) U(x) = A_n L(x)^59,  x in E,
```

have fixed the unique representatives `deg qn<e`, their `T`-Hasse
derivatives must satisfy the longitudinal second- and third-order equations
simultaneously with the actual `H^3 Z J1` tails.  CRT values alone provide
no independent derivative control.  This is a Hermite compatibility problem
for the four fixed representatives, not another binomial-ratio condition.

Nothing here proves those equations, the full `C_E` contact correction, F1
or F2, or the independent Z direction.

## Checked artifacts

`full187_low_relay_higher_jet_gate_6900.py` expands (1) in the literal
`V=1+E+TR-T^2S/2` chart through contact weight three and checks each endpoint
and strict strip exactly.  `Full187LowRelayHigherJetGate6900.lean` checks
the endpoint identities, all moment arithmetic, and the exact `n=56` red
cutoff.

```text
python3 -m py_compile .experiments/full187_low_relay_higher_jet_gate_6900.py
prlimit --as=4294967296 --cpu=120 -- python3 -B \
  .experiments/full187_low_relay_higher_jet_gate_6900.py
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187LowRelayHigherJetGate6900.lean
```
