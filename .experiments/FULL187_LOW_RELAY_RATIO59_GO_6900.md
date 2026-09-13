# Full187 low relay: ratio-59 first-jet GO

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, radius, or claim file was changed.

## Result

**GO for the requested first-jet gate.** The smallest genuinely lower-normal
relay has two literal rows:

```text
R59 := L (U V^59 - H^3 Z V^57 J1).
```

The two normal monomials have weighted normal degree 59:

```text
59 = 59 + 2·0 + 3·0 = 57 + 2·1 + 3·0.
```

The extra `L` provides the missing one unit of agreement contact.  Under the
same pure seed as the degree-60 checkerboard,

```text
V = -H^2 Z,       J1 = H U Z,       J2 = B Z,
```

it cancels exactly:

```text
L (U V^59 - H^3 Z V^57 J1) = 0.                         (1)
```

At an error, reduce modulo `H` in the literal chart

```text
V = 1 + E + T R + O(T^2).
```

The second relay row has an explicit `H^3`, hence

```text
R59 mod H = L U V^59.
```

It has a controllable nonzero value (both `L` and `U` are units at the
simple errors) and both value-normalized first ratios are **59**, rather
than the high checkerboard's locked ratio 60.

## Smallest matching packet: four rows

The existing two-row high block is

```text
R60 := U V^60 - H^3 Z V^58 J1,
R60 mod H = U V^60.
```

Take independent CRT multipliers so the effective error coefficients of
`R60` and `R59` are respectively

```text
A = -58 f,       B = 59 f,
```

where `f` is the desired value at the current error node.  Then

```text
A + B = f,
60 A + 59 B = f.
```

Therefore the four-row packet `A R60 + B R59` has, simultaneously,

```text
value = f,       first E coefficient = f,       first T*R coefficient = f.
```

The second equality is not an analogy: both `E` and `T*R` enter linearly in
the same local increment of `V`.  CRT realizes the displayed effective
coefficients because the factors `U` and `L U` are error-node units.  No
inverse is put into a source coefficient; the inverses are used only to
choose degree-`<e` CRT values.

Thus the 2-row `R59` is the smallest **relay**, and four rows are the
smallest packet which both retains the high block and matches a nonzero
value plus either first jet (in fact, both of the requested first jets).

## Literal strip ledger

Use the established pure-tail strip for normal degree `n` and stratum
`r=c+2d`:

```text
D(n,r) = n(g-2e) - (g-2e-1) r,
g=180413, e=81731.
```

For a CRT multiplier of degree at most `e-1=81730`, the two new low rows
have the following exact conservative coefficient degrees:

| row | coefficient | degree bound | strict strip | margin |
|---|---|---:|---:|---:|
| `V^59` | `q L U` | 524286 | `D(59,0)=1000109` | 475823 |
| `Z V^57 J1` | `q L H^3` | 507336 | `D(59,1)=983159` | 475823 |

So the relay fits every literal strip with substantial positive margin.  It
also obeys the ordinary non-X caps: its largest active/slope/seed figures
are respectively 58, 1, and 59, well below 82, 21, and 2703.

The original two-row high partner has margins 673187 in both rows.  The
three-row high square and four-row high cubic remain legal with common
margins 411044 and 148901, respectively.  Hence the exact 5-row
`(high square)+R59` and 6-row `(high cubic)+R59` variants also pass literal
strips; they are dominated by the four-row version.

## Explicit 2–6 row symbolic tests

| rows | candidate | pure seed | reduction / first-jet result |
|---:|---|---|---|
| 2 | high binomial | cancels | `U V^60`, ratio 60: STOP |
| 2 | low `R59` relay | cancels | `L U V^59`, ratio 59: relay GO |
| 3 | same-stratum `J2/S` checkerboard | cancels | all terms have `J1,J2` degree at least 2: zero value and first jet, STOP |
| 4 | high two-row + low two-row | cancels blockwise | `-58 V^60+59 V^59`: value, `E`, and `T R` all match |
| 5 | high square + low relay | cancels blockwise | same first-jet GO after unit/CRT normalization; dominated |
| 6 | high cubic + low relay | cancels blockwise | same first-jet GO after unit/CRT normalization; dominated |

The `J2/S` test is the exact prior three-row identity

```text
B V^52 J1^4 - (B-U^2)V^53 J1^2 J2 - U^2 V^54 J2^2 = 0
```

at the pure seed.  Its lowest normal-coordinate degree is two (`J2^2`), so
it cannot supply the missing value, `E`, or `T R` term.  This discharges the
smallest available `J2/S` alternative rather than assuming it away.

## Scope

This is not a 6900 proof and not yet a complete `C_E` correction.  It leaves
all higher Hasse layers, their interactions with CRT-multiplier derivatives,
the other two prescribed Y/R/S right-hand sides, and the separate Z1 class
open.  It does, however, reopen the mixed-H route at exactly the interface
where the previous `V^60`-only STOP said an evasion had to appear: a literal,
pure-seed-cancelling lower normal stratum changes the first-jet ratio and
passes all strips.

## Checked artifacts

`Full187LowRelayRatio59Go6900.lean` proves the pure-seed identities, the
exact target strip arithmetic, and the `-58/59` first-jet equation with only
standard Lean axioms.

`full187_low_relay_ratio59_go_6900.py` independently expands the pure seed
as exponent dictionaries and tests all listed 2–6 row candidates.

```text
python3 -m py_compile .experiments/full187_low_relay_ratio59_go_6900.py
prlimit --as=4294967296 --cpu=120 -- python3 -B \
  .experiments/full187_low_relay_ratio59_go_6900.py
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187LowRelayRatio59Go6900.lean
```
