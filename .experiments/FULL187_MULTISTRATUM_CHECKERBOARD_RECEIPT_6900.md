# Full187 multistratum checkerboard receipt

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, or claim file was changed.

## Exact mixed-degree/mixed-`H` result

The requested loophole is real at the pure-seed endpoint.  Seed shifts make
different `r=c+2d` strata comparable: their bare tails differ by one `Z` and
three `H` powers. With

```text
V  = -H^2 Z,
J1 =  H U Z,
```

the three literal normal-shell rows

```text
(a,c,d) = (60,0,0), (58,1,0), (56,2,0)
```

at `r=0,1,2`, respectively, satisfy

```text
U^2 V^60
  - 2 U H^3 Z V^58 J1
  + H^6 Z^2 V^56 J1^2 = 0.
```

All three pure tails are the same monomial `H^120 U^2 Z^60`. This is a
literal three-packet checkerboard across both normal degree and `H` stratum,
not an adjacent same-stratum two-packet identity.

It remains source-legal after multiplying the whole identity by a CRT
polynomial `q` of degree `<e=81731`:

| row | pure multiplier | degree upper bound | strict pure window | margin |
|---|---|---:|---:|---:|
| `V^60` | `q U^2` | 606016 | 1017060 | 411044 |
| `Z V^58 J1` | `q U H^3` | 589066 | 1000110 | 411044 |
| `Z^2 V^56 J1^2` | `q H^6` | 572116 | 983160 | 411044 |

At a simple error, `U=-2LH'` is a unit. Reducing the checkerboard at
`H=0,V=1,J1=0` leaves `q U^2`; degree-`<e` CRT can therefore prescribe its
error-node **values**. This is a concrete construction escaping the
pure-seed endpoint charge while retaining a controllable nonzero error value.

It does not match the higher error jets of `F0`, because `V^60` retains them.
Thus it is not a completed `C_E` correction or a 6900 proof. The next exact
object is the mixed-stratum Hermite system which cancels those jets without
losing the displayed strict margins.

## Same-stratum supplementary identity

The full 187 normal shell has a genuine source-legal three-term cancellation
at the pure-seed endpoint. Write its pure-seed specialisation as

```text
V  = -H^2 Z,
J1 =  H U Z,
J2 =  B Z.
```

Here `U` and `B` are the literal pure-seed coefficients of `J1` and `J2`.
For the three shell triples

```text
(a,c,d) = (52,4,0), (53,2,1), (54,0,2),
```

one has the exact polynomial identity

```text
B V^52 J1^4
  - (B-U^2) V^53 J1^2 J2
  - U^2 V^54 J2^2 = 0.
```

The signs use the literal `V=Y-H^2 Z` convention.  All three shapes have
weighted normal degree 60, and their `r=c+2d` value is four.

The coefficient degree bound is

```text
deg B, deg U^2 <= 2(g+e-1) = 524286.
```

The strict pure-seed X window for shell `r` is

```text
D_r = 60(g-2e) - (g-2e-1)r = 1017060 - 16950r.
```

At `r=4`, `D_r=949260`, leaving `424974` degrees of room. This gives another
three-normal source-legal endpoint cancellation, but it is weaker than the
mixed-`H` construction above.

The general enumeration finds 126 such three-term blocks. They occur for
`4 <= r <= 29`; the tight block at `r=29` still has strict margin `1224`.
The mechanism is the adjacent syzygy module of the weighted monomials
`U^(r-2d) B^d`, but the displayed combination contains all three adjacent
normal shapes, rather than merely renaming one two-packet relation.

## What the supplementary block does *not* solve

This same-stratum block is not a `C_E` correction and is not a 6900 source theorem. On the
normal error S-line (`E=R=0`), the first two terms vanish to orders four and
three, while the last has the exposed initial class

```text
-U^2 (L^2 S)^2.
```

At a simple error root, `U=-2 L H'` and `L` are units (in the target's odd
characteristic), so this quadratic class is nonzero. The three-term block
therefore cannot by itself lie in the complete error-contact kernel or match
one of the prescribed linear RHS values.

This isolates the genuine open loophole more narrowly: a future construction
must cancel that S-line class using *other* normal/H strata while retaining
the pure-seed cancellation and every strict X window. Conversely, a general
obstruction can target precisely this associated-graded S-line class; a
single-packet endpoint argument is insufficient.

## Actual-domain correction

For the NTT domain `Omega=X^N-1`, the natural error inverse is
`N^-1 X H'`, of degree `e`, not the obsolete constant-derivative degree
`e-1` representative. This receipt does not use an inverse; any later
CRT/packet calculation must use the degree-`e` cost.

## Artifacts

`Full187ThreeTermPureSeedCheckerboard6900.lean` proves the formal identity
and all target arithmetic with standard axioms only.

`full187_multistratum_checkerboard_receipt_6900.py` independently enumerates
the literal 187 triples, verifies the symbolic cancellation, and emits a
canonical SHA-256 receipt. It uses no third-party packages.

Reproduce under the requested hard cap:

```text
python3 -m py_compile .experiments/full187_multistratum_checkerboard_receipt_6900.py
prlimit --as=4294967296 --cpu=120 -- python3 -B \
  .experiments/full187_multistratum_checkerboard_receipt_6900.py
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187ThreeTermPureSeedCheckerboard6900.lean
```
