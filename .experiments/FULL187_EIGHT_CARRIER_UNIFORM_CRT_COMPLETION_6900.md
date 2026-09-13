# Full187 eight-carrier uniform CRT completion

Date: 2026-09-13 UTC. Scope: lower-6900 THREE-RHS research only. No
production, submission, claim, score, or radius file was changed.

## Verdict

The sixteen-dimensional global CRT deficit reported in `f31f1ef` is
**closed at Full187 scale**. It came from carrying the sharp multiplier
degrees of the tiny F101 reconstruction into the target, even though the
target width does not require that taper.

For the eight carriers

```text
K[a,c](p) =
  p Lambda^a V^(m-a-2c) J1^c Z^(b+a+c),

(a,c) = (0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),
d = a+c,
```

the tiny extraction used

```text
deg p <= 3e-1-d.
```

Those spaces have dimensions

```text
3e, 3e-1, 3e-1, 3e-2, 3e-2, 3e-3, 3e-3, 3e-4,
```

whose sum is `24e-16`. At Full187, commit `71a3e44` already proved the
stronger uniform legal bound

```text
deg p <= 3e-1 = 245192
```

for every carrier. The eight coefficient spaces then have total dimension

```text
8(3e) = 24e = 1,961,544,       e=81731.
```

The exact increments are

```text
0,1,1,2,2,3,3,4,
```

and sum to sixteen. This is dimension-minimal: fewer than sixteen new
coefficients cannot fill a rank-sixteen cokernel. No ninth carrier and no
sixteen-condition invariant for the forced residual are needed.

## Exact global F101 receipt

`f101_eight_carrier_uniform_crt_completion_6900.py` constructs the literal
global selected contact matrix in

```text
F101,
(n,w,g,m,D,s,t,J,L)=(10,4,7,4,28,1,1,6,10),
E={7,8,9}.
```

Rows comprise all 24 selected value/first/second-Hasse contact coordinates
at each of the three errors. Columns are actual raw carrier expansions
multiplied by monomials in `X`; the matrix is not replaced by an abstract
Vandermonde model.

For two nondegenerate arbitrary-offset chambers it obtains:

| offsets | residual values | tapered matrix | uniform matrix | determinant |
|---|---|---|---|---:|
| `(3,5,7)` | `(1,9,17)` | `72x56`, rank `56` | `72x72`, rank `72` | `92` |
| `(11,19,23)` | `(2,13,29)` | `72x56`, rank `56` | `72x72`, rank `72` | `76` |

It removes each of the sixteen restored columns in turn. Every resulting
matrix has rank `71`. Thus all sixteen additions are individually necessary
relative to the tapered box, and together they are sufficient.

For every passive shift `0,1,2,3` available in the small chamber, shifting
the source by `Z^k` and shifting the selected rows by the same amount gives
the identical `72x72` matrix, including its determinant. This is the exact
finite version of the fact that passive shifting changes neither the
coefficient CRT nor the diagonal block.

## Why this is the global CRT theorem, not only a count

At every error node the three-Hasse-layer carrier matrix is block lower
triangular, with the already proved nonzero determinant

```text
(Lambda(alpha)^16 delta(alpha)^(8m-19))^3.
```

Therefore arbitrary selected contact data uniquely determines three local
Hasse coordinates for each of the eight coefficient polynomials. Ordinary
Hermite CRT at `e` distinct nodes realizes arbitrary three-jets with one
polynomial of degree `<3e`. Applying it independently eight times produces
the required global multipliers. The Lean companion isolates this exact
eight-fold composition from the existing one-polynomial Hermite theorem.

The F101 full-rank calculation checks the composition in literal translated
contact coordinates, including all below-diagonal terms caused by the
received-direction offsets and by derivatives of `Lambda`. Hence the
argument is not relying only on equality of dimensions.

## Agreement contact and Full187 source width

Multiplying a `Lambda/V/J1` order-four agreement cycle by any polynomial in
`X` preserves agreement contact. Raising the coefficient degree also does
not change active degree, slope degree, curvature degree, seed degree, or
the passive `Z` shift.

For Full187, write `d=a+c<=4` and let `y` count centered factors replaced by
raw active variables. The exact uniform strip inequality is

```text
h + d*180413 + (60-d-y)*163462 + y*131071 < 10824780,
h <= 245192,
y <= 60-d.
```

The worst endpoint is the `d=4,y=0` carrier:

```text
245192 + 4*180413 + 56*163462 = 10120716,
10824780 - 10120716 = 704064.
```

Thus every restored top coefficient is individually source-legal with
`704064` units of worst-case strict-width margin. This does not use the
delicate coupled cancellation required in the tiny chamber. All passive
shifts `0<=k<=2620` retain the same width and stay within grade `2703`, as
proved in `Full187OrderFourCovariantWidth6900.lean`.

## What happened to the proposed sixteen compatibilities?

The three exact initial offset F101 terminal shells do satisfy the old
tapered conditions: their multiplier degrees are exactly

```text
8,7,7,6,6,5,5,4 = 3e-1-d.
```

So their sixteen top Hermite coordinates vanish. It remains unproved that
every residual produced by a long seed induction shares this special
property. That question no longer needs to be answered: the uniform target
box allows those sixteen coordinates to be arbitrary and interpolates them
directly.

## Honest remaining gate

This closes only the coefficient-cap/CRT issue. The route still must prove
that the **complete** live terminal residual is captured by the selected
`24e` three-jet state, and that cancelling one seed layer creates only the
strictly higher-seed leakage handled by the 2621-layer triangular assembly.
The independent `Z1` direction and downstream typed allocation are also not
addressed here. The result must not be reported as end-to-end 6900.

## Reproduction

```text
python3 -m py_compile \
  .experiments/f101_eight_carrier_uniform_crt_completion_6900.py
prlimit --as=4294967296 --cpu=1200 -- python3 -B \
  .experiments/f101_eight_carrier_uniform_crt_completion_6900.py

.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187EightCarrierUniformCRTCompletion6900.lean
```

The canonical Python payload hash is

```text
b0e4224b7907a92ad2494827dc3f86a91ea4dd8fe3ae56f67e3b50692db90102
```

Artifact hashes at the checked run are

```text
06c1e78396bed6e385811cbab5e6217be6fa3d8ec9d912345d4490627d8283f5  f101_eight_carrier_uniform_crt_completion_6900.py
bb3d8a12d6846ad03359a8c4cc43133d37452cff163b0f079f22f133feddec61  Full187EightCarrierUniformCRTCompletion6900.lean
```

The Lean run exits zero under the four-GiB wrapper. Its printed axioms are
only the ordinary accepted logical axioms (`propext`, `Classical.choice`,
and `Quot.sound`); there is no `sorry`, `decide`, or `native_decide`.
