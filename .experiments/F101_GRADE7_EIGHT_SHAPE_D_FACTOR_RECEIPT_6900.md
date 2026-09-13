# F101 canonical grade-7 shell: exact eight-shape D-factor receipt

Date: 2026-09-13 UTC. Scope: F101 control research only. No production,
submission, score, or claim file was changed.

## Result

The canonical grade-7 parts of all three exact `F0,F1,F2` corrections have
an exact common shape decomposition. Write

```text
Xi = x^3 + 74x^2 + 40x + 88
   = (x+91)(x+92)(x+93),
Q = Xi^2,
D = Y-QZ.
```

For each normal `i=0,1,2`, its complete grade-7 shell (all eight observed
`(Y,R,S,Z)` shapes, with coefficients in `F_101[x]`) is exactly

```text
G_i = D^2 Z^3 [ c_i D^2 + beta_i D Z
                + sigma_i (tau Q Z^2 + Xi R Z) ].                 (1)
```

There are no grade-7 `S` shapes. Expanding (1) gives precisely the five pure
shapes

```text
Y^y Z^(7-y),       0 <= y <= 4,
```

and the three one-`R` shapes

```text
Y^y R Z^(6-y),     0 <= y <= 2.
```

Thus after subtracting the requested top piece

```text
c_i (Y-QZ)^4 Z^3,
```

the five pure shapes are not arbitrary: their exact remainder is

```text
D^2 Z^4 (beta_i D + sigma_i tau Q Z).                            (2)
```

The `R` shapes are simultaneously

```text
Xi sigma_i R D^2 Z^4.                                            (3)
```

This is a genuine closed identity for the selected canonical corrections.
It is a promising PC/HRS *form*—a repeated `D^2` factor and successive
`Q=Xi^2` steps—but it is not basis-invariant and does not prove a
target-scale recurrence.

## Exact coefficient factors

The universal quotient in (1) is

```text
tau = 95 (x^2 + 83x + 47)
    = 95x^2 + 7x + 21.
```

The top constants are

| correction | `c_i` |
|---|---:|
| F0 | 53 |
| F1 | 76 = 91*53 |
| F2 | 66 |

For `F0`, write

```text
sigma0 = 84 x(x+39)(x+60)(x+94)(x+95)(x+96)(x+97)(x+98)
          (x+99)(x+100)(x^2+35x+41),

beta0 = (x^2+37x+58)(x^2+57x+18)
        (x^10+71x^9+76x^8+39x^7+96x^6+34x^5+62x^4
          +58x^3+82x^2+42x+44).
```

For `F1`, the non-top cores scale uniformly:

```text
beta1 = 55 beta0,
sigma1 = 55 sigma0.
```

`F2` is not a scalar multiple of the F0 core. Its exact factors are

```text
sigma2 = 23 x(x+77)(x+94)(x+95)(x+96)(x+97)(x+98)(x+99)(x+100)
          (x^3+80x^2+58x+12),

beta2 = 64 (x^14+62x^13+32x^12+41x^11+47x^10+78x^9+89x^8
             +53x^7+6x^6+x^5+71x^4+9x^3+2x^2+x+79).
```

The factor `(x^2+83x+47)` is exact in every `alpha_i/sigma_i`; this is the
source of the same `tau` in all three shells.

## Exact checks and negative result

The residual pure cubic after the top subtraction has `D` multiplicity
exactly two for each normal, not three or four. Equivalently, in the
five-pure-shape order its first two Hasse moments at `Y=QZ` vanish and its
second one is nonzero. Therefore (2) is sharp within this canonical shell:
the entire remainder does not carry an additional `D` factor.

The raw eight-shape shells are not all scalar multiples across normals:
after normalizing by the `Y^4Z^3` coefficient, F1 mismatches F0 on the other
seven shapes and F2 does as well. The factorization is common in shape, not
a one-dimensional correction vector.

## Reproduction

`f101_grade7_pure_yz_residual_factor_probe_6900.py` independently rebuilds
the canonical relations used by the existing factor probe, factors all
coefficient polynomials over `F_101`, verifies (1) coefficient by
coefficient, and checks the sharp `D^2` multiplicity. It ran under a 4 GiB
address-space cap in about six seconds.

```text
prlimit --as=4294967296 --cpu=180 -- python3 -B \
  .experiments/f101_grade7_pure_yz_residual_factor_probe_6900.py
```

Final receipt hashes:

```text
canonical payload SHA-256
d786f4481a76b536a8f9be0f7ad91e51d985daa89993fc2f9b89db3242420802

script SHA-256
63124bdda914582ae32260b73652b874f00b7c9c6b739f529df46867bfae73c9
```
