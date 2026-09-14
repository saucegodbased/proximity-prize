# Full187 corrected F3 transfer family: first-overflow STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production and the
accepted 6806 submission are unchanged.

## Verdict

The literal passive-`Z` correction gives a genuine 60-parameter family of
unbounded contact kernels, but that separated family is **RED at its first
new source coefficient, `Y^2`**.  Scalar coefficients miss the taper by
131,071 degrees. Even allowing the second family coefficient to be an
arbitrary polynomial cannot repair it: exact division of `Xi_H` by `Xi_E`
leaves a degree-81,730 remainder, so the best possible coefficient still
misses the legal bound by 81,729.

This is a STOP for the proposed factor-by-factor transfer family, not for a
full target-specific simultaneous Padé cascade.  The latter can use source
layers of degree at least three to change the error-side condition imposed on
the degree-two coefficient.  The exact `F_101,N=10` analogue confirms that
this distinction is real: the full target-specific cascade is solvable even
though the analogous separated first step is not.

## Correct passive-Z forms

Write

```text
H = Xi_H,             R = Xi_(G\H),        E0 = Xi_E,
V = Y-Z*q_H,          W_E = Y-1-X^81730 Z,
B = H^59 R^60.
```

Outer `Z` is passive: it is not counted by the contact-order truncation.
Thus `V-1` is not error-active. At an error node it has zero-contact part

```text
Z*(U1-q_H),
```

which is nonzero at every one of the 81,731 target error nodes. The correct
error-active form is `W_E`: on errors `U1=X^81730`, so its entire passive
part cancels.

For arbitrary scalars `c_i`, `c_0=1`, consider

```text
K(c) = sum_(i=0)^59 c_i H^(59-i) R^60 E0^i
                         V^(i+1) W_E^(60-i).
```

Every summand separately has contact order 60:

```text
H nodes:  (59-i) locator zeros + (i+1) active V factors = 60;
R nodes:  R^60                                             = 60;
E nodes:  i locator zeros + (60-i) active W_E factors     = 60.
```

Only `i=0` has source degree one, and its linear term is exactly

```text
H^59 R^60 V = B*(Y-Z*q_H) = F3.
```

So this is a sound unbounded causal guide, unlike the bare `(V-1)^60` seed.

## Exact first overflow

The homogeneous source-degree-two part receives contributions only from
`i=0,1`.  Its pure `Y^2` coefficient, up to a nonzero global sign, is

```text
H^58 R^60 (60 H + c_1 E0).                    (1)
```

The common factor has degree

```text
58*131072 + 60*49341 = 10562636.
```

The Full187 half-open coefficient window for `Y^2` is

```text
D-2W = 10562638,
```

so the parenthesis in (1) would have to have degree at most one.

For scalar `c_1`, the `H` leading term cannot cancel, and (1) has degree
10,693,708, exceeding the maximum legal degree 10,562,637 by 131,071.

Allowing polynomial `c_1(X)` does not fix it. Euclidean reduction gives the
smallest possible degree in the coset `60H + E0*F_p[X]`. On the literal
target,

```text
degree(H mod E0) = 81730.
```

Therefore every polynomial choice has degree at least

```text
10562636 + 81730 = 10644366,
```

still 81,729 beyond the legal maximum.  The exact coefficient hash of the
remainder is

```text
1e4843a39155ed311f8c66a6136184d76528847be0f0478222dce8f8689cfca2.
```

## Process consequence

Do not spend time tuning scalar/binomial/lacunary `c_i` in this separated
family: no such tuning reaches even `Y^2`.  The next viable test is the full
multi-degree target-specific Padé problem, in which all higher source layers
are solved simultaneously.  It must retain passive `Z` coefficientwise.
Collapsing `Z`, replacing `W_E` by `V-1`, or promoting the present family to
a source lift is unsound.

## Reproduction

```bash
prlimit --as=2147483648 --cpu=180 -- \
  python3 -B \
  .experiments/full187_corrected_f3_transfer_family_first_overflow_6900.py
```

Recorded run: exit 0, peak RSS 151,816 KiB.

```text
canonical sha256 1ba1e76c1054bd9e940d48c135ed5cb5418bf126d4eac24f16a2ae52fa29af9f
script sha256    37a7b12def3250906739ad2ad06c686b7124e9b5f91c997e83ba3345ed96986b
```

