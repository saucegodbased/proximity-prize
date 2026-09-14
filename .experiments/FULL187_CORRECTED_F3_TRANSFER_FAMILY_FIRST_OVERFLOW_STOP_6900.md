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

There is also a shorter global STOP: even allowing *every* `c_i` to be an
arbitrary polynomial cannot make the family legal. Its top `Y^61`
coefficient has an unavoidable `R^60` factor whose degree already exceeds
the complete `Y^61` source window, while the zero identity it would require
is impossible modulo `E0`.

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

## Global polynomial-coefficient STOP

Let every `c_i(X)` be arbitrary, retaining only `c_0=1` so the packet
boundary is unchanged. The coefficient of the top monomial `Y^61` is

```text
R^60 * sum_(i=0)^59 c_i(X) H^(59-i) E0^i.               (2)
```

The factor `R^60` alone has degree `60*49341=2960460`, whereas the entire
half-open `Y^61` coefficient window has width

```text
D-61W = 2829449
```

(maximum legal degree `2829448`). Thus source legality forces the sum in
(2) to vanish identically. Reducing that identity modulo `E0` leaves
`H^59=0 mod E0`, because every `i>0` summand contains `E0` and `c_0=1`.
This is impossible: `H` and `E0` are locators of disjoint node sets and are
therefore coprime. No polynomial tuning of any of the sixty separated
transfer coefficients can repair the family.

## Process consequence

Do not spend time tuning scalar/binomial/lacunary or polynomial `c_i` in this
separated family. The next viable test is the full multi-degree
target-specific Padé problem, in which genuinely different higher source
layers are solved simultaneously. It must retain passive `Z` coefficientwise.
Collapsing `Z`, replacing `W_E` by `V-1`, or promoting the present family to
a source lift is unsound.

## Reproduction

```bash
prlimit --as=2147483648 --cpu=180 -- \
  python3 -B \
  .experiments/full187_corrected_f3_transfer_family_first_overflow_6900.py
```

Recorded run: exit 0, peak RSS 946,912 KiB.

```text
canonical sha256 8febd723d4c9ea072fd8dc012a83f276af5f241354ba6a08b6faab3be2fc94c2
script sha256    05da0bfd36a05b3826fcbb1eabccef532c76b0e4828d643b35f3fce71ed41eea
```
