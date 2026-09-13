# Full187 mixed-`H` binomial ladder: first-jet STOP

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
submission, score, or claim file was changed.

## The surviving pure-seed family, extended once

Put

```text
B := U V^2 - H^3 Z J1,
Phi_k := V^(60-2k) B^k.
```

For the pure seed `V=-H^2 Z`, `J1=H U Z`, one has `B=0`.  Hence every
`Phi_k` has zero pure tail.  The prior three-row checkerboard is exactly

```text
Phi_2 = V^56 B^2
      = U^2 V^60 - 2 U H^3 Z V^58 J1 + H^6 Z^2 V^56 J1^2.
```

The next (four-row) chain member is

```text
Phi_3 = V^54 B^3
      = U^3 V^60 - 3 U^2 H^3 Z V^58 J1
        + 3 U H^6 Z^2 V^56 J1^2 - H^9 Z^3 V^54 J1^3.
```

Thus this check reaches beyond the original three-row square.  Its rows are
the literal triples `(60-2i,i,0)`, `0 <= i <= k`, with seed shift `i` and
distinct `r=i` strata.

For a multiplier `q_k` of degree `<e=81731`, the `i`th source coefficient
has degree at most

```text
(e-1) + (k-i)(g+e-1) + 3 i e,
where g+e-1 = 262143.
```

The strict windows are `D_i=1017060-16950i`.  Their common slack is

| chain | source degrees (in increasing `i`) | common slack |
|---|---|---:|
| `k=1` | `343873, 326923` | `673187` |
| `k=2` | `606016, 589066, 572116` | `411044` |
| `k=3` | `868159, 851209, 834259, 817309` | `148901` |

The putative quartic has its first source degree `1130302`, exceeding
`D_0=1017060` by `113242`.  So `k=3` is the last member of this particular
source-legal binomial chain; it gives no new higher-jet degree of freedom
outside the three coefficients `q_1,q_2,q_3`.

## Exact local expansion through the first error layers

In the literal error chart write the order-one `H` parameter as `T` and

```text
V = 1 + E + T R + T^2 C,
```

where `C` collects the known `-S/2` term and any order-two control term.  The
first-passive minor `T R` is unchanged by such order-two controls.  Expanding
the displayed binomial, every summand with `i>0` has `H^(3i)`, hence is
`O(T^3)`.  Therefore, for any `k>=1`,

```text
Phi_k = U^k (1 + E + T R + T^2 C)^60 + O(T^3).
```

For a combination of all source-legal ladder members,

```text
Phi = q_1 Phi_1 + q_2 Phi_2 + q_3 Phi_3,
P := q_1 U + q_2 U^2 + q_3 U^3,
```

this gives the associated-graded identity

```text
Phi = P + 60 P E + 60 P (T R) + 60 P T^2 C
      + terms quadratic in (E,T R,T^2) + O(T^3).
```

Equivalently, modulo `H` the whole ladder is exactly `P V^60`.  This statement
does **not** require a specialization of `J1`: all `J1`-terms are already
killed by their explicit positive `H` power.

The desired normalized `F0=L^59 V` has instead

```text
F0 = L^59 + L^59 E + L^59 (T R) + L^59 T^2 C.
```

Matching the value at a simple error requires `P=L^59`, a nonzero unit.
Then both the `E` coefficient and the first `T R` coefficient differ by

```text
60 P - L^59 = 59 L^59 != 0.
```

The target field has odd characteristic larger than `59`, so this is a real
first-jet incompatibility.  It happens before any further source-window cost
is relevant: no combination of the `k=1,2,3` chain can match even one
nontrivial higher error jet after it has matched the nonzero value.

## Scope of the STOP

This closes the whole binomial-power ladder anchored at the sole `r=0` row
`V^60`, including the original mixed three-row checkerboard and its cubic
four-row extension.  Any combination of such shifted triples reduces modulo
`H` to a scalar multiple of `V^60`, so it has the locked ratio
`(first E jet)/(value)=(first T R jet)/(value)=60`.

It is not a no-go theorem for every mixed-degree/mixed-`H` construction.  An
evasion must introduce another nonvanishing `H=0` error class (therefore a
genuine lower-degree relay or a different normal source), which can alter
that ratio while preserving the pure-seed cancellation.  The present source
shell contains no second `r=0` triple, so it cannot do so internally.

## Checked artifact

`Full187MixedHBinomialLadderEJetStop6900.lean` formally proves the square and
cubic factorizations, the exact `k<=3` source arithmetic, and the field-generic
`60` versus `1` first-jet contradiction.  It uses only standard axioms and
fits the 4 GiB runner:

```text
.experiments/run_lean_4g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/Full187MixedHBinomialLadderEJetStop6900.lean
```

The actual NTT-domain inverse convention remains `N^-1 X H'` (degree `e`);
no inverse is used in this binomial-ladder calculation.
