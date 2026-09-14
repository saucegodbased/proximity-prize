# k=0 critical raw-S robustness correction

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G`, full raw source. This is
an exact finite discriminator plus a STOP boundary, not a target proof or a
submission candidate.

## Corrected verdict

The special constant-`T`, equal-error receipt was useful for discovering the
raw-S staircase, but its first closing grade is **not universal**. On that
receipt the seed-zero critical band `X^a Y^m S` creates the missing curvature
normal. On three deterministic nonconstant/generic receipts, the same entire
prefix is contact-injective and creates no normal at all.

In the exact `m=3B-1` m5 chamber, the generic closing object is instead a
causal adjacent pair. After all subcritical raw-S bands `Y^y S`, `y<m`, and
the raw `{1,R}` family, either of these two prefixes reaches rank four:

```text
(Y^m S, Y^m S Z),       or
(Y^m S, Y^(m+1) S).
```

The predecessor `Y^m S` is essential: `Y^m S Z` alone and `Y^(m+1) S`
alone are both injective. This is a two-dimensional staircase corner, not an
isolated monomial or an arbitrary top layer.

However, a second exact chamber shows that this statement needs an explicit
capacity hypothesis. In a three-error m8/B3 control, even the complete
two-seed critical cell plus the first newly legal mixed connector
`S Y^(m-1) R` is contact-injective—but that profile's *complete* source is
smaller than the published contact bound. Thus this is a capacity RED, not a
target-relevant profile-universality falsifier.

The seed shift does **not** track the Newton quotient degree. A generic
receipt with constant anchor quotient still needs the `z=1` companion, while
the special constant-`T`/equal-error receipt closes at `z=0`. Therefore the
target passive cap does not need to cover the possible degree 49340 of an
anchor quotient; that inference was tested and rejected.

## Exact robustness table

All ranks below are over `F_101`; a row is
`columns / contact rank / kernel dimension / boundary gain`.

The target-ratio exact profile is

```text
(n,w,g,m,B,s,U,L) = (11,5,8,5,2,1,8,8).
```

| receipt | tangent | raw `{1,R}` | + all `S,y<5` | + `Y^5S,z=0` | + adjacent cell |
|---|---:|---:|---:|---:|---:|
| special constant-T/equal mismatch | deg 6 | 2076/2038/38/3 | 2936/2898/38/3 | 2948/2907/41/4 | already closed |
| trial 401 top monomial | `Q=X^7`, deg T=1 | 2076/2076/0/0 | 2936/2936/0/0 | 2948/2948/0/0 | z1: 2960/2948/12/4 |
| trial 402 top dense | deg Q=7, deg T=1 | 2076/2076/0/0 | 2936/2936/0/0 | 2948/2948/0/0 | z1: 2960/2948/12/4 |
| trial 407 generic constant quotient | `Q=X^6`, deg T=0 | 2076/2076/0/0 | 2936/2936/0/0 | 2948/2948/0/0 | z1: 2960/2948/12/4 |

For trial 401, the active-axis alternative is exact:

```text
precritical + Y^5 S Z                  2948/2948/0/0
precritical + Y^6 S                    2943/2943/0/0
precritical + Y^5 S + Y^6 S            2955/2948/7/4
precritical + Y^5 S + Y^5 S Z          2960/2948/12/4.
```

Thus neither second cell works alone, but either adjacent cell works after
the same critical predecessor.

The two low-tangent countercontrols correctly fail to reach four (indeed the
tested prefixes have gain zero). Their agreement tangents have degree at most
`w`, so the actual decoder pencil supplies a nonzero tangent annihilator and
rank four would be mathematically impossible.

The ceiling profile `(m,B)=(6,2)` is a useful negative control: a generic
degree-seven tangent remains injective through the *complete* raw `{1,R,S}`
family, ending at `3924/3924/0/0`. Hence none of the finite first-grade claims
may be stated for arbitrary `m`; the target-relevant arithmetic is the exact
chamber `m=3B-1`.

## Second exact-chamber discriminator: capacity RED, target-inconclusive

The first m8 control with `(n,w,g)=(7,3,5)` was too easy: raw `{1,R}` plus
the subcritical S staircase already had gain four,
`6718/6627/91/4`. It is recorded as **INCONCLUSIVE**, not confirmation.

The corrected discriminator adds a third error and tests precisely the
three-cell/connector family suggested by the literal quotient recurrence:

```text
field                 F_101
(n,w,g,m,B,s,U,L)     (8,3,5,8,3,1,12,12)
trial                 811
deg(P), deg(Q)        3, 4
agreement set         {0,1,4,5,7}

raw {1,R}                              4654 columns
all S with Y degree < 8                2064 columns
all legal S Y^7 R connectors             64 columns
Y^8 S at seed degrees 0 and 1             30 columns
-----------------------------------------------------
total/contact/kernel/boundary gain     6812/6812/0/0
```

This is an exact **family RED**: there is no relation at all for this family,
so no boundary argument can repair it inside this profile. But the published
local rank is 1531, while the complete source has only 11,711 columns:

```text
full-source margin = 11711 - 8*1531 = -537.
```

Consequently the result cannot falsify a theorem whose hypotheses include the
positive source surplus enjoyed by the target. It ran in 215.9 seconds at
3.85 GiB peak RSS
under a hard 7.5 GB address-space cap. Canonical SHA-256:
`48cf97402b1126bcbd23e2744b9347f8cc4fbdbe140cd28c88351d828c47dd09`.

The honest conclusion is narrower: exact `m=3B-1` arithmetic alone does not
guarantee this low-family kernel; a source-capacity hypothesis is essential.
Whether positive capacity plus the first mixed connector suffices must be
tested separately. Extrapolating either the m5 positive receipt or this m8
negative-capacity receipt to target scale would be unsound.

## Literal causal identity (now formal)

Let

```text
W = u0 + u1 Z,
N = epsilon R - epsilon^2 S + epsilon^3 T,
V = W + N.
```

Because `epsilon^m` divides `N^m=(V-W)^m`, multiplication by raw `S` gives
modulo order-`m` contact

```text
S V^m = - sum_{y<m} (-1)^(y+m) choose(m,y) S V^y W^(m-y),

W^(m-y) = sum_z choose(m-y,z)
                 u0^(m-y-z) u1^z Z^z.
```

This exactly explains why every lower `Y` grade and its seed companions occur;
the critical band without the subcritical staircase cannot close. Commit
`41bec9f` proves the identity in Lean, and `806558b` proves its arbitrary seed
shift plus target legality for the two-seed packet. These are local complete-
contact identities. They do not yet globalize the node-dependent `u0,u1`
coefficients through the tapered X windows.

## Exact factor evidence and the Q'' correction

For the special m5 receipt, the first critical band creates three canonical
relations. Every one uses raw `{1,R}` and all S layers `y=0,...,5`. The gcd of
their boundary-S polynomials is exactly

```text
Lambda_A(X)^(m-1) = Lambda_A(X)^4,
```

of degree 32, where `Lambda_A` is the degree-eight agreement locator. The
interpolated direction's `Q''` divides none of the three boundary-S
polynomials and does not divide their gcd. Thus `Q''` is not a local primal
factor. It must arise only after the global transpose/connection commutator.
This matches the formal semantic endpoint in commit `a81b194`: once the
missing recurrence outputs `lambdaS • Q'' = 0`, retained badness and the
below-characteristic degree bound force `Q'' != 0` and hence `lambdaS=0`.

The factor receipt is canonical SHA-256
`2d3b1bbfd731d8f6ff8dbb6f06fcc90c6f0e4b153c4f72b8c726046eaa774f95`;
runtime was 31.1 seconds and peak RSS 685 MiB. The exact script is
`k0_target_ratio_critical_s_relation_factor_6900.py`.

## Target legality and capacity

In the reduced-curvature green target profile from `da056e7`,

```text
(m,B,s,U,L) = (47,16,6,64,5107),
```

the relevant adjacent bands are all raw-source legal:

```text
X^a Y^47 S,       z=0 or 1, width 2,188,005 per seed band;
X^a Y^48 S,       z=0,      width 2,056,934.
```

Their active degrees are 48 and 49, at most `U=64`; passive degrees are at
most 49, far below `L=5107`; and derivative cost is two, below `B=16`.
They are subsets of the already capacity-green full source, so there is no
new source-count obligation. The formal source-monotonicity lemma in
`K0LineThenKill6900.lean` ensures that a surjective low subfamily stays
surjective when the rest of the full source is restored.

## Exact remaining universal hypothesis / STOP

The previously suggested unconditional low-family theorem

```text
raw {1,R} + subcritical S + one adjacent critical pair
  (+ the first S Y^(m-1) R connector)
forces lambdaS • Q'' = 0
```

is finite-falsified without source capacity. The strongest honest target
hypothesis left is a **capacity-aware** version: in the positive-surplus target
profile, the complete legal R/S/mixed-derivative staircase (or a proved
capacity-sufficient subfamily) must make the global transposed connection
output `lambdaS • Q'' = 0`. No smaller capacity-aware universal raw family has
yet been identified.

The local nilpotent identity and two-seed legality remain valid ingredients,
and the semantic `Q''` endpoint remains complete, but the missing bridge must
use higher derivative shapes. Local binomial closure, aggregate rank counts,
and the special constant-T or m5 receipts do not prove it. Do not claim that
seed zero alone is universal, that the seed grade is `deg T`, that `Q''` is a
factor of a local primal relation, that the first mixed connector suffices
without capacity, or that the negative-capacity m8 receipt refutes the target
profile.

## Reproduction

```text
k0_target_ratio_raw_s_staircase_robustness_6900.py
  canonical 82a95b952c3d8a10a59b2abd6c0d76b240e91bb8e4fb3812bfff10bdfaab8c3c
  runtime 128.0 s; largest worker RSS 1.22 GiB

k0_target_ratio_high_tangent_s_grade_extension_6900.py
  trial401 canonical cd7b22bfdd3ee656c20cc3173927feabab0dcf3be944d0a5e48336b2ff889e90
  runtime 72.1 s; peak RSS 625 MiB

k0_second_exact_chamber_corrected_connector_gate_6900.py
  canonical 48cf97402b1126bcbd23e2744b9347f8cc4fbdbe140cd28c88351d828c47dd09
  runtime 215.9 s; peak RSS 3.85 GiB
```

Every run was deterministic. At most three finite matrices were live in the
parallel robustness gate; aggregate RSS stayed below 4 GiB. No `decide`,
`native_decide`, random parameter search, production file, or candidate was
used.
