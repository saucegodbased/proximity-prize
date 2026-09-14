# K0 tangent-degree / passive-face discriminator

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G`, raw full source. This is a
finite exact mechanism/STOP receipt, not a target proof or candidate.

## Frozen receipt and hypotheses

The controlled profile at passive cap 10 is

```text
(n,w,g,m,B,s,U,L) = (9,3,6,8,3,1,12,10),  field F_101.
```

Trial 912 has candidate degree 3, seed 42, nodes `0,...,8`, exact agreement
set `{0,1,4,5,6,8}`, and errors `{2,3,7}` with nonzero value residuals
`(53,3,76)`. The two receipts keep the candidate, agreement set, seed, and
off-agreement data fixed and prescribe agreement tangents `Q=X^4` and
`Q=X^5`. Each is retained-bad: six distinct agreement nodes rule out any
degree-at-most-three polynomial with the same values. Characteristic 101 is
larger than every local order used here, and `Q''` is nonzero in both cases.

The four boundary rows are the literal gradient coordinates `(Y,R,S,Z)` at
the new point `X=9`. Replacing ordinary second derivative by the target's
Hasse-scaled curvature is an invertible coordinate rescaling and does not
change any rank.

## Exact L=10 comparison

The full source has 11,178 columns. The published local bound is 1,207 per
node, hence nominal source margin `11178 - 9*1207 = +315`.

```text
tangent   contact rows/rank/nullity   boundary gain at X=9
deg 4     14535 / 10861 / 317         3
deg 5     14535 / 10863 / 315         4
```

In the explicit order

```text
selected low, remaining S, R^2, R^3, remaining S R,
```

both receipts are injective through `R^2`. The first degree-four kernel and
gains 1--2 occur at `X^(28..29) Y^4 R^3 Z`; gain 3 first occurs at
`X^18 Y^4 R^3 Z^2`, and gain 4 never occurs. For degree five, the first
kernel and gains 1--4 are the four consecutive columns

```text
X^(21..24) Y^4 R^3 Z^2.
```

Thus increasing tangent degree from four to five shifts the first live
passive seed by one (`z=1` to `z=2`), but the observed law is not
`z=deg Q`. These are `R^3` relations, before the final `S R` group; first is
relative to the stated source order, not an order-independent minimality.

Exact receipts:

```text
deg4 canonical 0641bf2b649d3ee94f6a615ae74908f39edd6ecc52790f51f1b7feb96de50b2a
  runtime 306.890 s; peak RSS 2,266,120 KiB
deg5 canonical 3ceac6780cf176b7f8f711242940d0d41d021e5d0337a78af9f980374916f7b9
  runtime 305.997 s; peak RSS 2,267,040 KiB
```

## Degree-four function-field audit

The rank-three degree-four result is not an accident at `X=9`. Reusing one
contact RREF, the exact kernel-normal ranks at `X=9,10,11` are all three, and
the respective tangent jets `(Q,Q',Q'',1)` annihilate all 317 kernel normals.
More strongly, every canonical kernel relation's tangent contraction is the
zero polynomial. Raw contractions have degree at most 48, exactly
`deg Lambda_G^m`; there are zero nonzero residual contractions. A rank-three
specialization supplies the lower bound, so the normal image over
`F_101(X)` has exact rank three.

```text
canonical 19a7a7e22e9535a19dfcbf4db91b012a81083601a2d7b69ca13647d51e15f41d
runtime 305.498 s; peak RSS 2,282,148 KiB
script SHA-256 9e354830b86f2004727d873cafd4759f246dd865c0101b79ed7f5d00ebe50393
```

At `X=9`, the three first independent normal vectors are

```text
(28,73,24,54), (31,68,19,13), (43,73,71,82).
```

Their unique annihilator is `(97,88,63,1)`, exactly
`(Q(9),Q'(9),Q''(9),1)` for `Q=X^4`.

## Essential scope correction / STOP

Despite positive nominal margin, `L=10<U=12`: the actual source omits two
passive layers, including the terminal active face. The target and the earlier
L16 capacity-positive control both have `L>=U`. Therefore the degree-four
function-field RED is rigorous for the *passively truncated* source but does
not refute the target-like full source.

The controlled cap ladder uses the same receipt generated at `L=10` while
changing only source support. Although `L=11` still omits the terminal
active-12 face, it already restores boundary gain four. Thus the terminal
face is not necessary in this receipt: one additional passive layer is the
sharp tested repair. `L=12` remains the first full-active-face confirmation.
Do not infer that target tangent degree demands passive seed `deg Q`, that
positive margin alone suffices, or that the complete target source leaves the
tangent-jet line.

The exact source-difference ledger is:

```text
L=10 -> L=11: +1,961 columns, including 101 new active=11,z=0 columns;
L=11 -> L=12: +2,044 columns, including  83 new active=12,z=0 columns.
```

Inside the terminal active-12 face, the two highest-derivative candidate
connectors are the 15 columns `X^(0..14) Y^9 R^3` and the 15 columns
`X^(0..14) Y^10 R S`. The L11 result proves that neither these 30 nor the
other 53 terminal-face columns are required in this receipt.

## Controlled L11 repair

Holding every receipt datum fixed and changing only the source cap to `L=11`
gives:

```text
source/local bound/margin = 13,139 / 1,369 / +818
contact rows/rank/nullity = 16,560 / 12,321 / 818
boundary gain at X=9     = 4
```

The exact ordered filtration is:

```text
stage                    columns   rank   nullity   gain
selected low               7,696   7,696       0       0
+ remaining S              7,776   7,776       0       0
+ R^2                      9,701   9,486     215       3
+ R^3                     11,231  10,710     521       4
+ remaining S R           13,139  12,321     818       4
```

Gains 1--3 first appear at the consecutive last columns
`X^(21..23) Y^5 R^2 Z^2`; gain 4 first appears at `X^30 Y^2 R^3 Z`.
These monomials themselves fit at L10; their new relations use columns added
by the L11 scaffold. The precise statement is therefore relative, not that a
four-monomial standalone family suffices.

In this order the first three gains are at source columns 9,406--9,408 and
the fourth is at column 10,458 (the 757th of 1,530 `R^3` columns). Therefore
the smallest currently certified natural prefix with gain four has 10,458
columns and omits the final 773 `R^3` columns and all 1,908 remaining `S R`
columns. Its contact rank/nullity was not retained and is deliberately left
unspecified; only its gain-four certificate is claimed.

```text
canonical 3edf20e727c39162449370f49db91dafde4f8e473b68d7ddaa727524406f8311
runtime 419.810 s; peak RSS 3,147,804 KiB
```

This cap ladder falsifies the tempting `z=deg Q` transport: degree-four
tangent badness is detected with passive seeds at most two once the one-layer
scaffold is present. What must be globalized is a rank-adaptive passive-layer
connection, not a seed tower reaching the tangent polynomial's degree.

### Exact active-face versus passive-reach ablation

The 1,961 columns added from L10 to L11 split disjointly into:

```text
101  new active-total=11, z=0 face columns;
1860 extensions of the passive seed reach on existing active shapes.
```

Adjoining each part separately to the complete L10 source gives:

```text
addition                 columns   contact rank   nullity   gain
active11,z0 only          11,279        10,962       317      3
other passive reach only  13,038        12,321       717      4
complete L11              13,139        12,321       818      4
```

Every active-face column is independent modulo L10, so the active-only kernel
and normal image are unchanged. Conversely, passive reach alone attains the
same contact rank and gain as complete L11; after that scaffold is present,
all 101 active-face columns add only kernel dimension. Therefore the causal
verdict is exact: **passive reach is sufficient; the new active face is
neither sufficient nor necessary.**

In the passive-only order, the first relation whose last column is newly
added is column 9,420, `X^25 Y^5 R^2 Z^4`, and it raises gain from zero to
one. The fourth gain appears at column 10,394, `X^31 Y^2 R^3 Z`, with normal
`(22,45,87,4)`. The last monomial was already L10-legal; its relation depends
on the earlier passive scaffold. This is relation provenance, not a claim
that either monomial works alone.

```text
active-only canonical
  8ca8f013cc7429531e205fc41f14af64439365f9d066f826d52e5a328c52af47
  runtime 342.348 s; peak RSS 2,453,936 KiB
passive-only canonical
  1a0961460552946d161c16c078bb33f5ac1006134f2db6467db66877adef1b1c
  runtime 410.392 s; peak RSS 3,108,140 KiB
ablation script SHA-256
  f116bae257de2b63b72a246c2ef32b001b5d3787e1c464e125c89f53cf1ddc46
```

## Controlled L12 full-face confirmation

Holding the receipt fixed and restoring `L=U=12` gives:

```text
source/local bound/margin = 15,183 / 1,531 / +1,404
contact rows/rank/nullity = 18,585 / 13,779 / 1,404
boundary gain at X=9     = 4
```

The source ordering now closes substantially earlier:

```text
stage                    columns    rank   nullity   gain
selected low               8,756   8,726       30      2
+ remaining S              8,910   8,727      183      4
+ R^2                     11,154  10,581      573      4
+ R^3                     12,969  11,976      993      4
+ remaining S R           15,183  13,779    1,404      4
```

Gains 1--2 first appear at columns 5,977--5,978, ending in
`X^15 Y^10 R` and `Y^10 R Z`. Gains 3--4 first appear at columns
8,758--8,759, ending in `X^(1..2) Y^8 S Z^2`. Hence the smallest certified
natural prefix in this run has 8,759 columns and already has gain four. Since
one specialization has rank four, the normal image over `F_101(X)` also has
rank four.

```text
canonical c2f8672b6f7dda5799184b2cc72dec9f041cd1217a8925f9e4277a19b3895ca0
runtime 614.040 s; peak RSS 4,094,856 KiB
```

The same-receipt ladder is therefore exact and monotone at the normal-map
level:

```text
L=10: function-field gain 3;
L=11: gain 4 before the S R group;
L=12: gain 4 inside raw {1,R,S}.
```

This is the strongest finite mechanism conclusion: one extra passive layer,
not the terminal active face and not a seed tower of length `deg Q`, repairs
the minimal bad tangent. The smallest successful family is nevertheless a
large relative prefix, so the universal target proof must construct the
corresponding relative repairs from the target-tapered source. The axiom-clean
rank-adaptive endpoint is
`K0LineThenKill6900.normal_surjective_of_packet_separating_relative_family`;
the exact remaining hypothesis is that the literal m47 full-source/passive-
connection staircase separates every packet-compatible conormal. These
finite ranks do not prove that hypothesis.

## Reproduction

```text
python3 .experiments/k0_degree4_degree5_full_sr_attribution_6900.py \
  --tangent-degree 4 --passive-cap 10 --receipt-passive-cap 10
python3 .experiments/k0_degree4_degree5_full_sr_attribution_6900.py \
  --tangent-degree 4 --passive-cap 11 --receipt-passive-cap 10
python3 .experiments/k0_degree4_degree5_full_sr_attribution_6900.py \
  --tangent-degree 4 --passive-cap 12 --receipt-passive-cap 10
python3 .experiments/k0_degree4_degree5_full_sr_attribution_6900.py \
  --tangent-degree 5 --passive-cap 10 --receipt-passive-cap 10
python3 .experiments/k0_degree4_function_field_audit_6900.py
python3 .experiments/k0_l11_active_face_vs_passive_reach_6900.py \
  --support-mode active11_z0
python3 .experiments/k0_l11_active_face_vs_passive_reach_6900.py \
  --support-mode other_l11
```

The generalized cap-ladder script currently has SHA-256
`4a6d53f337406b97692050781c541ebb8d74cf40eced7b914fa8a530efabbcd8`;
the function-field script hash is recorded above. All large runs were exact,
sequential within each worker, and protected by a 4.2 GB address-space cap.
