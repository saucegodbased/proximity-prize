# k=0 target-ratio passive product-rule gate

Date: 2026-09-14 UTC. Scope: lower-6900 finite mechanism audit only. This
changes no production file, score, candidate, or submission.

## Verdict

**RED for transport of the m8 passive-seed repair as a causal
rank-three-to-four mechanism.** It is not RED for the desired rank-four
conclusion: both target-ratio controls already have boundary-gradient rank
four before the added passive layer.

The exact obstruction taxonomy is:

```text
old rank three                         FAIL: old rank is already four
residual lambda_Z nonzero              N/A: no residual conormal exists
old-kernel boundary-value rank         FAIL: identically zero in both cases
all complete-L7 Z shifts source-legal  PASS
new passive relative boundary quotient rank  zero
```

Thus the finite m8 story does not merely retune in these chambers.  There is
no missing fourth direction for the product rule to repair, and direct
`Z * old-kernel` witnesses have zero boundary gradient.  If the target proof
ever reaches a genuine rank-three stage, these controls provide no evidence
that a direct old-kernel shift supplies its fourth normal.  Such a proof must
establish either nonzero old-kernel boundary value in the actual target
stratum or a genuinely relative `d_new - p_old` connecting map.

## Faithful cap comparison

The executable is

```text
.experiments/k0_target_ratio_passive_product_rule_gate_6900.py
```

It reuses the deterministic constant-`T` receipts from
`k0_target_ratio_constant_t_gate_6900.py`:

```text
field F_101
(n,w,g,B,s,U,L,k,n0) = (11,5,8,2,1,8,8,0,1)
m = 5 (exact ratio) or 6 (ceiling)
Q = binomial(X,6)
errors have equal nonzero value/direction mismatch
```

For each `m`, three nested literal sources are used:

1. the complete `L=7` source;
2. that source plus the newly legal active-total-eight, `Z=0` face; and
3. the complete `L=8` source, obtained from stage 2 by adjoining only the
   positive-`Z`, total-eight frontier.

Stage 2 is the largest natural subsource of complete `L=8` for which the last
transition changes only passive reach.  This avoids blaming a result on the
simultaneously exposed active face.

The exact contact results are:

| profile | L7 columns | active face | pre-passive columns | passive frontier | L8 columns | contact rank/nullity: L7 | pre-passive | L8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| m5 | 3001 | 5 | 3006 | 598 | 3604 | 2901 / 100 | 2906 / 100 | 3418 / 186 |
| m6 | 3905 | 37 | 3942 | 822 | 4764 | 3867 / 38 | 3904 / 38 | 4635 / 129 |

The five and 37 active-face columns are contact pivots: they change rank but
not nullity.  The passive frontier creates 86 and 91 additional compatible
coefficient directions, respectively.

At each fresh boundary point `X=11,12,13`, however, the contact-kernel
boundary-gradient ranks are

```text
                 L7   pre-passive   L8
m5                4        4         4
m6                4        4         4
```

Consequently the intrinsic boundary connecting map for the isolated
pre-passive-to-full transition has quotient rank zero in both profiles.  The
86/91 new contact-compatible coefficient directions land inside the boundary
image already supplied by the old kernel.

## Direct passive product rule

Every complete-L7 monomial shifts legally by one `Z` into complete `L=8`.
The shift counts split as

```text
                    shift stays in L7   shift enters new passive frontier
m5                          2403                         598
m6                          3083                         822
```

For every exact basis vector `f` of the L7 contact kernel, the executable
re-expands all shifted monomials and verifies

```text
C(Z*f) = 0
grad(Z*f) = gamma * grad(f) + f(boundary) * e_Z.
```

Here `gamma=0`.  More decisively, the restriction of every old contact-kernel
relation to the candidate graph is the zero **polynomial**, not merely zero
at the three tested boundary points.  The exact map ranks on the old kernel
are therefore

```text
profile   gradient rank   value rank   [gradient; value] rank
m5              4             0                  4
m6              4             0                  4
```

The script verifies the polynomial statement by composing the full kernel
basis with the literal candidate-graph value polynomials.  All 100 m5 and 38
m6 outputs are zero.  In this zero-candidate, zero-seed receipt only the
pure-`X` strip can contribute to value.  Its strict widths are `m*g=40` and
`48`, matching the agreement multiplicity count, which explains the exact
zero by the root-count boundary.

It follows that the direct shifted boundary image has rank zero in both
profiles.  Source legality is not the failure.  `lambda_Z=0` is not the
failure either: there is no compatible conormal at all once the old image is
already four-dimensional.  The two independent reasons the m8 mechanism
does not transport are (i) lack of an old rank-three image and (ii) zero
old-kernel value.

The larger pre-passive source is deliberately not called uniformly
shift-closed: its new active-total-eight, `Z=0` face would shift outside
`L=8`.  All product-rule claims above use the complete-L7 shift-closed source.

## Relative-map control

The executable does not stop at the failed direct shifts.  For each nested
transition it computes the full new contact kernel, projects it to the new
source coefficients, and then maps its boundary gradients modulo the old
kernel-boundary image.  Exact rank-nullity checks give:

```text
profile  compatible new coefficient dimension  boundary quotient rank
m5                         86                              0
m6                         91                              0
```

This is the coordinate-free `d_new - p_old` control requested after a direct
shift failure.  A nonzero relative repair is not hidden by the zero direct
shift; in these two chambers its target quotient is already zero because the
old image is surjective.

## Reproduction and scope

```bash
cd yukon-6900-work
PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_target_ratio_passive_product_rule_gate_6900.py
```

The script uses exact Flint finite-field matrices and installs a hard
`4,089,446,400`-byte address-space cap (3900 MiB).  The final replay peaked at
`1,304,944` KiB and took `133.061` seconds.  Its receipt hashes are

```text
canonical SHA-256  8293a4fb57e68b977aa4f55c8ff0579faf42ab227196943950db98c363efd610
script SHA-256     8d3bc1e78b8f6c51dd63fdeacb29f994fd96621a2f134de134c8cae00edb8345
```

This is a deterministic adversarial control, not a target-uniform theorem.
Its honest consequence is narrow: the m8 passive-shift repair cannot be cited
as a target-ratio mechanism without a theorem producing a rank-three old
stage and a nonzero old-kernel value (or a separate nonzero relative
connecting map) in the actual target source.
