# K0 low-head four-row adversarial sweep

## Verdict

The target theorem must concern the **four terminal boundary rows directly**.
It must not assert that the entire fresh-node low-head contact probe is
independent of the old heads.

Exact arithmetic over `F_101` gives both sides of this distinction:

- all ten retained-bad test instances give rank gain exactly `4` after the
  four boundary rows are appended to the old low-head rows;
- four near-capacity instances refute independence of the whole fresh probe,
  with defects from `78` to `209`;
- every source monomial in every case also passes the coefficientwise contact
  factorization check from the fresh probe to the four boundary rows.

Thus a proof attempt at full local CRT is solving a false and unnecessary
statement.  The surviving target is a four-dimensional quotient statement:
the boundary map restricted to the kernel of the old-head map is onto.

## Reproduction

Run:

```text
python3 .experiments/k0_low_head_four_row_adversarial_sweep_6900.py
```

The script imposes an address-space cap of `4,200,000,000` bytes and computes
all ranks exactly with FLINT `nmod_mat`; it uses no floating-point rank tests.
The final run took `127.030 s` and peaked at `1,381,424 KiB` RSS.

- canonical result SHA-256:
  `f4f1a54afc0c8979bcabfe1f6455f82bd55803435353fe002aa2cbe891c7b3dd`
- script SHA-256:
  `6c6b191dfdd49edfabc5d1f645392976af13e1a1d23704bde30553e6ca394607`

The four load-bearing near-capacity receipts are embedded as assertions, so
the program fails if either the full-probe counterexample or the four-row
survival is lost.

## Exact near-capacity ranks

Write `r_old`, `r_probe`, and `r_joint` for the ranks of the old heads, fresh
probe, and their tagged joint map.  `probe defect` is
`r_probe - (r_joint-r_old)`.  The last two columns concern only the four raw
boundary outputs.

| case | source | nominal margin | `r_old` | `r_probe` | `r_joint` | probe defect | old+four | four gain |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| m7 n15 structured | 3280 | 85 | 2870 | 213 | 3005 | 78 | 2874 | 4 |
| m7 n15 adversarial | 3280 | 85 | 3195 | 213 | 3280 | 128 | 3199 | 4 |
| m8 n12 structured | 3860 | 104 | 3530 | 313 | 3698 | 145 | 3534 | 4 |
| m8 n12 adversarial | 3860 | 104 | 3756 | 313 | 3860 | 209 | 3760 | 4 |

The adversarial receipts vary the agreement set and use an arbitrary
off-agreement direction, alternating error values, and a spike tangent.  The
structured receipts use a polynomial off-agreement direction and common error
values.  In all cases the agreement tangent has degree strictly above `w` and
strictly below `g`, as required by retained badness.

## Roomy controls

For m7 at n5/n6 the old-plus-probe gain is the full probe rank `213`; for m8
at n5/n6 it is `313`.  Their four-row gains are also exactly `4`.  This is why
small tests alone misleadingly suggested a full-probe theorem: the stronger
claim first breaks only when the old heads nearly fill the source.

## Formal connection and exact scope

`K0LowHeadContactBoundaryReadout6900.lean` proves that literal contact already
recovers the four boundary derivatives:

```text
Q_Y = [eps^3] (partial_T contact)
Q_R = (partial_R contact)|eps=0
Q_S = (partial_S contact)|eps=0
Q_Z = (partial_Z contact)|eps=0 - u1 * Q_Y.
```

It also gives an explicit section of this four-scalar readout.  No augmented
ambient jet is required when `m >= 7`; the target `m=47` is safely in scope.
This finite sweep does **not** prove that the four rows are independent for the
target, and positive dimension margin is not used as a rank proof.  What it
does prove is methodological: the smallest plausible missing result is direct
four-row dual separation (equivalently a rank-three base plus one nonzero
syndrome), not surjectivity of all fresh contact coefficients and not an
all-node X-only locator.

