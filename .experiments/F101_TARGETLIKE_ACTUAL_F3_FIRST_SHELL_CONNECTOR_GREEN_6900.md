# Targetlike actual-F3 first-shell connector: exact GREEN

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This is an exact
finite-field discriminator and a target theorem specification, not a
Full187 proof, score, candidate, or submission.

## Decision

There is a sharply smaller and more faithful mechanism than the failed
two-sided bicovariant Popov rectangle. In the primary `F_101` chamber with
the targetlike nonmatched error direction, the complete grade-`J` prefix
together with exactly the raw first-shell derivative shapes

```text
{(r,s)=(0,0), (r,s)=(1,0)}
```

lifts the actual `F3 = B (Y-Z q_H)` and, simultaneously, each of
`F0,F1,F2,F3`. This is the unique inclusion-minimal closing subset among
the three available shapes `(0,0),(1,0),(0,1)`.

The word **raw** is essential. Each single shell group is RED. The pairs
`{pure,S}` and `{R,S}` are RED. Even the three canonical centered carriers

```text
(Y-QZ)^4 Z^3,
R (Y-QZ)^4 Z^2,
S (Y-QZ)^4 Z^2
```

together leave joint packet defect four. Closure comes from
coefficient-sensitive combinations *inside* the complete pure and slope
shell groups, whose contact errors cancel jointly with prefix columns. It
does not come from adding another already-contact-zero factor.

This identifies why the earlier factorized ansatz missed by rank one: it
required every correction generator to lie individually in the complete
contact kernel. The successful mechanism instead uses the connecting map of
the coupled contact-and-boundary complex. Intermediate raw columns have
contact; only the assembled representative has zero contact.

## Exact faithful chamber

The executable receipt is
`f101_targetlike_actual_f3_connector_gate_6900.py`. It fixes

```text
F_101,
(N,w,g,m,D,s,t,J,L)=(11,5,8,4,32,1,1,6,10),
G={0,...,7}, E={8,9,10},
agreement direction Q=Xi_E^2,
error direction X^2,
F3=B(Y-Zq_H).
```

Thus the agreement word and the packet are unchanged from the successful
four-normal source experiment, while the error direction is the exact small
analogue of Full187's `X^81730`. The literal error-node offsets from `Q` are
`(64,81,100)`.

The script constructs every one of the 2,707 legal source monomials and the
literal all-node order-four contact columns, retaining the four polynomial
boundary coordinates in the same matrix. `build_case` rechecks the source
support, agreement contacts of every locator normal, the exact centered
shell support, and the contact row map. No pointwise replacement, rational
localization, arbitrary terminal `C`, or post-hoc source column is used.

Stable fingerprints and ranks are:

```text
source monomial-list sha256
  10d3c7e0cf398e5099bcc846cbbdc0c4e194a2f457c33d3da8ecedafe91f5526
coupled rows                         3174
complete source columns             2707
complete coupled rank               2586
grade <= J prefix columns/rank       1463 / 1463
packet quotient rank over prefix     4
prefix F0,F1,F2,F3 residue supports  50,72,94,53
```

Whole-grade staging is also sharp: all four packets have defect one through
grade six, and all four first become solvable at grade seven (`J+1`). The
grade-seven group has 311 columns and adds 298 ranks.

## Sharp shape ablations

Modulo the complete grade-six prefix:

| shell shapes | raw columns | individual defects F0..F3 | joint defect |
|---|---:|---|---:|
| pure | 119 | `(1,1,1,1)` | 4 |
| S | 99 | `(1,1,1,1)` | 4 |
| R | 93 | `(1,1,1,1)` | 4 |
| pure + S | 218 | `(1,1,1,1)` | 4 |
| R + S | 192 | `(1,1,1,1)` | 4 |
| **pure + R** | **212** | **`(0,0,0,0)`** | **0** |
| pure + R + S | 311 | `(0,0,0,0)` | 0 |

Therefore curvature is not needed in this chamber, and no single factor or
single shape explains the result. This agrees with the matched small
connector controls and improves the earlier arbitrary-error m6/m7/m8 result,
where all three shapes were necessary: the structured targetlike direction
`X^(|E|-1)` restores the two-shape mechanism.

## Explicit exact F3 representative

An exact FLINT nullspace extraction restricted to the 1,463 prefix columns
and the 212 pure-plus-slope shell columns gives:

```text
selected columns / rank / augmented nullity = 1675 / 1673 / 3
representative support                       = 1151
representative sha256
  91fe5c1963971bb2b5684681d07beb53fb36e42de28a1ae870b3887c7cf0e01e
used derivative shapes                       = pure:689, R:462
used grade-seven shell shapes                 = exactly pure and R
```

The script then literally re-sums all selected coupled columns and asserts
equality to the exact F3 boundary target. The re-evaluated result has zero
nonzero contact rows. Hence this is a coefficientwise witness, not only a
rank equality. Peak RSS was 213,092 KiB and runtime was 43.5 seconds, below
the declared 3 GiB cap.

Stable result sha256:

```text
06db4dbd0730dcdbce3653b9067d2a0d1bf131d80c63d0c9205043f4e4d080d6
```

## Safe103 and source legality

Every used monomial is selected from the literal complete source. The only
new shell shapes are `(0,0)` and `(1,0)`, both conservative103. In the F101
analogue there are nine terminal-face candidates and zero forbidden ones.

For Full187, the corresponding first shell has total grade `J+1=83`, far
below the terminal grade `L=2703`, so it is untouched by the 103 deletion.
After passive continuation by `Z^(L-J-1)`, the possible deleted-face endpoints
have shapes `(0,0)` and `(1,0)`, again conservative103. The previously audited
centered carriers are also source-legal for `Q=Xi_E^2`, with strict width
slack at least 885,989 for the slope carrier.

## Exact Full187 scaling ledger

The target analogue is not a 894-million-column calculation. It should be
represented as 165 polynomial coefficient channels:

```text
sum_(y=0)^82 A_y(X) Y^y Z^(83-y)
+ sum_(y=0)^81 B_y(X) R Y^y Z^(82-y).
```

The scalar column counts encoded by these channels are nevertheless exact.
With `D=60*180413=10824780` and `w=131071`, the raw legal windows contain

```text
pure:  sum_(y=0)^82 (D-w*y)             = 452,422,127
slope: sum_(y=0)^81 (D-(w-1)-w*y)       = 441,597,429
total                                           894,019,556.
```

This count explains why direct target Gaussian elimination is the wrong
scaling path. The small-chamber witness is dense in scalar coefficients but
low-state in derivative shapes and polynomial channels.

The older `7 x 7` shift rectangle has 14,327 semantic factor pairs and at
most 916,928 shifted columns, but its targetlike-error analogue is exactly
RED by one. It should not be enlarged. The present connecting-map route
supersedes that rectangle rather than certifying it.

## What target proof would certify 6900

A scalable proof now has a specific, narrow obligation:

1. Identify the complete grade-at-most-82 sector with a saturated filtered
   `F[X]` module for the literal contact map.
2. Compute the connecting map on the two first-shell polynomial families
   `A_y,B_y` above and prove that its image contains the four exact locator
   packet classes for agreement word `Xi_E^2` and error direction `X^81730`.
3. Synthesize the preimage by polynomial recurrence/Popov reduction, while
   preserving each varying width bound.
4. Continue passively to grade 2703 and use conservative103 only at the final
   deleted face.

The informal saturated-contact lemma in GitHub discussion comment 18427358
is relevant only if its complete-sector and filtration hypotheses can be
proved for this literal pure-plus-slope sector. Its distinct top-monomial
argument may establish step 1; it does not by itself establish the connecting
surjectivity in step 2.

The remaining uncertainty is therefore no longer “which derivative shapes”
or “does targetlike F3 lift in the faithful chamber.” It is the uniform
filtered connecting-map theorem over `F[X]`, including the target's strongly
nonmatched degree balance `g-(e+w)=-32389`. A ratio-faithful finite chamber is
still required before calling the target theorem likely.

