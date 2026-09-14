# Safe-105/103 terminal subsource: exact ledger and surjectivity audit

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

The original 105-shape agreement-Hermite restriction, and the corrected
103-shape arbitrary-error restriction, both have ample target Euler room.
Neither **supports a proof by blanket surjectivity of contact on zero
boundary**.  That replacement theorem is already false in a literal
nonzero-node, retained-bad control with the analogous strong safe polytope
and positive dimension surplus.

The same control is nevertheless **GREEN for both relevant four-packet
gates**.  After deleting its unsafe terminal shape, the complete contact
kernel has boundary rank four over `F_1009(X)`.  More strongly, its exact
coefficientwise boundary image jointly contains the four named agreement
packets `F0,F1,F2,F3`.  Thus the new restriction survives its first strongest
faithful finite discriminator.  This remains a finite control, not the target
recurrence theorem.

## 1. Independently recomputed target ledger

For

```text
(n,w,g,m,D,q,t,J,L)
  =(262144,131071,180413,60,10824780,21,10,82,2703),
```

the agreement-Hermite `q=0` low-`T` corner criterion gives

```text
all terminal derivative shapes                         187
safe shapes                                            105
unsafe shapes                                           82
safe iff                         r+s <= 16 and r+4s <= 33
```

The terminal coefficient-width ledger is

```text
safe width sum                                     8,081,883
unsafe width sum                                   6,312,464
full-source Euler surplus                          9,757,693
surplus after deleting unsafe terminal coordinates 3,445,229
surplus after four additional boundary rows         3,445,225
```

These figures are exact integer identities.  The last positive number is a
necessary room check, not a rank theorem.

For actual four-packet correction, the coefficient strip must retain
arbitrary values on all `n-g=81,731` error nodes.  Replacing the capacity
threshold `margin>=0` by the strong threshold `margin>=81,731` removes two
additional shapes, exactly `(1,8)` and `(5,7)`.  The live ledger is therefore

```text
strong affine-safe shapes                              103
strong affine-unsafe shapes                             84
strong safe width sum                            7,927,931
strong unsafe width sum                          6,466,416
restricted Euler surplus                         3,291,277
restricted surplus after four boundary rows       3,291,273
```

The executable reports both the 105 agreement-only ledger and this corrected
103-shape affine ledger so they cannot be conflated.

## 2. Faithful nonzero-node retained-bad control

The finite control is

```text
F_1009,
(n,w,g,m,D,q,t,J,L)=(22,10,17,4,68,3,1,5,5),
domain={1,...,22}, agreements={1,...,17}.
```

In particular, zero is excluded just as it is from the target NTT domain.
Take `u0=0` on agreements and `u0=1` on errors.  The retained-bad direction
is

```text
u1 = Lambda_{1,...,11}.
```

It has degree `w+1=11`, vanishes at the `w+1` anchors, and is nonzero at all
remaining domain nodes.  Hence it is genuinely not a degree-at-most-`w`
direction disguised as a hard case.

Applying the same **strong** corner inequalities with required margin
`n-g=5`, rather than hand-selecting a face, gives

```text
safe shapes    (0,0),(1,0),(2,0),(3,0),(0,1),(1,1)
unsafe shape   (2,1)
full Euler surplus                                      83
unsafe terminal width                                   22
restricted surplus                                      61
restricted surplus after four boundary rows             57
```

The executable builds the complete literal order-two translation matrix.  It
uses exactly the 164-dimensional image of the one-node capped contact map,
not the larger set of 178 raw quotient monomials.  A pivot-coordinate
projection is independently checked to have rank 164 at every one of the 22
nodes.

The exact ranks after deleting the unsafe terminal shape are

```text
source / canonical contact dimensions             3669 / 3608
unrestricted contact rank / defect                 3474 / 134
restricted contact rank / nullity / defect     3452 / 217 / 156
boundary rank of restricted contact kernel               4
contact rank on fraction-field zero boundary       3452 / 3608
```

For matrices `C` and `B(X)`, the identity

```text
rank(C | ker B) = rank C + rank(B | ker C) - rank B
```

therefore gives defect 156.  Positive surplus plus the safe-polytope
condition does not imply the blanket surjectivity statement.

On the other hand, `rank(B | ker C)=4`.  The script computes this exactly by
polynomial minors, not by sampling `X`.  Consequently the four-dimensional
boundary space is hit after extending scalars to `F_1009(X)`.  This is the
right kind of evidence for the actual four-normal objective and explains why
the much stronger blanket theorem should be discarded rather than treating
the restriction itself as red.

## 3. Direct coefficientwise four-packet gate

To remove the fraction-field ambiguity, the executable also builds the exact
agreement sections.  The first three are the standard centered locator
normals.  The fourth is

```text
B  = Lambda_H^(m-1) Lambda_(G\H)^m,
F3 = B (Y - Z q_H),
```

with `H={1,...,11}` and `q_H` the degree-at-most-`w` interpolant of `u1` on
`H`.  Here `q_H=0`, whereas `Q_G-q_H` has degree 11, so the fourth direction
is genuinely independent by retained badness.  All four rows are checked to
belong to the restricted source and to have literal zero contact at every
agreement node.

The coefficient boundary has 245 positions.  The restricted complete-contact
kernel maps to a 24-dimensional subspace of it.  Exact bordered ranks give

```text
individual defects (F0,F1,F2,F3) = (0,0,0,0)
joint four-column defect           = 0
error contact support sizes        = (65,70,85,70)
```

This is equivalent to simultaneous coefficientwise containment of the four
packet contacts in the error-contact image of

```text
ker(agreement contact) intersect ker(boundary),
```

for this finite control: subtract each complete-kernel representative from
its named agreement section.  It is strictly stronger than merely seeing
rank four after extending to `F_1009(X)`.

An independently parameterized second retained-bad control gives the same
answer:

```text
F_211, (n,w,g,m,D,q,t,J,L)=(10,4,7,5,35,4,1,7,7)
domain={1,...,10}, H={1,...,5}, u1=Lambda_H
strong safe/unsafe shapes                         8 / 1
restricted surplus after four boundary rows         174
restricted contact rank / target              4017 / 4090
fraction-field boundary rank                           4
coefficientwise individual defects             (0,0,0,0)
coefficientwise joint defect                            0
```

Thus two different mixed safe/unsafe chambers refute the blanket theorem but
support the exact atomic four-packet statement.

## 4. Scope and next decisive gate

The controls show that the strong safe-terminal restriction and the exact
fourth packet are mutually compatible.  They do not prove uniform target
coefficient propagation through 2,703 passive grades.  The remaining theorem
must orient the target transition recurrence while preserving the four atomic
packet columns.  In particular, one must keep the exact fourth row

```text
B  = Lambda_H^(m-1) Lambda_(G\H)^m,
F3 = B (Y - Z q_H),
```

where `|H|=w+1` and `q_H` interpolates `u1` on `H`.  Zero-containing toy
domains are not admissible negative evidence for the target's residual-`Z`
mechanism.

## 5. Reproduction

```text
prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/safe_terminal_subsource_surjectivity_audit_6900.py --compact
```

Peak RSS stays below the 4 GiB process cap.  The computation uses no
`decide`, `native_decide`, production module, or submission artifact.
