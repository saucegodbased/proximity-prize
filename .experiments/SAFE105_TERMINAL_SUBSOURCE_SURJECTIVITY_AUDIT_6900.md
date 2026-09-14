# Safe-105 terminal subsource: exact ledger and first surjectivity audit

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

The 105-shape terminal restriction has ample target Euler room, but **does
not support a proof by blanket surjectivity of contact on zero boundary**.
That replacement theorem is already false in a literal nonzero-node,
retained-bad control with the analogous safe polytope and positive dimension
surplus.

The same control is nevertheless **GREEN for the weaker four-boundary gate
over the fraction field**: after deleting its unsafe terminal shape, the
complete contact kernel has boundary rank four over `F_1009(X)`.  Thus the
new restriction is not killed; it narrows the honest next gate to direct
coefficientwise containment of the four named agreement packets.  The
fraction-field rank alone does not prove that stronger strict-window
containment.

## 1. Independently recomputed target ledger

For

```text
(n,w,g,m,D,q,t,J,L)
  =(262144,131071,180413,60,10824780,21,10,82,2703),
```

the exact `q=0` low-`T` corner criterion gives

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

Applying the same corner inequalities, rather than hand-selecting a face,
gives

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

## 3. Scope and next decisive gate

The GREEN fact is fraction-field boundary rank.  It permits rational-function
linear combinations of complete-contact kernel vectors.  It does **not** yet
show that the four named agreement-side sections `F0,F1,F2,F3` admit
coefficientwise corrections inside every strict source window.

The next discriminator must therefore construct those four packet columns
explicitly and check joint containment in the error-contact image of

```text
ker(agreement contact) intersect ker(boundary),
```

with the 105-shape terminal restriction imposed.  For the fourth packet one
must use the retained-bad exact-cardinality row

```text
B  = Lambda_H^(m-1) Lambda_(G\H)^m,
F3 = B (Y - Z q_H),
```

where `|H|=w+1` and `q_H` interpolates `u1` on `H`.  Zero-containing toy
domains are not admissible negative evidence for the target's residual-`Z`
mechanism.

## 4. Reproduction

```text
prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/safe_terminal_subsource_surjectivity_audit_6900.py --compact
```

Peak RSS in the recorded run was about 540 MiB.  The computation uses no
`decide`, `native_decide`, production module, or submission artifact.
