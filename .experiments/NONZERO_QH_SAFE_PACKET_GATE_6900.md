# Nonzero-q_H safe-terminal four-packet gate

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

The first specialization is **GREEN**, but the target-relevant one-offset
robustness replay is **RED**.  The green specialization has all error values
on the same degree-`w+1` polynomial as the agreements.  Keeping every source
parameter, agreement value, packet, and deleted shape fixed while applying
predeclared nonzero offsets only at the four error nodes changes the answer to

```text
boundary rank on the complete-contact kernel over F_1009(X)    3 / 4
coefficientwise defects of F0,F1,F2,F3                     1,1,1,1
joint coefficientwise four-packet defect                         4
```

Therefore the safe-terminal packet theorem, in its current unrestricted-error
form, is false even in this small retained-bad control.  The earlier green
answer was partly a global-polynomial error specialization and cannot be used
as evidence for arbitrary error values.

For reference, before perturbing the error values, both tests pass:

```text
boundary rank on the complete-contact kernel over F_1009(X)    4 / 4
coefficientwise defects of F0,F1,F2,F3                     0,0,0,0
joint coefficientwise four-packet defect                         0
```

Unlike the previous safe-terminal controls, both replays have genuinely
nonzero, nonconstant `q_H = 1+X`.  Consequently its exact fourth packet

```text
F3 = B (Y - P - Z q_H)
```

contains the hard `-B Z q_H` term.  This rules out `q_H=0` as the explanation
for failure, but the error-offset replay reveals a different degeneracy in the
green case.

This is a finite structural falsifier.  It is **not** the Full187 target
recurrence theorem and does not imply `ProtocolClaim6900`.

## 1. Predeclared control and retained badness

Before any matrix rank was computed, the control was fixed as

```text
F_1009
(n,w,g,m,D,q,t,J,L) = (18,8,14,6,84,4,1,5,5)
domain               = {1,...,18}
agreement set G      = {1,...,14}
anchor set H         = {1,...,9}
q_H                  = 1 + X
Q_G                  = q_H + Lambda_H
```

Every domain node is nonzero.  Moreover, every sampled value `Q_G(a)` is
nonzero, so the result is not caused by a zero direction at a convenient
point.  On `H`, interpolation recovers exactly `q_H=1+X`, while

```text
Q_G - q_H = Lambda_H,
deg(Q_G-q_H) = 9 > w = 8.
```

Thus `Q_G` is genuinely retained-bad: no polynomial of degree at most `w`
can agree with it on all of `G`.  This is the exact independence mechanism
used by the fourth packet, with a nonzero residual `Z` coefficient.

## 2. Exact strong safe-shell restriction

The safe/unsafe split is recomputed from the same strong affine-error
criterion as the target safe-103 proposal, using required margin `n-g=4`.
It is not selected from the observed matrix ranks:

```text
safe terminal shapes
  (0,0),(1,0),(2,0),(3,0),(4,0),(0,1),(1,1),(2,1)
unsafe terminal shape
  (3,1)
unsafe terminal coefficient width                              49
```

Only the unsafe shape in the final combined terminal shell
`y+r+s=J`, `y+r+s+z=L` is deleted.  Every lower active grade, lower passive
grade, and safe terminal shape remains.

The exact dimension ledger is intentionally tight:

```text
full Euler surplus                                              54
restricted surplus after deleting the unsafe terminal width      5
restricted surplus after reserving four packet conditions         1
```

A green answer therefore cannot be dismissed as a consequence of a large
unused source surplus.

## 3. Literal baseline matrix results

The executable constructs the complete order-two translated contact matrix
at all 18 nodes and projects each local quotient to the exact reachable
one-node contact image.  The restricted matrix has

```text
source dimension / canonical contact dimension             5711 / 5706
restricted contact rank / nullity / defect             5512 / 199 / 194
```

The large blanket contact defect is expected and reconfirms that blanket
surjectivity is the wrong theorem.  The packet-specific maps give:

```text
fraction-field boundary rank, full source / contact kernel       4 / 4
boundary coefficient positions / kernel-image rank             315 / 21
F0,F1,F2,F3 coefficientwise defects                           0,0,0,0
joint coefficientwise defect                                         0
error-contact support sizes                              92,96,106,96
```

All four exact normals are verified to lie in the restricted source.  Their
literal contacts vanish at every agreement node and are nonzero on the error
set.  Thus the direct bordered-rank test says that the complete-contact
kernel has simultaneous coefficientwise representatives for the exact four
packet columns, not merely rational representatives after extending scalars
to `F_1009(X)`.

Peak RSS for the baseline run was 1,308,600 KiB under a hard 4 GiB
address-space limit.

## 4. Frozen arbitrary-error replay

The robustness replay changes only the actual `U1` values at the four error
nodes.  The offsets were predeclared as

```text
error nodes                  15,16,17,18
offsets                      37,74,111,148
resulting actual U1 values   768,365,467,633
```

They are all nonzero.  Agreement values remain exactly the evaluations of
`Q_G=q_H+Lambda_H`, so `q_H=1+X`, the retained-bad proof, the four packet
polynomials, the safe/unsafe split, and every source dimension are unchanged.
Only the error translations in the literal contact matrix change.

The exact replay ranks are

```text
restricted contact rank / nullity / defect             5602 / 109 / 104
fraction-field boundary rank, full source / kernel             4 / 3
boundary coefficient positions / kernel-image rank           315 / 5
F0,F1,F2,F3 coefficientwise defects                         1,1,1,1
joint coefficientwise defect                                       4
```

Thus both the weak fraction-field CS4 gate and the stronger direct packet gate
fail.  In particular, this is not a borderline choice between rational and
polynomial representatives: every named packet is individually absent from
the coefficientwise image.  Peak RSS was 1,308,652 KiB.

## 5. What this resolves, and what remains

The paired test resolves two concrete uncertainties:

```text
q_H ambiguity:
  q_H=1+X is compatible with a green specialization

arbitrary-error ambiguity:
  RED; the same result does not survive independent error U1 values
```

Any surviving target route now needs additional source directions or a
stronger structured relation on error values.  Since the benchmark permits
arbitrary received words, the latter is unavailable.  The immediate useful
question is which omitted terminal/lower-grade connector restores the four
packets; one should not begin formalizing packet-preserving confluence until
that missing direction is identified.

### Bounded augmentation screen

Two predeclared augmentations were tested against the same offset-error
matrix.  Here `weak rank` is the boundary rank on the complete-contact kernel
over `F_1009(X)`.

| source | columns / contact rows | contact rank / nullity | weak rank | coefficient image rank | packet defects / joint |
|---|---:|---:|---:|---:|---:|
| safe restricted | 5711 / 5706 | 5602 / 109 | 3 | 5 | `(1,1,1,1)` / 4 |
| restore all 49 unsafe `(3,1)` columns | 5760 / 5706 | 5651 / 109 | 3 | 5 | `(1,1,1,1)` / 4 |
| add next raw `{00,10,01}` shell groups | 6710 / 7524 | 6548 / 162 | 3 | 15 | `(0,1,1,1)` / 3 |

The unsafe face is contact-injective modulo the restricted source and adds no
kernel connector.  The raw triple supplies exactly the `F0` class but not
`F1,F2,F3`.  This chamber is under-scaled: `J=5<m=6`, so it omits part of the
full centered multiplicity-six head.  Accordingly this last red row is a
diagnosis of the small chamber, not a target-scaled falsification.  The
separate `J=8` maximal-degree control in
`F101_M6_HIGHDEGREE_Q_RAW_SHELL_GATE_6900.md` is the relevant connector test
and is green exactly when all three raw groups are combined.

## 6. Reproduction

```text
prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/nonzero_qh_safe_packet_gate_6900.py

prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/nonzero_qh_safe_packet_gate_6900.py --offset-errors

prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/nonzero_qh_safe_packet_gate_6900.py \
  --offset-errors --restore-unsafe

prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/nonzero_qh_safe_packet_gate_6900.py \
  --offset-errors --raw-yrs-shell
```

The run uses no `decide`, `native_decide`, production module, or submission
artifact.
