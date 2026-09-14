# Nonzero-q_H safe-terminal four-packet gate

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, score, and radius files are unchanged.

## Verdict

**GREEN** in the predeclared nearly dimension-tight nonzero-node chamber.
After the exact strong safe/unsafe terminal deletion, both of the relevant
tests pass:

```text
boundary rank on the complete-contact kernel over F_1009(X)    4 / 4
coefficientwise defects of F0,F1,F2,F3                     0,0,0,0
joint coefficientwise four-packet defect                         0
```

Unlike the previous safe-terminal controls, this test has genuinely
nonzero, nonconstant `q_H = 1+X`.  Consequently its exact fourth packet

```text
F3 = B (Y - P - Z q_H)
```

contains the hard `-B Z q_H` term.  The earlier green answer was therefore
not an artifact of choosing a retained-bad direction that vanished on all
anchors and made `q_H=0`.

This is strong finite structural evidence.  It is **not** the Full187 target
recurrence theorem and does not by itself imply `ProtocolClaim6900`.

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

## 3. Literal matrix results

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

Peak RSS for the full run was 1,308,600 KiB under a hard 4 GiB address-space
limit.

## 4. What this resolves, and what remains

This test resolves one concrete uncertainty in favor of the safe-terminal
route:

```text
old ambiguity:
  packet containment might pass only because q_H=0 and F3 has no -BZq_H

result:
  false in this discriminator; q_H=1+X and both gates remain green
```

It does not resolve the main remaining uniformity problem.  A target proof
must still propagate the four atomic packet columns through the full 2,703
passive grades and all target contact-weight transitions, while respecting
the safe-103 source restriction.  The appropriate next theorem is therefore
packet-preserving triangular/confluent elimination, not blanket contact
surjectivity and not a standalone pure-`Z` correction theorem.

## 5. Reproduction

```text
prlimit --as=4294967296 --cpu=900 -- \
  python3 -B \
  .experiments/nonzero_qh_safe_packet_gate_6900.py
```

The run uses no `decide`, `native_decide`, production module, or submission
artifact.
