# k=0 flattened-contact sweep regression and one-spare-layer receipt

Date: 2026-09-15 UTC.  Scope: exact finite-field mechanism audit for the
lower-6900 k=0 source.  No production or submission file is changed.

## Headline

The old complete-contact and passive-face ranks survive, but for a subtler
reason than the first audit stated.  The compressed second-jet oracle is
conjugate to the accepted flattened contact map after the second-derivative
normalization.  Its **head filter was wrong**: it selected the free Taylor
index `q`, whereas the accepted epsilon order is `q+3E`.

After replaying every previously reported transition, defect, spare-layer,
and deep-passive control against the accepted flattened map:

```text
broad complete transition caps:          gain 4 in 30/36, gain 3 in 6/36
broad old+new-passive transition source: gain 4 in  6/36
one-spare defect bases:                   gain 4 in  0/7
one-spare old+positive-Z successor:       gain 4 in  7/7
preceding-cap accepted eps>=3 head:       gain 4 in  7/7
deep-passive complete controls:           gain 4 in  3/3
```

The first three head rows in the `7/7` line are **vacuous**: those controls
have `m=3`, so epsilon order at least three is empty.  The meaningful result
is therefore head gain four in **4/4 nonempty m4/m6 controls**, not a seven
case target analogue.

This is strong finite support for a one-spare-layer, head/tail proof pattern.
It is not a target-size rank theorem, and the source used in the `7/7`
successor line includes every newly legal positive-Z monomial, not merely the
raw `(R,S)=(0,0)` subface.

## 1. Exact accepted contact semantics

For a raw monomial in `(X,Y,R,S,Z)`, the checked local substitution is

```text
X |-> x + eps,
Y |-> u0(x) + u1(x) Z + eps R - eps^2 S + eps^3 T,
```

with rows

```text
(node, eps exponent, S exponent, T exponent, R exponent, Z exponent)
```

and truncation `eps exponent < m`.  The boundary graph is evaluated at

```text
(Y,R,S,Z) = (P, P', Hasse2(P), gamma) = (P,P',P''/2,gamma).
```

The earlier ordinary-`P''` boundary replay was stopped and discarded before
producing this receipt.

## 2. Why the compressed full ranks were nevertheless valid

The compressed oracle row `(q,E,V1,V2,Z)` maps to the formal row

```text
(eps=q+3E, S=V2, T=E, R=V1, Z).
```

For a raw column with S exponent `s_raw`, the exact coefficient identity is

```text
formal(row,column)
  = 2^(localS-s_raw) * compressed(row,column).
```

After column scaling by `2^(-s_raw)`, the boundary `Y/R/Z` rows agree and the
formal Hasse2-`S` boundary row is twice the compressed `S` row.  These are
invertible row/column scalings over every odd field in the sweep.  Thus full
contact and contact-plus-boundary ranks are conjugate.

The script checks this identity coefficientwise on all 771 source columns at
all six nodes of an m4 control: 4,626 node-columns total.  The correct head
condition in compressed coordinates is

```text
q + 3*E >= 3,
```

not a condition on `q` alone.  That is the actual regression fixed here.

## 3. Broad transition sweep

The 36 cases are six profiles times three deterministic data families times
the seed pair `gamma=0,5` (reduced in the stated field).  Candidate degree,
agreement set, retained-bad tangent shape, and off-agreement received
direction vary.  At the fixed off-domain boundary point `X=n`, the exact
histograms are

```text
complete cap:       gain 3: 6     gain 4: 30
old+passive source: gain 0:12     gain 2: 6
                    gain 3:12     gain 4:  6
```

These exactly reproduce the earlier compressed full/passive histograms, as
the conjugacy predicts.  The six complete gain-three cases remain the three
`m=3` random-mid-spike controls and their paired seed translations.  They do
not challenge the target head statement because `m=3` has no epsilon orders
at least three.

## 4. One-spare-layer and corrected head details

```text
case                    base gain   L+1 positive-Z gain   preceding head
m3 n9 spike                 3                 4           vacuous, gain 4
m3 n10 spike                3                 4           vacuous, gain 4
m3 n11 spike                3                 4           vacuous, gain 4
m4 n8 minimal               3                 4           710/336/336/374, gain 4
m4 n9 minimal               3                 4           798/378/378/420, gain 4
m4 n10 minimal              1                 4           886/420/420/466, gain 4
m6 target-ratio minimal     3                 4          3905/3718/3069/836, gain 4
```

Each nonvacuous head tuple is

```text
columns / literal head rows / contact rank / nullity.
```

For the strongest target-ratio control, the complete base is

```text
L8: 4764 columns / 5995 rows / rank 4719 / nullity 45 / boundary gain 3.
```

Adjoining the full newly legal positive-Z part of L9 gives

```text
5623 columns / 6941 rows / rank 5445 / nullity 178 / boundary gain 4.
```

The corrected old L7 head has gain four with a large 836-dimensional kernel.
This is the finite pattern wanted by a quotient-aware last-three lift: first
realize all four boundary axes modulo epsilon orders `0,1,2`, then use one
passive layer to restore those omitted orders.

## 5. Derivative-shape attribution is not universal

For the 18 seed-zero broad cases, the complete source was admitted in nested
blocks

```text
raw (R,S)=(0,0), then +R, then +S, then +R^2.
```

The first stage with any contact kernel was

```text
+R:   12/18
+S:    1/18
+R^2:  5/18
```

Therefore the strong m6 observation “all kernel directions are born at the
highest R block” is data/profile specific.  It is false as a universal
finite mechanism and should not be elevated into the target theorem without
an additional target-specific injectivity hypothesis for the earlier blocks.

## 6. Deep-passive controls and scope

Complete caps at passive depths `L-U=5,8,9` all have boundary gain four:

```text
gap 8, m3: 2462 columns / rank 2440 / nullity 22
gap 5, m4: 3067 columns / rank 3030 / nullity 37
gap 9, m4: 4674 columns / rank 4653 / nullity 21
```

This provides no counterexample in the sampled deep-passive regime, but gaps
of at most nine are not a proof for target gap 3693.  The experiment also
checks only the deterministic boundary point `X=n`; it is a falsifier and
mechanism discriminator, not a universal nonvanishing argument.

## 7. Process correction

The failure was semantic, not computational.  A row count from a convenient
oracle was accepted before writing the explicit isomorphism to the formal
contact and boundary conventions.  The corrected order of operations is:

1. write the literal substitution and boundary graph, including Hasse versus
   ordinary derivative normalization;
2. prove or test the exact row/column conjugacy;
3. state projections in invariant weighted coordinates (`q+3E` here);
4. only then interpret ranks as evidence for a formal theorem.

The deterministic receipt is
`.experiments/k0_flattened_contact_sweep_regression_6900.py`.

```text
canonical SHA-256  4a59e55d08fbb5a42d17f2d74b361fc919a7c6bfd254c6de6b85b9fca0599fb2
script SHA-256     35915544667b3244728fe970e98867facc0940715f833251b88b83fbd136ff45
runtime            851.356 seconds
peak RSS           1,196,616 KiB
address-space cap  4,294,967,296 bytes
```
