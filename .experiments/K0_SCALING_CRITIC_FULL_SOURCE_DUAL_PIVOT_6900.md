# k=0 scaling critic: packet STOP and full-source dual pivot

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G` research only. This note
changes no production file, score, candidate, or submission.

## Verdict

The current evidence is honestly split:

```text
intrinsic full-source four-boundary gain in the tested chambers       GREEN
one fixed maximal-contact bordered minor across two errors             RED
arbitrary scalar error localization by the partial-carrier packet      RED
all-anchor partial-carrier packet gives four simultaneous directions   RED
target full-source compatible-dual-zero theorem                        OPEN
```

The new decisive observation is not just that constant passive ratios
collapse the scalar packet. In the smallest target-gated two-Newton,
two-error chamber, expanding every legal partial carrier and using every
literal order-two contact row gives the following exact progression:

```text
one anchor, a0/a1/a2 packet:        boundary gain 0
two adjacent anchor packets:        boundary gain 1
three adjacent anchor packets:      boundary gain 3
all 10 possible anchor packets:     boundary gain 3
complete relaxed source:            boundary gain 4
```

For the all-anchor packet there is exactly one compatible nonzero boundary
covector, represented over `F_11` by

```text
(lambda_Y,lambda_R,lambda_S,lambda_Z) = (1,8,2,1).
```

Each boundary coordinate separately has gain one, yet the combined gain is
only three. Thus four separate one-coordinate witnesses are not a rank-four
argument. More anchor charts also do not repair the fourth direction in this
faithful chamber. The complete source does.

The exact next target is therefore a rank-adaptive **full-source dual
separation lemma**, not another packet count, scalar Hermite theorem, or
fixed contact minor.

## 1. What was audited

The audit started from the actual positive chain and its STOP boundaries:

- `e735b93`: exact-`G` m47 source and consumer arithmetic;
- `9665cbc`: one-error two-bordered cover in the first-Newton toy chamber;
- `605c468`: target-gated one-error adjacent 919-minor cover;
- `2b4a421`: three-border versus `T2`, including the exact `T2` shortcut
  counterexample;
- `494d7e9`: two-error contact-rank adaptivity;
- `38f1fe6`: the adjoint bridge and direct single-carrier HRS obstruction;
- `4160cb3`: exact carrier transform, local Toeplitz determinant, and the
  target-valid constant-`T` scalar-trace STOP.

The exact-`G` m47 arithmetic remains useful:

```text
(m,B,s,U,L)                         (47,16,8,64,3757)
source surplus at g=180413                    2,371,080
exact-cardinality consumer       126,379,740,905,865,216
MCA allowance                    254,684,620,614,660,120
```

It proves that a full-source theorem would fit. It does not prove that
theorem.

## 2. Hidden assumptions exposed

### 2.1 A fixed contact basis was silently being extrapolated

The one-error certificates in `9665cbc` and `605c468` are genuine exact
minor covers in their chambers. They do not select a contact pivot basis
which remains maximal when another error or another Newton coefficient is
introduced.

In the two-error gate of `494d7e9`, the contact rank moves among `722`, `724`,
and `726` while the augmented rank moves with it and the intrinsic gain stays
four. A fixed maximal-contact determinant from one chamber must vanish in a
lower-rank chamber even though the desired normal map is still surjective.

So the scalable statement cannot name one contact pivot set before seeing
the mismatch pattern.

### 2.2 One-error nonvanishing was being confused with all-error localization

The target has `81731` errors at the lowest exact stratum. A local factor
such as `epsilon_i^22` proves a one-node Toeplitz block is nonsingular. It
does not show that the chosen source columns clear the other `81730` error
blocks or place them strictly off a global Schur diagonal.

The missing global triangularity is theorem content, not a mechanical
iteration of the one-error factorization.

### 2.3 Nominal seed/anchor column count was being confused with trace rank

For m47, the unshifted packet has only `75888` columns, below `81731`, but
higher legal seed shifts give more than 283 million nominal columns. Neither
count decides the relevant rank. On an error with finite passive ratio
`rho=-delta/epsilon`, all seed powers evaluate to scalars `rho^z`.

The formal constant-`T` family in `4160cb3` is decisive. Take `deg Q_G=w+1`
and leading coefficient `c!=0`. For every size-`w+1` anchor `H`,

```text
q_H = Q_G-c Lambda_H,      T_H=(Q_G-q_H)/Lambda_H=c.
```

With common nonzero mismatch ratio, every anchor, seed shift, and scalar
packet trace lies in

```text
Lambda_G^m * span{1,X,...,X^(m-1)}.
```

The dimension is at most `m`, not the nominal column count. The same family
collapses m60 to dimension at most 60.

### 2.4 Anchor swaps do not force passive-ratio diversity

`K0RankAdaptiveDual6900.adjacent_anchor_swap_preserves_constant_ratio_family`
constructs exact residuals for which two adjacent anchor charts have any
two prescribed nonzero constant ratios. The stronger result in `4160cb3`
makes all anchor trace spaces identical in the degree-`w+1` family.

Therefore an anchor swap may change locator prefactors, but it cannot be
credited with an automatic Vandermonde in the error nodes.

### 2.5 Separate coordinate gains do not imply rank four

The new all-anchor exact gate has individual gains

```text
Y=1, R=1, S=1, Z=1
```

but simultaneous gain three. Its compatible covector `(1,8,2,1)` is a
literal counterexample to any proof which constructs four nonzero coordinate
classes but never proves their independence modulo the contact row space.

### 2.6 The `T2` reduction cannot absorb the missing direction

The exact gate in `2b4a421` already shows that the tempting three-border
`T2` shortcut fails on a legal `(Y,R,S^2)` configuration. The remaining
direction has to be killed in the actual four-boundary module.

## 3. Two-Newton/two-error target-gated result

`.experiments/k0_target_gated_two_newton_two_error_6900.py` uses

```text
F_11,
(n,w,g,m,B,s,U,L,k,n0)=(7,2,5,4,2,1,7,7,0,1),
Q=C(X,3)+t*C(X,4).
```

The first extra Newton coordinate is fixed to one, the later coordinate
`t` is exhausted over `F_11`, and five two-error mismatch patterns are
tested. All 55 exact cases have conormal gain four. The contact rank is not
constant: the constant-`T` cases at `t=0` have rank 1280, while most cases
have rank 1281; another first-mismatch specialization at `t=6` drops to
1276 while retaining gain four.

Receipt:

```text
source columns / contact cap / margin       1728 / 1281 / 447
canonical SHA-256  19104ecc21df7eb12e0ba42dc4bb6119df1cf387af630b8c511e863928cb66d9
script SHA-256     00b5e3c0e4e6706e42a55f8739e37f094a90e71c17244413737f0bf570cb6a58
runtime            about 54 s, about 130 MiB child RSS
```

This is the first exact gate here with two agreement Newton coordinates and
two errors while satisfying the promoted profile equalities. It is finite
small-field evidence, not the target theorem.

## 4. Rank-adaptive replacement lemma

`.experiments/K0RankAdaptiveDual6900.lean` proves, for arbitrary linear maps
and without a contact rank, basis, or finite-dimensional hypothesis:

```text
not Surjective (boundary restricted to ker contact)
iff
exists lambda != 0,
  boundary.dualMap lambda in range contact.dualMap.
```

Equivalently, the normal map is onto exactly when every compatible boundary
covector is zero. The theorem names are

```text
not_surjective_normal_iff_exists_compatible_dual
normal_surjective_iff_compatible_dual_zero
```

This is the correct invariant replacement for all fixed-pivot claims. The
file compiles in 3.3 seconds under `-M8000`; printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. File SHA-256:

```text
ed4e2591bf74cc5290b1a26e3e4da3a5561548f5382237a8937dd2e274b26f57
```

## 5. Selected survivor experiment

Three mechanisms retain information discarded by the scalar trace:

1. higher osculating/contact rows from `a1`, `a2`, and the complete source;
2. the fact that only a distinguished four-dimensional boundary covector,
   rather than an arbitrary `81731`-entry error syndrome, must be excluded;
3. simultaneous full four-border Schur coupling modulo the contact row
   space.

The falsifiable experiment chosen for all three was the exact constant-`T`
carrier ablation in
`.experiments/k0_constantT_packet_conormal_ablation_6900.py`. It expands the
actual legal anchor-centered carriers into the raw `(X,Y,R,S,Z)` source and
uses every literal order-two contact row. It does not model the packet by a
dimension count or scalar evaluation.

Exact result:

```text
source family                         cols   contact rank   kernel   gain
anchor 012, a0 only                     50       50            0      0
anchor 012, a0+a1                      126      126            0      0
anchor 012, a0+a1+a2                   171      171            0      0
anchors 012+013, full packet           342      272           70      1
anchors 012+013+014, full packet       513      297          216      3
all ten size-three anchors            1710      297         1413      3
complete relaxed source               1728     1280          448      4
```

For all ten anchor packets, the compatible-boundary space is exactly the
line represented by `(1,8,2,1)`. The complete source removes that line.

Receipt:

```text
canonical SHA-256  3eef07a9a476e27634799a9cc5d2db73e916a94b6cae801761acbe43dd72f65e
script SHA-256     ea78a8ae67974ccc8fd6e43fb4f6303bc1f71b310e1754c5cff0445e90f6ec19
runtime            about 14 s, about 153 MiB RSS, 4 GiB cap
```

Interpretation by mechanism:

- Higher contact information in one packet is insufficient; the full packet
  is injective in this chamber. Across charts it recovers three directions,
  so it is useful but incomplete.
- The distinguished-covector formulation compresses the remaining problem
  to one explicit line in this chamber. This is much smaller than arbitrary
  error-trace surjectivity and is the right proof language.
- Full four-border coupling survives only after the complete source is
  retained. This is the sole mechanism among the three which passes the
  adversarial gate as stated.

The limitation is explicit: this is a structurally faithful small chamber,
not a scaling theorem. It refutes universal packet-only lemmas because such
lemmas would specialize here; it does not prove the target full-source
statement.

## 6. m47 versus the old exact-G m60 profile

The old profile

```text
(m,B,s,U,L)=(60,21,10,82,2703)
```

was not abandoned because its source or consumer arithmetic failed. Its full
prefix has surplus `9,757,693`, the strong safe-103 restriction retains
`3,291,277`, and the 52-chart exact-strata consumer cost
`192,195,019,290,064,896` is below the MCA allowance. Much of its exact-G
source and consumer wrapper is already formalized.

It was demoted because the claimed source-to-consumer connector never became
a theorem. The first-shell fixed connector has exact ratio-faithful
countercontrols, and the pointwise CS4/full-source dual statement remains an
explicit premise in the packaged wrappers.

Its unshifted partial-packet count `197824>81731` is not a reason to pivot
back. The constant-`T` family collapses those columns to dimension at most
60, exactly as it collapses m47 to dimension at most 47.

Recommendation:

```text
do not pivot to m60 for packet capacity;
keep m47 for the cheaper current dual test;
switch only if a proved full-source dual recurrence identifies a source
family present in m60 but genuinely absent from m47.
```

m60 remains a plausible integration fallback because it has more formal
infrastructure and margin. It has no demonstrated mathematical advantage on
the theorem which is actually open.

## 7. Exact next go/no-go theorem

Let `C` be the literal complete all-node contact map and `beta` the four-row
boundary map for one exact-`G` stratum. The target statement should be written
directly as

```text
forall lambda : Dual K (Fin 4 -> K),
  beta.dualMap lambda in range C.dualMap -> lambda=0.       (DUAL0)
```

By the compiled rank-adaptive lemma, `(DUAL0)` is exactly full conormal rank
four. It never chooses contact pivots and does not require scalar error-trace
surjectivity.

The most concrete intermediate target suggested by the new gate is a
**line-then-kill** lemma:

```text
1. three source-safe anchor packets force every compatible lambda into a
   distinguished rank-at-most-one module L(Q_G,G);
2. one explicitly named lower-weight complete-source family forces the
   remaining lambda in L(Q_G,G) to be zero.
```

Both clauses must be identities for arbitrary exact-`G` bad data, retaining
all contact coordinates and the full Newton quotient `T(X)`. No clause may
assume a fixed contact rank, varying passive ratios, or error-by-error packet
localizers.

The go/no-go criterion is sharp:

```text
GO: derive the two clauses above and compile (DUAL0), or exhibit a symbolic
    Schur identity which is equivalent to them.

NO-GO: produce one valid exact-G datum and a nonzero lambda satisfying the
       complete-source adjoint equations. A lambda compatible only with the
       partial packet, such as (1,8,2,1), is not a counterexample; it is the
       obstruction the second clause must kill.
```

The next experiment should therefore identify which lower-weight raw source
family kills the explicit packet obstruction and then formulate its
coefficient identity. It should not run another generic rank grid. Until
that identity is proved, there is no target rank theorem, assembled 6900
candidate, or verifier-ready submission.

