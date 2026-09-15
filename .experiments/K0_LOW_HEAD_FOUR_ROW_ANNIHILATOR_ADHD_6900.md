# K0 low-head four-row annihilator: ADHD divergence and convergence

Date: 2026-09-15 UTC. Scope: lower-6900 terminal route. This note changes no
production file, candidate, claim, or submission root.

## Brief

The load-bearing statement was unnecessarily large: the corrected terminal
consumer does **not** need an `(n+1)`-node low-head CRT. It needs only the four
boundary rows to be independent modulo the old low-head rows. Five isolated
divergent passes generated 30 alternatives; the best target-formal route is a
four-dimensional dual recurrence defect.

Scores below are `[N novelty, V viability, F fit]`, each on `0..10`; ranking
uses `0.35*N + 0.40*V + 0.25*F`.

## Wide set

### Four-row quotient and dual plays

- Four-row annihilator separation `[N8 V8 F10]`
- Truncated inverse-system subquotient `[N9 V6 F9]`
- Four-symbol parity-check/erasure decoder `[N7 V8 F10]`
- Apolar multiplier excluding old support `[N9 V5 F8]`
- Local principal-part residue pairing `[N8 V5 F8]`
- Four leading-monomial dual eliminations `[N7 V6 F9]`

### Scalar pivots and Schur repair plays

- Successive one-dimensional quotient lifting `[N7 V7 F10]`
- Nested-kernel triangular boundary pivots `[N6 V7 F10]`
- Four-column Schur complement `[N7 V7 F9]`
- Right inverse only on the four attained residuals `[N8 V6 F10]`
- Boundary-transparent residual correction `[N6 V6 F9]`
- Four-standard-monomial quotient staircase `[N8 V5 F9]`

### Recurrence and state-space plays

- Confluent recurrence at one fresh root `[N9 V7 F10]`
- Four terminal syndrome defects `[N9 V7 F10]`
- Rank-four displacement certificate `[N10 V4 F8]`
- Four-lane output-nulling controllability `[N9 V4 F8]`
- Accepted nodal top-coefficient recurrence `[N8 V8 F10]`
- Collision-asymptotic confluent differences `[N9 V3 F6]`

### Partial-locator and feedback plays

- Four short repair germs `[N8 V6 F9]`
- Sequential regenerative cascade `[N8 V5 F8]`
- Nilpotent filtered feedback `[N9 V6 F9]`
- Paired partial locators `[N9 V5 F8]`
- Cyclic block-local defect cancellation `[N9 V4 F7]`
- Packetized constraint excision `[N8 V5 F8]`

### Small determinant and deformation plays

- Sparse separator family with a symbolic four-minor `[N8 V3 F6]`
- Partial confluent minor factorization `[N8 V5 F8]`
- Degeneration to a monomial initial module `[N10 V3 F5]`
- Generic four-parameter determinant `[N7 V3 F5]`

### Geometric and distributed-vanishing plays

- Osculating-curve pullback with four transverse lifts `[N9 V3 F6]`
- Node-dependent active-coordinate vanishing allocations `[N10 V2 F6]`

## Converge

1. **Four-dimensional nodal recurrence defect — 8.50/10.** Apply a
   recurrence operator to source duals which kills the entire old row image;
   prove that its values on the four boundary rows form an invertible
   `4 x 4` map. This is exactly the desired quotient statement and composes
   with the existing exact raw-adjoint/HRS interface.
2. **Right inverse on four attained residuals — 7.70/10.** Correct only the
   old-head residuals of four explicit boundary seeds. It is genuinely
   smaller than an extra-node CRT, but constructing boundary-invisible lifts
   of those four residuals can conceal the original theorem.
3. **★ Partial-locator nilpotent feedback — 7.80/10.** A cap-legal correction
   may be imperfect if its residual strictly advances a finite filtration;
   a finite geometric series then gives an exact correction. This is the
   most interesting non-obvious alternative, but the advancing-filtration
   identity is still unproved.

### Traps removed

- **Full extra-probe CRT:** exact in the m8 receipt but much stronger than the
  four-row target and not proved at target scale.
- **`Omega_all^44`:** source-illegal:
  `44*(262144+1)=11,534,380 > 8,479,411` by `3,054,969`.
- **Generic determinant/deformation:** proves a Zariski-open configuration,
  while the benchmark theorem must handle the actual arbitrary received word.
- **Boundary-transparent right inverse rhetoric:** the hidden premise is
  `span(H(seed_i)) <= H(ker B)`; without a construction this merely renames
  the problem.
- **Nilpotence by itself:** the geometric sum is bookkeeping; the hard fact
  is a legal `C` with `H*C=id-N`, `B*C=0`, and filtration-raising `N`.
- **Four separately nonzero defects:** this does not imply joint rank four.
  One needs an injective defect map or a genuine `4 x 4` left inverse.
- **Opposite head projection:** the old `epsilon>=3` receipts cannot support
  this route. Here `head=epsilon^0,...,epsilon^43` and the terminal coordinates
  are `epsilon^44,epsilon^45,epsilon^46`.
- **Finite rank-three splice:** the rank-three old-boundary fact is only an
  m8 complete-contact receipt. There is currently no target-literal theorem
  giving three boundary axes on `ker(head<44)`.

## Focus 1: four-dimensional recurrence defect

Let

```text
H : Source -> OldHead
B : Source -> Boundary4.
```

The smallest useful certificate is a linear map

```text
A : Dual(Source) -> Defect
```

such that

```text
A o H* = 0,
A o B* is injective.
```

Then any boundary covector whose pullback is an old contact covector is killed
by `A`; injectivity forces the boundary covector to be zero. Algebraic duality
then gives `Surjective (B|ker H)`. The new Lean file proves this without a
finite-dimensional assumption on `Source` or `OldHead`, and also provides a
version where an explicit decoder is a left inverse to `A o B*`.

The intended concrete `A` consists of only four terminal defects of a
matrix-valued nodal/confluent recurrence. `K0WeightedRawAdjointRecurrence6900`
already gives the exact raw-source basis, complete-contact dual coefficients,
agreement/error split, and reverse-Hasse multiplier identity. The new missing
theorem is therefore sharply reduced to:

```text
construct four linear recurrence defects on the literal capped raw dual;
prove each kills every old low-head row basiswise;
compute a left inverse on the four readout rows.
```

The load-bearing risk is source taper: a recurrence valid for an unrestricted
X staircase need not preserve every shape-dependent X window. The first
falsifier is correspondingly cheap and exact: test `A(H*(eta))=0` on each raw
shape boundary, before computing any determinant. The second falsifier is
rank of the four boundary defects, not their individual nonvanishing.

Useful child routes are a triangular four-defect matrix, an agreement/error
factorization using one-grade error-value CRT, a matrix-polynomial/Popov
annihilator across active-shape lanes, and a decoder stated as four coefficient
identities rather than a determinant.

## Focus 2: four-residual Schur repair

Choose four legal seeds with an invertible boundary matrix and let `W` be the
span of their four old-head residuals. It is enough to construct

```text
C : W -> Source,
H o C = inclusion(W),
B o C = 0.
```

Subtracting `C(H(seed_i))` gives four head-kernel vectors with the same
boundary matrix. The load-bearing risk is exactly `W <= H(ker B)`, which can
be as hard as the desired conclusion. The first concrete target test should
therefore be a symbolic locator-grade correction for the residuals of the
four local section elements, with source legality checked term by term. Do
not build a general right inverse.

Child routes include lowering `dim W` by choosing contact-adapted seeds,
correcting coordinates sequentially, using the agreement/error split for
each residual, and allowing a nontransparent correction while certifying the
resulting Schur determinant.

## Focus 3: partial-locator nilpotent feedback

Suppose `S : Boundary4 -> Source` is the explicit local boundary section and
its head defects lie in `W`. If maps `C : W -> ker B` and `N : W -> W` obey

```text
H o C = id - N,       N^m = 0,
```

then

```text
R = S - C (id + N + ... + N^(m-1)) H S
```

satisfies `H o R=0` and `B o R=id`. Agreement-locator grades and passive
successors suggest possible filtrations. The load-bearing risk is that the
residual may move sideways into an equally early active shape, as witnessed
by earlier confluence counterexamples. The first test is not a dense rank:
derive the exact image of one locator-grade correction and verify strict
filtration advance plus zero boundary.

Child routes include agreement/error two-block feedback, reverse-Hasse-order
feedback, passive-degree feedback, and a hybrid where the recurrence defect
proves nilpotence of the primal residual operator.

## Formal artifact and status

`.experiments/K0LowHeadFourRowAnnihilator6900.lean` proves:

```text
kernelBoundary_surjective_of_dual_separation
kernelBoundary_surjective_of_annihilator
kernelBoundary_surjective_of_pointwise_defect
kernelBoundary_surjective_of_defect_leftInverse
compatibleBoundaryDual_eq_zero_of_lowHead_annihilator
```

The final theorem feeds the annihilator certificate directly into the
quotient-aware last-three compatible-dual detector. Replay:

```bash
LEAN_PATH=.experiments lake env lean \
  .experiments/K0LowHeadFourRowAnnihilator6900.lean -j1 -M4200
```

It completes in about 3.3 seconds and all printed theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, `admit`, `decide`,
`native_decide`, explicit axiom, or unsafe declaration.

Verdict: **GREEN abstract reduction; YELLOW target route.** The full
`n+1` low-head CRT has been removed. The concrete target recurrence operator
`A` and its rank-four defect/left inverse remain open; no 6900 proof is
claimed from this artifact alone.

## Provocation

Can the accepted raw nodal top-coefficient recurrence be evaluated only on
the four formal readout section elements, producing an upper-triangular defect
matrix, without ever defining its action on the rest of the extra local jet?
That would turn the remaining global theorem into four basiswise recurrence
identities rather than a rank theorem.
