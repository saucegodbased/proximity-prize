# k=0 rank-four / tangent-pencil consumer audit for lower 6900

Date: 2026-09-14 UTC.  Scope: consumer audit only.  No production file,
candidate, score, claim, build, comparator run, or submission is changed.

## Executive decision

The order-15 route is stopped.  Its cutoff accounting counted the four
curvature derivatives on only one side: after `D4`, both weighted degree and
contact lose the corresponding `4A`, so even the first canonical-tangent
coefficient is not root-forced.

For the replacement `k=0` ordinary source, the low-degree agreement tangent
has a much cleaner consumer:

* **GO, zero extra counting cost, if original bad-row provenance is kept.**
  A degree-`w` polynomial `h` agreeing with the received direction `U1` on
  the candidate's original agreement set contradicts the bad-row witness at
  that candidate.  This endpoint is already formalized in
  `GlobalO2BadRowConormalBridge6900.no_direction_interpolant_of_bad`, and
  `full_rank_four_of_bad_and_rank_defect_recovery` already turns the exact
  source statement `rank < 4 -> such an h exists` into rank at least four.

* **NARROW but quantitatively green if only `NoLargeSelectedPencil` is
  retained.**  The tangent determines a literal fixed polynomial pencil,
  and `NoLargeSelectedPencil` caps the selected occupants of each *fixed*
  pencil by `e+1`.  It does not cap the union over a varying pencil for every
  candidate.  To use it globally, deduplicate the tangent pencils and bound
  their number.  A common regular triple plus the existing seed-generic
  Fin4 aggregate adapter does exactly that; no local-intersection or
  multiplicity theorem is needed.

* **STOP** treating “rank four generically” or the forward implication
  `low-degree tangent -> rank three` as an exhaustive partition.  The needed
  source theorem is the reverse implication, on every retained low-band
  candidate and over the base field.  Also, a fixed cutoff has a separate
  high-actual-agreement rank collapse which is not a tangent-pencil
  exception.

Thus the fastest endpoint is to preserve `hbad` and prove one exact
rank-defect-recovery theorem.  The pencil aggregation below is a sound,
cheap fallback if the caller insists on retaining only the historical
no-large-pencil abstraction.

## 1. What `NoLargeSelectedPencil` actually says

The production definition in `LowerFoundation.lean` is literally

```lean
def NoLargeSelectedPencil
    (selected : K -> Polynomial K) (Gamma : Finset K) (w e : Nat) : Prop :=
  forall P0 P1 : Polynomial K,
    P0.natDegree <= w -> P1.natDegree <= w ->
    (Gamma.filter (fun gamma =>
      selected gamma = P0 + Polynomial.C gamma * P1)).card <= e + 1
```

At target 6900, `e=81731`, so one fixed pencil has at most `81732`
selected seeds.  The existing theorem

```text
BadSelectedPencilFibreCount.pencil_fibre_card_le_of_original_badness
```

derives this fixed-pencil cap directly from the original agreements and the
pointwise bad-row witness.  Therefore the information flow is

```text
original per-candidate badness  ==>  every fixed-pencil fibre is small,
```

not conversely.  Replacing badness by `NoLargeSelectedPencil` is a genuine
loss of information.

For one exceptional candidate `(gamma,P)` and one exact agreement tangent
`h`, put

```text
P1 = h,
P0 = P - gamma*h,
P_t = P0 + t*P1.
```

Both `P0` and `P1` have degree at most `w`.  Every `P_t` agrees with
`U0+t*U1` on the same agreement set, and the candidate is the member
`t=gamma`.  Hence this is exactly a pencil admitted by the definition above.

However, candidatewise witnesses may give different pairs `(P0,P1)`.
`NoLargeSelectedPencil` only says that each resulting fibre has size at most
`81732`; it does not bound how many distinct fibres occur.  A one-element
family already demonstrates the logical issue: it satisfies
`NoLargeSelectedPencil` vacuously, whether or not its sole candidate has a
low-degree tangent.

## 2. The preferred pointwise badness discharge is already formal

Suppose the selected polynomial `P` and the tangent polynomial `h` satisfy

```text
deg P <= w,
deg h <= w,
P(x_i) = U0(i) + gamma*U1(i)  for i in A,
h(x_i) = U1(i)                for i in A.
```

Then `P0=P-gamma*h` interpolates `U0` on `A`, while `h` interpolates `U1`.
Thus both projected received rows belong to the degree-`w` Reed--Solomon
code on `A`.  This contradicts the exact MCA bad-row witness

```lean
exists j : Fin 2,
  projectedWord (U j) A not_mem projectedCodeSubmod (RS(w+1)) A.
```

This is not a proposed lemma.  It is the compiled theorem

```lean
GlobalO2BadRowConormalBridge6900.no_direction_interpolant_of_bad
```

proved through
`BadRowSecondInterpolatorUniqueness6900.second_interpolant_is_proportional`.
The same file already exposes the exact source-facing consumer:

```lean
theorem full_rank_four_of_bad_and_rank_defect_recovery
    ...
    (normal : Tangent L ->ₗ[L] W)
    ...
    (hrankDefectRecovery :
      finrank L (range normal) < 4 ->
        exists h : Polynomial K,
          h.natDegree <= w /\
          forall i in A, h.eval (domain i) = U 1 i) :
    4 <= finrank L (range normal)
```

Consequently the minimal theorem needed from the new `k=0` source is exactly

```lean
theorem k0_rankDefectRecovery_on_original_agreement
    (gamma : K) (hgamma : gamma in Gamma)
    (hrank : finrank (RatFunc K) (range (normal gamma)) < 4) :
    exists h : Polynomial K,
      h.natDegree <= w /\
      forall i in A gamma,
        h.eval (domain i) = U 1 i
```

and not an intersection-multiplicity theorem.  Applying the existing
consumer candidate by candidate yields rank four on the entire bad family.

Three details in this interface are load-bearing:

1. `h` is in the base-field ring `K[X]`, not merely in `RatFunc K[X]` or an
   algebraic extension;
2. its degree is `<=w`, not merely `< card (A gamma)`; and
3. it agrees on the original supplied `A gamma`, or on a proved enlargement
   containing it.  A punctured/unrelated support does not contradict the
   original bad-row witness.

`AffineLineBadFamilyContract6900.givenSetsBound_of_bad_selected_count`
already shows how to retain this pointwise badness in the top-level MCA
contradiction.  The process error to avoid is immediately downcasting it to
`NoLargeSelectedPencil` and later trying to reconstruct it.

## 3. Exact no-large-pencil fallback via explicit line primes

If the rank theorem is organized without `hbad`, the tangent pencils can
still be counted without new intersection theory.

Over the generic-X coefficient field, the pencil `(P0,P1)` is the affine
line in boundary-coordinate order `(S,Y,R,Z)`

```text
t |-> (P0'' + t*P1'', P0 + t*P1, P0' + t*P1', t).
```

Define `pencilPrime P0 P1` as the kernel of the algebra map from the Fin4
boundary ring to a polynomial ring in `t` given by this substitution.  The
map is onto because `Z` maps to `t`; its target is a domain, so the kernel is
prime.  The seed coordinate is transcendental modulo this prime, and the
generic seed-projection residue field has positive degree (in fact degree
one).

Let `g : Fin 3 -> Poly4` be three common source rows whose ordinary
three-by-three derivative minor is nonzero at every tangent exception.  Such
a triple exists by the same finite-avoidance argument already implemented in
`FiniteSimultaneousFourJetBasis6900`; that file needs only a small Fin3
specialization of its iterative selection proof.

For every tangent line:

* each retained row lies in `pencilPrime P0 P1`, because the symbolic graph
  `P0+t*P1` has the same agreement set and the ordinary source root-forcing
  theorem vanishes on it;
* the ordinary derivative determinant is outside the line prime because it
  is nonzero at the original candidate; and
* nonzero polynomials in the seed are disjoint from the line prime.

Therefore the existing theorem

```text
Fin4GenericFibreTotalDegreeAggregate6900.
  sum_finrank_genericPrime_le_three_mul_totalDegree
```

applies directly to the finite family of distinct line primes.  It accepts
arbitrary distinct primes containing the common triple; it does not require
minimal primes or a preproved height statement.  If the three rows have
ordinary total degree at most `J`, it gives

```text
sum over distinct tangent lines of generic seed-fibre degree <= 3*J^3.
```

Every summand is positive, hence the number of distinct tangent lines is at
most `3*J^3`.  On each line,
`CanonicalRationalBoundary.fixed_pencil_card_le` (or the definition of
`NoLargeSelectedPencil` directly) bounds the selected occupants by `e+1`.
Thus

```text
card tangentExceptions <= (e+1) * 3*J^3.                 (TP)
```

This is the theorem-shaped aggregation interface:

```lean
theorem tangent_exception_card_le
    (lines : Finset (Polynomial K × Polynomial K))
    (hcover : tangentExceptions subset
      lines.biUnion (fun q =>
        Gamma.filter (fun gamma =>
          selected gamma = q.1 + C gamma * q.2)))
    (hdegrees : forall q in lines,
      q.1.natDegree <= w /\ q.2.natDegree <= w)
    (hprimeInjective : Function.Injective
      (fun q : lines => pencilPrime q.1 q.2))
    (hrowsIn : ...)
    (hminor : ...)
    (hbox : ...)
    (hno : NoLargeSelectedPencil selected Gamma w e) :
    tangentExceptions.card <= (e+1) * 3*J^3
```

The required proof is only finite union arithmetic plus the two existing
consumers.  The missing formal glue is an explicit `pencilPrime` package,
the Fin3 common-row selector, and the source-row symbolic-line vanishing
adapter.  Mathlib already supplies the polynomial evaluation homomorphisms,
prime kernels into domains, fraction fields, and injectivity needed here.
CompPoly contributes no necessary local-intersection API.

Importantly, we do **not** need to prove that a tangent line is a minimal
component.  Feeding its explicit prime to the aggregate theorem is stronger
and cheaper.  Nor do we need a fourth separator on the line: every ordinary
source row vanishes along an honest agreement pencil, so such a separator
would generally be false.

## 4. Full theorem-shaped finite partition

For an end-to-end rank/pencil consumer, the source must prove the exhaustive
dichotomy

```lean
forall gamma in Gamma,
  4 <= finrank (range (normal gamma))
  or
  (finrank (range (normal gamma)) = 3 /\
    exists h : Polynomial K,
      h.natDegree <= w /\
      forall i in A gamma, h.eval (domain i) = U 1 i).
                                                               (DICH)
```

The forward observation

```text
such an h exists  ==>  the canonical tangent annihilates the source
```

proves only rank at most three.  It does not prove `(DICH)`.  The reverse
inclusion—every rank defect descends to that base-field bounded polynomial—is
the substantive source theorem.

With `(DICH)`, define `Gamma4` and `GammaPencil` by the two cases.  Existing
rank-four work gives

```text
card Gamma4 <= allChartCost J L,
```

while `(TP)` gives

```text
card GammaPencil <= (e+1)*3*J^3.
```

Hence the exact combined endpoint is

```text
card Gamma <= allChartCost J L + (e+1)*3*J^3.             (TOTAL)
```

If pointwise `hbad` is retained, `GammaPencil` is empty by Section 2 and the
second term disappears.

The useful consumer fact preserved from the abandoned order-15 audit is:
a regular common triple plus *any* fourth row proper on the associated prime
already plugs into the existing 52-chart count.  No multiplicity-aware
consumer is needed.  An honest tangent pencil is precisely the case where
properness is unavailable, which is why it is routed to badness or the
per-pencil cap instead.

## 5. Exact arithmetic for the low-m k=0 hit

The deterministic integer source search currently has the low-m hit

```text
(m,B,s,U,L,k) = (38,15,7,52,17832,0)
source-minus-rank margin = +1,027,158.
```

This is source arithmetic, not the missing rank theorem.  Setting `J=52`,
the existing consumer formulas give

```text
all 52 rank-four charts       3,915,721,325,568
seed generic degree 3*J^3            421,824
pencil charge 421824*81732         34,476,519,168
combined TOTAL                3,950,197,844,736
MCA allowance          254,684,620,614,660,120
remaining margin       254,680,670,416,815,384.
```

So the pencil fallback costs only about `0.00155%` of the MCA allowance.
Counting is emphatically not the numerical blocker.

## 6. Separate high-agreement rank-collapse audit

A fixed source cutoff `D=m*A` has another rank-defect mechanism unrelated to
low-degree tangents.  Using the already audited full-normal degree and
locator orders, at design agreement `A` its four-minor residual is

```text
(4D - 3w - 1) - A*(4m-3) = 3*(A-w)-1 = 148025.
```

Thus every full minor is degree-forced to vanish after

```text
floor(148025/(4m-3)) + 1
```

extra actual agreements.  This gives literal bad-row counterfamilies to a
uniform `rank<4 -> low-degree tangent` statement: take a larger actual
agreement set, retain a bad `U1` restriction on the original `A`, and degree
alone kills all minors.

For `m=38`, the last not-degree-forced size and first forced size are

```text
last:  180413 + 993 = 181406, residual 68
first: 181407.
```

The accepted-6810 source starts at agreement `181294`, so there is a
113-point arithmetic overlap.  That makes `m=38` strategically preferable
to the cheaper-chart `m=46` hit, whose first forced failure is already
`181231`.  The overlap is not itself an assembled high-band theorem: the
accepted high source still needs an interface preserving the target badness
or target pencil cap.  Nevertheless it removes a numerical gap if the two
source consumers are joined honestly.

Accordingly the low-band source theorem should state its actual-agreement
range explicitly, for example

```lean
card (actualAgreement gamma) <= 181406 ->
rankDefectRecovery ...
```

and the global partition must route `card actualAgreement >= 181294` to the
accepted high source.  Reporting a uniform rank-four theorem from genericity
would repeat the earlier process failure.

## 7. Final gap table

| Obligation | Status | Consequence |
|---|---|---|
| Low-degree tangent contradicts original badness | **GREEN, compiled** | `no_direction_interpolant_of_bad` |
| Rank-defect consumer from such an `h` | **GREEN, compiled** | `full_rank_four_of_bad_and_rank_defect_recovery` |
| One fixed tangent pencil has at most `81732` selected occupants | **GREEN, compiled** | definition / `fixed_pencil_card_le` |
| Aggregate degree of distinct seed-active regular line primes | **GREEN, compiled consumer** | `<=3*J^3` once line-prime inputs are supplied |
| Explicit line-prime + symbolic line-vanishing wrapper | **NARROW formal glue** | modest, no new geometry |
| `rank<4 -> h in K[X]`, `deg h<=w`, on original `A` | **OPEN, load-bearing** | exact reverse-inclusion/source theorem |
| Exclusion of rank `<=2` if using the NLS dichotomy | **OPEN, load-bearing** | required for a regular triple |
| High-actual-agreement handoff to accepted source | **OPEN integration** | arithmetic overlap exists at `m=38` |
| Order-15 local-intersection/multiplicity route | **STOP** | premise invalid; consumer unnecessary |

Overall decision: **NARROW**.  The downstream algebra and counting are much
closer than the abandoned order-15 note suggested, but a submission is not
just mechanical yet.  The honest critical path is the low-band
rank-defect-recovery theorem, followed by the overlapping accepted-high
handoff.  More work on multiplicity-15 or general local intersection would
not reduce the current uncertainty.
