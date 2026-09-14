# Adversarial process audit: terminal-103 route versus the actual 6900 endpoint

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This note audits
commits `ac53954`, `b71edd7`, `f7330e6`, `a6057a3`, and `14c7712`, plus the
live matched m4/m5 four-packet discriminator. Production, the accepted 6806
submission, score, and radius are unchanged.

## Bottom line

The 103-shape result is a useful **local associated-graded license**, not a
restricted-source CS4 theorem. The present route is directionally connected
to `SelectedBadGivenSetsBound`, but it is still missing its central source
theorem and two downstream counting bridges. There is no 6900 candidate.

The main semantic corrections are:

1. “all-Hasse” currently means every coefficient-Hasse order `q` on the
   maximal-`h` agreement-principal branch of a terminal column. It does not
   mean every literal `u0^(y-f-h) u1^h` branch on error nodes, nor simultaneous
   propagation through passive grades.
2. The 103-shape deletion is only at the intersection
   `y+r+s=J`, `y+r+s+z=L`. It is not a global ban on those derivative shapes.
   Sharp adapted pivots legitimately use lower-active-grade source terms whose
   `(r,s)` may be outside the 103 set; those coordinates were never deleted.
3. Coefficientwise containment of the four named packets is sufficient for
   Full187 fraction-field CS4, but is strictly stronger than the theorem the
   benchmark route actually needs. It must not be called the “smallest honest
   target theorem.”
4. The live matched discriminator kills the one-carrier shortcut. At m4 the
   packet quotient happens to have rank one; at m5 it has rank four and the
   pure centered carrier adds a fifth independent class. The recurrence must
   carry four atomic residues, not one scalar residue.

Confidence that the current artifacts already prove target CS4: **low**.
Confidence that a faithful next falsifier is now well specified: **high**.

## 1. Semantic map: what each layer actually says

| Layer | Literal meaning | What is established | Missing implication |
|---|---|---|---|
| 103 terminal shapes | Delete the 84 unsafe `(r,s)` coordinates only where active grade is `J=82` and total active-plus-passive grade is `L=2703` | Exact arithmetic gives 103 retained shapes and positive Euler room | Positive room is not contact rank, CS4, or packet containment |
| all-Hasse local license | For a terminal source shape, set the agreement-principal exponent `h=y-f`, retain its passive tag, and check every surviving coefficient-Hasse order `q=0..59` | Exact target-parameter enumeration has no local capacity/pivot obstruction | Lower-`h` error branches, pivot tails, simultaneous X interpolation, and passive confluence are not covered |
| sharp pivot | A target contact monomial has a nonzero leading term in the order-two adapted basis and enough raw product width in the checked q=0 census | Local leading monomial and strict higher-contact tails are formal/algebraic; target counts are exact finite arithmetic | A global bounded source combination cancelling all tails while preserving four boundary classes is open |
| coefficientwise `F0..F3` containment | Each entire polynomial packet boundary lies in the complete-contact-kernel boundary image over the ground polynomial ring | Green in several tiny literal controls | Uniform target characteristic/parameters/received words/all exact `g` are open; this is stronger than necessary |
| fraction-field boundary rank four | `ker C_all -> K(X)^4` is onto | The abstract equivalence and consumers are Lean-proved; tiny controls have rank four | Literal Full187 rank four is precisely the open source theorem |
| exact-g point count | Four common equations isolate every candidate in one exact-agreement stratum | Common-kernel selection, base change, root forcing, injection, and point-ideal height have formal pieces | Jacobian-to-local-minimality and the fourfold isolated-point bound are still open |
| benchmark endpoint | Uniform exact-stratum count implies `SelectedBadGivenSetsBound`, then `ProtocolClaim 6900` | Conditional Lean adapters exist | The exact-stratum count has not been supplied; current checkout also lacks the imported `Order2Protocol6900.lean` source and sees only a stale `.olean` |

### Important non-mismatch about the 103 set

It would be wrong to require every monomial in an adapted pivot lift to have
derivative shape inside the 103 set. For a terminal origin,

```text
d = E+R+S = f+r+s,
h = J-r-s-f,
d+h = J.
```

On the 103 corner, `r+s<=16` and survival gives `f<=59`, so `d<=75<J`.
After the common passive shift to total grade `L`, the adapted lift remains on
the final total shell but at lower active grade. The deletion predicate does
not remove it. Thus source expansions leaving the 103 derivative polygon are
not by themselves a counterexample. The real obligation is the typed
passive-shift/window/confluence theorem, which has not been proved.

## 2. Commit-by-commit audit

### `ac53954`: all-Hasse closure

What it proves or checks:

* Exact executable enumeration: the agreement-only corner has 105 shapes;
  requiring one arbitrary scalar value per error node leaves 103, losing
  `(5,7)` and `(1,8)`.
* Exact executable counts on the 103 set:
  `676,776+21,049` q=0 capacity/pivot origins and
  `10,498,193+49,007` positive-q origins, with zero local obstructions.
* Lean proves only the monotonic arithmetic
  `margin(q)=margin(0)+gq`, `T(q)=T(0)+q`, survival monotonicity, and the
  numerical sum `103`.

What it does not prove:

* the 103-shape enumeration in Lean;
* a linear map whose kernel is exactly the retained source;
* all literal lower-`h` error branches;
* tail cancellation or a confluent mapping cone;
* any `F0..F3` containment or Full187 CS4 statement.

The phrase “all-Hasse” should therefore be read as “all coefficient-Hasse
orders of the terminal agreement-principal face,” not “all contact terms.”

### `b71edd7` and follow-up `f005db9`: restricted literal controls

The script's deletion predicate is semantically correct:

```text
terminal_last_shell := y+r+s == J and y+r+s+z == L.
```

It does not accidentally delete unsafe derivative shapes at lower active
grades. It also constructs the all-node contact matrix before dropping source
columns, so target rows that lose support are not silently discarded.

The controls prove exact finite facts only. Blanket contact surjectivity at
zero boundary is red, while fraction-field rank four and coefficientwise
`F0..F3` containment are green, including the near-tight control. This is
good evidence that packet specificity matters.

But every retained-bad packet control takes `u1=Lambda_H` with the first
`w+1` agreement nodes as `H`. Hence `q_H=0` and

```text
F3 = B*Y.
```

The strict-window term `-B*Z*q_H` is absent. The different primes,
multiplicities, and safe/unsafe chambers are not independent tests of that
mechanism; they share the same degeneracy. These controls do not yet validate
the hard fourth packet.

### `f7330e6`: exact F3 versus naive Z

This correctly stops pure constant `Z` and bare `Lambda_G Z` as replacements
for the fourth packet. It shows exact coefficientwise correction of
`F0..F3` in one nonzero-domain F7 full-source control. It is not a 103-source
test, and again `q_H=0`, so it does not exercise the coupled Z tail.

### `a6057a3`: affine translation of the pure-Z defect

The coordinate-change argument is mathematically useful: downward-closed X
windows are translation invariant, and translating all data cannot repair
pure constant-Z membership. The exact m5 ranks are finite evidence.

After `f7330e6`/`14c7712`, however, pure Z is known not to be the target.
Further affine-origin work on this class is a diagnostic rabbit hole, not a
route to Full187.

### `14c7712`: target correction

The correction to

```text
B  = Lambda_H^(m-1) Lambda_(G\H)^m,
F3 = B*(Y-P-(Z-gamma)q_H)
```

is correct, as is the determinant mechanism using
`U1-q_H=Lambda_H*T`. The discussion overstates one point: direct
coefficientwise containment of the four prescribed packets is a strong
constructive sufficient condition, not the logically smallest Full187 gate.
The actual gate is surjectivity/rank four of the candidate boundary map over
`K(X)`.

## 3. Live matched m4/m5 discriminator

The current exact F101 run uses `Q=Xi_error^2`, so its anchor interpolant is
nonzero and it is materially more informative about F3 than the qH-zero
restricted controls. It remains a tiny full-source control, not a target
proof.

```text
matched m4:
  grade-J prefix rank                    1351
  four-packet quotient rank                 1
  packet plus pure carrier rank             1
  each of (0,0), (0,1), (1,0) shell groups closes all packets

matched m5:
  grade-J prefix rank                    2296
  four-packet quotient rank                 4
  packet plus pure carrier rank             5
  (0,0) shell group closes all four packets
  (0,1) or (1,0) alone leaves joint defect 4
```

This is a decisive STOP for extrapolating the m4 formula
`(Y-QZ)^m Z^k` as a universal connector. At m5 the whole `(0,0)` shell group
still contains the packet frame, but no single canonical pure carrier spans
it. The right abstraction is a matrix recurrence on four atomic packet
residues, with possible extra nuisance classes—not a scalar recurrence.

## 4. Proved, finite evidence, and open

### Kernel/Lean proved

* Generic q-monotonicity and the arithmetic sum 103.
* Exact source caps and agreement contact/source legality for the named
  partial-locator packet, conditional source interfaces, and its nonzero
  determinant under retained badness.
* Abstract equivalence of coupled Schur gain four, complete-kernel boundary
  rank four, surjectivity, and absence of a nonzero dual contact relation.
* Literal contact/base-change naturality, common-kernel finite-family row
  selection, root forcing, candidate injection, and point-ideal height in the
  experimental chain.
* Exact-agreement partition and the conditional adapters
  `ExactActualBadStratumBound -> SelectedBadGivenSetsBound -> ProtocolClaim
  6900`.

These theorems are conditional plumbing; none instantiates Full187 CS4.

### Exact finite/computational evidence

* The target-parameter 103/84 shape ledger and all-q local-origin counts.
* Positive Euler surplus `3,291,273` after the four-row reservation.
* Three qH-zero restricted-source controls with fraction-field rank four and
  coefficientwise four-packet containment, despite blanket-surjectivity
  defects.
* One qH-zero shifted F7 full-source packet control.
* The live qH-nonzero matched m4/m5 full-source discriminator above.

None of these finite ranks transfers to the target field/size uniformly.

### Open mathematical or integration obligations

1. A source-origin-preserving terminal mapping cone for the **literal
   restricted source**, including lower-`h` error branches, every relevant q,
   strict coefficient intervals, passive shifts, and pivot remainders.
2. Uniform Full187 fraction-field CS4 for every exact
   `g=180413,...,262144`, received pair, selected polynomial, and retained-bad
   seed. Coefficientwise `F0..F3` lifts would suffice but are stronger.
3. The typed lemma turning the selected bad-row premise into the nonzero
   F3 determinant premise at each maximal actual agreement set.
4. Jacobian rank four to local minimality/reduced isolation, and a fourfold
   multihomogeneous bound that counts isolated affine points even with
   improper positive-dimensional components.
5. The resulting uniform per-stratum bound (the current endpoint hardcodes
   `5,961,390,816`) and final source packaging/build/verifier audit.

Current packaging warning: `.experiments/Order2ProtocolBadFamily6900.lean`
imports `ProximityPrize.SubmissionLower.Order2Protocol6900`, but this checkout
has no corresponding `.lean` source, only a stale build `.olean`. A green
incremental experimental build is therefore not a reproducible submission
receipt.

## 5. Highest-information next gates

### Immediate cheap falsifier

Combine the two strongest controls that currently miss each other:

* use a matched/nondegenerate direction such as `Q=Xi_error^2`, with
  full-degree nonzero `q_H` and preferably nonzero error offsets;
* perform the exact strong safe/unsafe deletion only at
  `(active,total)=(J,L)`;
* test the four named packets coefficientwise **and** fraction-field CS4 in
  m4 and m5.

This directly tests whether the qH-zero positive controls were misleading.
If coefficientwise containment is red but fraction-field rank four is green,
stop forcing prescribed integral packets and pivot immediately to weak CS4.
If rank four itself is red in a faithful retained-bad control, the proposed
uniform 103 theorem is falsified.

### Most target-faithful source gate

Build the target-characteristic, target-parameter **transposed four-residue
mapping cone** at the smallest unresolved layer (extra charge 13: 33 choices,
three `(f,aE,cS)` types). Carry four separate atomic residues from the start.
The state must retain:

```text
source origin; active and passive grades; all lower-h branches;
coefficient-Hasse order; exact half-open X interval; retained/deleted flag;
four packet coordinates; nuisance quotient classes.
```

Quotient only by already proved Hermite and raw-diagonal pivots. Test both
the strong coefficientwise packet frame and the weak localized four-rank.
Only after charge 13 is green should the recurrence descend through charges
12,...,0. A support-only transitive closure or target-exponent closure is not
this gate: it can silently forget coefficient windows and source provenance.

## 6. Process stops and duplication audit

Stop now:

* more pure-Z, affine-translation, or bare-locator-Z experiments;
* more qH-zero toy chambers unless they test a new deletion/window invariant;
* the one-carrier connector after the matched m5 rank `4 -> 5` result;
* blanket contact-on-zero-boundary surjectivity;
* treating Euler surplus, local reachability, or target-side remainder support
  closure as packet containment;
* re-formalizing common-kernel/base-change/packet-legality plumbing before the
  literal CS4 producer exists;
* polishing a 6900 submission package before the exact-stratum theorem is
  inhabited.

Do continue:

* four atomic residues, strict windows, and source provenance;
* one cheap nondegenerate restricted control as implementation acceptance;
* then the target charge-13 transposed gate;
* dual and primal outputs together, so a red result yields an explicit
  separator and a green result yields an auditable recurrence.

The strategy targets `SelectedBadGivenSetsBound` only through this chain:

```text
uniform Full187 CS4
  -> four common equations per exact-g bad family
  -> isolated-point bound per exact g
  -> ExactActualBadStratumBound
  -> SelectedBadGivenSetsBound
  -> ProtocolClaim 6900.
```

Today only the arrows and consumers are mostly formalized. The first node and
the isolated-point count are not. Reporting the 103 local license as a large
percentage of the benchmark proof would therefore be misleading.
