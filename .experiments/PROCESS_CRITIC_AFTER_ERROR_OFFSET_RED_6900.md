# Process critic after the arbitrary-error offset RED

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This audits the route
through commits `89f519c`, `8a70207`, `7b3dcc0`, `d463af9`, `a64361e`,
`7fe2418`, and `a99c3bc`, together with the corrections through `71f233a`
and `b9ad817`. Production and the accepted 6806 submission are unchanged.

## Verdict

We are overfitting the small controls. The safe103 theorem currently being
tested is false for arbitrary received directions, while the apparent
three-shape repair has exhausted every available shape in one repeatedly used
tiny chamber and contradicts an older complete first-shell control in another.
No further `m=6,7,8,...` run in either chamber is promotion evidence.

The one worthwhile next cycle is the already-identified **target-parameter
charge-13 transposed four-residue matrix**, now with the exact 11 physical
source blocks, their three correlated outputs, strict coefficient windows,
and a precommitted non-low-degree error word. This revives the full187
filtered-map route; it does not revive the falsified restricted-safe103 claim.

## Ranked GO / STOP

1. **GO now — full187 charge-13 transpose, one cycle only.** Work at the
   target characteristic and parameters, preserve physical source provenance,
   and return either checked legal lifts of the four packets or a checked dual
   separator. A rank or reachability receipt alone is not a result.
2. **GO as infrastructure — mixed CRT and the local 103 ledger.** Commit
   `a64361e` proves the mixed agreement-Hermite/error-value CRT and `7fe2418`
   specializes its target width. They justify individual eliminations when
   their hypotheses hold; they do not couple source origins or prove packet
   containment. Likewise the 103 audit is a local license, not a source map.
3. **HOLD — the discussion-530 binary-sector idea.** Commit `a99c3bc` proves
   the charge-13 rectangle/fringe arithmetic, but exponent-diagram agreement
   is not a filtered-ring map. Do not invoke the `C0,C1` order formula until
   actual benchmark `R,S` and the carrier have a regular, filtration-preserving
   initial-form bridge. The transpose below deliberately bypasses this analogy.
4. **STOP — the unrestricted-error safe103 packet theorem as stated.** In
   `5b7a8ed`, changing only the four error values sends weak CS4 from `4/4` to
   `3/4` and gives coefficientwise defects `(1,1,1,1)`, joint defect four.
   Commit `b9ad817` shows that restoring the 49 deleted unsafe columns is
   inert. This is not a missing-face failure.
5. **STOP — more fixed raw-shell or fixed-carrier scaling.** The under-scaled
   `J=5<m=6` three-group shell repairs only `F0` and changes the joint defect
   `4 -> 3`. The better-scaled `m=6` and small `m=7,8` controls are green only
   with all of `(0,0),(1,0),(0,1)`; every proper subset remains deficient.
   There is no ablation reserve from which to infer a stable block.
6. **STOP — submission work.** Neither full187 CS4 nor the isolated-point
   count is proved. Accepted remains 6806.

## Why the small greens do not extrapolate

The baseline nonzero-`q_H` green in `7b3dcc0` placed agreement and error
directions on the same low-degree global polynomial. The offset replay fixes
all source parameters, agreements, packets, and deleted shapes, and changes
only error values; both the weak and strong conclusions then fail. This is a
direct confounder, not ordinary finite-field uncertainty.

The subsequent green sequence still holds nearly everything fixed:

```text
field F_101; N=7; w=3; g=5; two errors; offsets=(3,5);
q=t=1; one first shell; exactly three available derivative shapes.
```

Increasing only `m` through 8 is not an independent robustness axis. At `m=8`
the four packet residues have rank four, each single group has full internal
rank but defect four, `{00,10}` solves only `F1` and has joint defect two, and
only all three groups close. The target instead has

```text
(p,N,w,g,e,m,q,t,J,L)
  =(2130706433,262144,131071,180413,81731,60,21,10,82,2703),
```

with 187 raw derivative shapes, 103 shapes in the proposed restricted face,
positive-Hasse tails, and 2621 passive layers. None of those axes is sampled
by the small sequence. The maximal-degree `m=6` control in `b9ad817` improves
one axis but still has only three errors, a vacuous safe deletion, and all
three available groups load-bearing.

## Duplicate countergates already in the corpus

The current iteration is revisiting an older failure/repair loop:

* `43b3d2a`, `F101_N10_ERROR_OFFSET_GRADE7_CENTERED_COUNTERGATE_6900.md`,
  used the same predeclared offsets `(3,5,7)` and proved the earlier centered
  three-carrier form false for every one of `F0,F1,F2`.
* `e0d8442` and `71a3e44` enlarged that repair to eight order-four
  covariants. Commit `cd384ce` then killed the complete legal full11
  enlargement in a cap-rich chamber with three explicit duals pairing
  nonsingularly with `(F0,F1,F2)`. Renaming a raw three-group union is not an
  answer to that invariant failure.
* `f0ee426`, `f101_n10_m7_first_shell_target_gate_6900.py`, already gives an
  arbitrary-offset `m=7` complete `J -> J+1` countergate: both prefixes are
  contact-injective and all three RHS remain deficient. Therefore a universal
  first-shell theorem is already false, independently of the new small m7/m8
  greens.
* `242891b`, `F101_TRANSPOSED_FOUR_RESIDUE_MAPPING_CONE_GATE_6900.md`, already
  separated coefficientwise filtered residues from fraction-field rank and
  named charge 13 as the next target layer. Its `m=5` replay is the required
  implementation test: THREE-RHS is green while filtered Z1 is red even
  though localized four-rank is green.
* The current corpus also already contains
  `f101_m6_offset_three_shape_connector_witness_6900.py`, which extracts the
  same three-group `m=6` witness and explicitly warns that a dense unrelated
  factorization is only a finite-field coincidence.

Thus the next artifact must implement the target transpose, not write a third
proposal for it or extend the same multiplicity table.

## The one executable next gate

Implement

```text
.experiments/full187_charge13_transposed_packet_gate_6900.py
```

with the following frozen contract.

### Precommitted target instance

Use the exact target field, NTT domain, and parameters above. Take the first
`g` enumerated domain points as `G`, its complement as `E`, and the first
`w+1` points of `G` as `H`. Put `Q=Xi_E^2` and interpolate `q_H` from `Q` on
`H`. Set the actual direction equal to `Q` on `G` and to

```text
Q(x) + x^(e-1) = x^81730
```

on `E` (where `Q` vanishes). Assert before elimination that every error value
is nonzero, the error-offset interpolant modulo `Xi_E` has degree exactly
`81730`, and no degree-at-most-`w` polynomial describes the all-node
direction. This is one fixed falsifier, not a searched random seed. A RED is
decisive for the claimed uniform theorem; a GREEN is only one-layer evidence.

### Physical charge-13 columns

Do not create 33 independent source polynomials. There are exactly eleven:

```text
c_s(X) Y^61 R^(21-s) S^s Z^2621,
0 <= s <= 10,     deg c_s < 76979+s.
```

Hence the source module has `846824` scalar coefficients: a common complete
binary degree-ten rectangle of dimension `11*76979=846769`, plus the exact
fringe `10+...+1=55`. Store it as eleven truncated polynomial streams, not a
dense 846824-column node matrix.

Each coefficient stream produces all three correlated unresolved outputs:

```text
A: (f,aE,cS,h)=(7,6,1,54),
   row (T,E,R,S,Z)=(2,6,21-s,s+1,2675), scalar 603758703;
B: (8,5,3,53),
   row (6,5,21-s,s+3,2674), scalar 693269975;
C: (8,6,1,53),
   row (3,6,22-s,s+1,2674), scalar 642373467.
```

Check in `F_2130706433` that `C=54*A` and `B=C/4`. A column operation must
apply these three outputs together. Preserve the `u1^h` tag, every induced
positive-Hasse/pivot tail, the passive grade, and each half-open X interval.
Quotient only rows whose mixed CRT or sharp-pivot eliminator is already proved
and whose exact width hypothesis is checked at that occurrence.

### Four-residue bordered result

Seed the transpose with the exact `F0,F1,F2,F3` packet covectors. Report both
the coefficientwise packet defects and the localized weak-CS4 rank, but never
substitute the latter for the former. The executable must emit and independently
recheck one of:

* **RED certificate:** a nonzero legal dual annihilating every retained source
  column and all admitted prior eliminators, with nonzero pairing against a
  named packet;
* **GREEN certificate:** four explicit legal truncated-polynomial source
  vectors whose literal contacts and boundaries re-evaluate to the four
  packets, with all eleven windows and three-output correlations checked.

Before the target run, the same code path must replay the `242891b` m5 control
and reproduce filtered THREE-RHS green / Z1 red; otherwise it has silently
localized or dropped a cutoff. Run the target gate under a fixed cap:

```text
prlimit --as=8589934592 --cpu=2400 -- \
  python3 -B \
  .experiments/full187_charge13_transposed_packet_gate_6900.py \
  --self-check-m5 --target-charge 13
```

Decision rule: weak rank below four stops full187 CS4 for this target
instance; weak rank four with a coefficientwise defect stops the prescribed
packet-lift route but permits a separately stated weak-CS4 route; a checked
coefficientwise green authorizes descent to charge 12 and nothing more.
