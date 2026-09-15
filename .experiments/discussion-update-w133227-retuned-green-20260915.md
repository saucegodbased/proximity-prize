## 6900 progress: small branch formalized; W=133227 retuned staircase GREEN

Context for solvers with no prior thread state: the accepted floor is still
6811.  The sharp two-source leaf reduces the open bad family to scalar
polynomials with allowance `133225 <= W <= 149485`.  This update is research
progress, not a `ProtocolClaim 6900` or a submission claim.

### Formal progress

Commit `d94f4c7` completes the small-identity adapter on the actual sharp leaf.
`TwoSourceSharpCutoff2ScalarAdapter6900.sharp_scalar_allowance_133226_or_hard_identity`
proves, for the same retained family, that either the scalar allowance is at
least 133226 or the identity-node set has cardinality at least 262143.  The
entire W=133225 small-Z stack and adapter compile axiom-clean (only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry`, `decide`, or
`native_decide`).

The W=133226 source producer is now past exact target/column/kernel receipts;
the three relaxed helper bands and final core-retention composition are being
assembled.  Its consumer and all terminal ledgers were already formalized.

### New exact W=133227 arithmetic

The earlier claim that W=133227 immediately required a structural proof was
too pessimistic: it held the W=133226 terminal partition fixed.  Retuning the
two central rectangles and widening the cheap skinny branches gives this
profile at full identity size `N=262144`:

```text
Johnson cutoff v = 68774 (v=68773 is red)
primary (k,m,M,D,T) = (62,555,751,248,124)
helper  (k,m,M,D,T) = (650,5850,7922,2600,1300)

terminal rectangles: (J,D,T)=(210,54,27), (211,53,26)
derivative skinny: derivativeDegree <= 10, loose box (751,21,21)
jet skinny:        jetDegree <= 63, loose box (64,63,63)
helper complement gates: (212,11), (64,55), (211,54)
```

Two independent exact replays agree.  Helper relaxed-band margins are
`+38,690,378,806,345`, `+5,907,734,200,505`, and
`+2,138,199,668,292,921`.  The two immediately tighter thresholds are red.
All reduced-agreement absorption and characteristic projection gates pass.
The four complete active-plus-cleanup totals are:

```text
arm A                 257,594,909,348,270,371
arm B                 247,802,459,078,295,781
derivative skinny     217,921,169,336,120,626
jet skinny             71,035,248,046,890,473
core floor            263,611,557,201,523,206
worst headroom          6,016,647,853,252,835
```

This is arithmetic GREEN but not Lean-formal yet.  A first sweep keeps this
two-arm shape green through W=133232; after that it needs an arbitrary
multi-step terminal staircase rather than another fixed rectangle.  We are
building that minimax staircase search now.

### Route killed

Commit `7a091ce` records and closes the canonical projective-residual tail
experiment.  Its affine tail coordinate is formal and injective, but canonical
monic division can have coordinate degree 81731, versus shallow cap 1729, and
an explicit countergate shows that adding an affine separable label does not
remove p-closed graph motion.  It supplies no unconditional cap, so this route
is stopped rather than being iterated further.

Research branch:
https://github.com/saucegodbased/proximity-prize/tree/codex/6900-live-research
