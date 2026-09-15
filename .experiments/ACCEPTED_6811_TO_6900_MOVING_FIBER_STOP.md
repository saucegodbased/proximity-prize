# Accepted 6811 moving-fiber audit at target 6900: literal retarget STOP

Date: 2026-09-15 UTC.  Audited source commit:
`cdb451f13fdc6c84f5fe363e77ee13a89bd30974` (`origin/main`, accepted 6811).
This is an exact arithmetic/source-interface audit, not a 6900 candidate.

## Verdict

**STOP for a literal retarget of the accepted 6811 construction.**  The
failure is upstream of packing: both independently required interpolation
arms lose strict source dimension when agreement changes from `181284` to
`180413`.  The failure is therefore not repairable by renaming modules,
replaying the old packing receipt, or spending the old ledger margin.

The reusable result is narrower and useful: the abstract moving-fiber
geometry, source-routing interfaces, and finite packing/phase checkers remain
potential infrastructure after a genuinely new target-valid source family is
proved and its tables are regenerated.

## Exact target substitution

```text
n                         262144
accepted errors            80860
target errors              81731
accepted agreements       181284
target agreements         180413
section degree            131071
accepted gap               50213
target gap                 49342
target MCA allowance 254684620614660120
```

The exact budget/ratio checks are formalized in
`Accepted6811To6900FirstDelta.lean`.  In particular, the accepted ledger
maximum `274693043573515013` would exceed the target allowance by
`20008422958854893` if it did not change.  This is a terminal retuning
obligation, not the first failure: the first failures below occur before a
packing ledger can be instantiated.

## First failure in the scalar-list arm

This arm is the dependency

```text
MovingFiberProtocol6811.lambda_le
  -> MovingFiberScalarList6811.exists_seedless_interpolant
  -> MovingFiberScalar6811.interpolation_gate.
```

Its literal coefficient space is the **four-argument** RCN279 source

```text
coefficientCount (115 * agreement) 131071 159 35.
```

The `159` here is really the scalar source's total cap; it must not be
confused with the middle cap printed for principal kernel A.  At 6900:

```text
coefficients                              47353889814
262144 * accepted localRankBound          47862251520
rank side - coefficients                    508361706
```

Thus the target analogue of
`MovingFiberScalar6811.interpolation_gate` is false.  Strict nullity needs at
least one of the following local mathematical improvements:

* add at least `508361707` legal independent coefficients; or
* lower the local rank bound by at least `1940` (about `1.063%`).

This distinct failure is kernel-checked in
`MovingFiber6811ScalarProfileRetarget6900.lean`.

## First failure in the MCA moving-fiber arm

The principal sources in `MovingFiberKernels6811.lean` use the **five-part
ConstraintKernel shape** `(D,w,totalCap,slopeCap,multiplicity)`.  Keeping each
accepted shape but setting `D = multiplicity * 180413` gives:

| kernel | `(m,total,slope)` | target coefficients | `262144 * rank` | deficit | minimum rank drop |
|---|---:|---:|---:|---:|---:|
| A | `(115,274277,35)` | `12985142848514811` | `13125118926520320` | `139976078005509` | `533966363` |
| B | `(134,18992,40)` | `1390207251526060` | `1405157216092160` | `14949964566100` | `57029589` |
| T | `(226,9281,70)` | `3277307768876838` | `3312621160235008` | `35313391358170` | `134709898` |

Kernel A is already a decisive first source failure.  Its target analogue of
`MovingFiberKernels6811.A.nullity_lower` cannot have a positive gap with the
accepted rank theorem.  Strict nullity requires either
`139976078005510` additional legal coefficients or a rank reduction of
`533966363` (about `1.066%`).  B and T fail independently as well.

`Accepted6811PrincipalKernelRetarget6900.lean` kernel-checks all three exact
counts/deficits and the minimal A rank reduction.  This is separate from, and
does not contradict, the scalar-list calculation above.

## Native phase sources

All seven accepted native phase kernel shapes also lose strict nullity:

| source | exact target coefficient deficit | minimum rank drop |
|---|---:|---:|
| 00 | `220090056863886727062784` | `839576938109919461` |
| 01 | `20726846964163996398886` | `79066646439224230` |
| 02 | `18980938035806229038886` | `72406532424187581` |
| 03 | `930640210049624524047` | `3550110664556979` |
| 04 | `58495105198091600080` | `223141117851607` |
| 05 | `19550893759173647` | `74580740964` |
| 06 | `1775385389804909385811` | `6772557791919363` |

The source-00 target residue crosses a row boundary:

```text
64000 * 180413 = 88092 * 131071 + 125468
125468 + 19840 > 131071.
```

Consequently the accepted one-residue closed theorem is not applicable to
that target count.  The replay deliberately uses the underlying exact
RCN100 `coefficientCount` row sum there; applying the accepted closed formula
outside its hypotheses gives a subtly wrong number.

## The 27 relaxed moving-fiber interpolants

All 27 parameter tuples in `MovingFiberCatalog6811` fail target strict
dimension under their exact target-induced caps.  This statement uses the
cap-sensitive `SecondJetRelaxedGlobalMap.rankBound`, not merely the accepted
closed upper bound.

The first tuple P0, `(m,B,s,U,L,k,n0)=(132,54,24,180,1786,5,7)`, fails even
earlier than its dimension comparison.  At `h=5` the target cap is

```text
(132*180413 - 5*49344 + 54 - 1) / 131071 = 179,
```

so the target analogue of `MovingFiberSources6811.P0.cutoff_caps` asks for
the false inequality `180 <= 179`.  Even after using the smaller exact rank
allowed by that cap, P0 has

```text
target coefficients                   2062922226330019
exact cap-sensitive target rank             7954747195
262144 * rank - coefficients            22367022356061
minimum further rank drop                     85323420.
```

The other 26 deficits are all positive too.  The replay script prints every
tuple rather than hiding them behind the P0 representative.

## Identity, packing, and phase arithmetic

`MovingFiberProfile6811.count_of_interpolants` hardcodes the accepted identity
absorption ratio through

```text
scale * 131073 * 80861 * identityDegree <= 50213 * number.
```

The target ratio is strictly worse: `(81732 / 49342) > (80861 / 50213)`, as
proved by exact cross multiplication in `Accepted6811To6900FirstDelta.lean`.
The target phase-band width (`gap+1`) falls from `50214` to `49343`, which can
make some downstream charges cheaper, but it cannot manufacture any of the
missing sources and it does not validate an old identity receipt.

Therefore:

* no accepted source polynomial can simply be assumed at the target;
* all source profiles, identity receipts, potentials, thresholds, and phase
  tables must be regenerated after new source theorems exist;
* the abstract Bellman/packing/receipt soundness code may be reused, but the
  accepted 45,663,660-state numerical certificate is not a 6900 certificate.

## Generator and optimizer provenance

The accepted commit contains the Lean tables and their finite soundness
proofs, but no numerical generator/optimizer source was found by filename,
content, or parent-history search.  Its public Yukon note explicitly calls
the 45,663,660-state calculation an “external calculation” and says the Lean
certificates, rather than that calculation, establish the claim.  The public
commit has the single parent `09d8a2ae2e99404c556888cc18918afb03a94800`.

This does not prove that no private generator ever existed; it means there is
no admitted/public generator to retarget or audit.  Reconstructing the search
would itself be work after the source obstruction is solved.

## Hybridization with same-witness / K0 work

There is no arithmetic plug-in hybrid at present.

* The same-witness no-leaf record is an alternative selected-count endpoint.
  It does not provide a `ConstraintKernel`, relaxed interpolant, source
  profile, or moving-fiber identity receipt.
* The K0 order-seven bivariate approximant supplies a new cap-legal source
  architecture, but its fresh-point boundary readout is still open and it has
  no proved adapter to the accepted moving-fiber consumer interfaces.
* A real hybrid would need either (a) a K0/same-witness theorem producing the
  exact interpolant plus leading-coefficient/cost contracts consumed here, or
  (b) a complete replacement selected-count theorem bypassing this source
  branch.  It cannot reduce the deficits above merely by sharing a witness.

So the accepted construction is valuable as geometry and certificate
infrastructure, but not as a nearly mechanical path from 6811 to 6900.

## Replay

Low-memory exact arithmetic replay (it first asserts every published 6811
source count/rank, then performs the target substitutions):

```bash
python3 .experiments/accepted6811_to_6900_source_replay.py
```

Kernel-check the principal theorem audit:

```bash
lake env lean -j1 -s4096 -M7500 \
  .experiments/Accepted6811PrincipalKernelRetarget6900.lean
```

The principal Lean audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The Python replay takes roughly seven seconds and enumerates no
large state space.

