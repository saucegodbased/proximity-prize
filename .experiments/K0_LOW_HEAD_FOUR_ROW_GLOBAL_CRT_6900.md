# K0 four-row global CRT: exact target and route audit

Date: 2026-09-15 UTC. Scope: lower-6900, global half of the corrected
low-head/fresh-probe architecture. This note does not claim a target proof or
change a candidate.

## Verdict

The correct target-uniform theorem is much smaller than independence of the
entire fresh low-head image. If

```text
H : Source -> OldHead
J : Source -> Boundary4
```

are the literal old-node low-head contact and compatible fresh-node boundary
readout, the exact missing assertion is

```text
Surjective (H.rangeRestrict, J)
```

or, equivalently,

```text
Surjective (J restricted to ker H).
```

This equivalence is now proved, axiom-clean, in
`K0LowHeadFourRowCRT6900.lean`. That file also instantiates the literal capped
K0 source (`g=180413`, `m=47`, `B=16`, `s=8`, `U=64`, `L=3757`, and the
accepted weighted X taper) without importing the large accepted aggregate.

The stronger statement

```text
range(H, Probe) = range(H) x range(Probe)
```

implies the four-row statement when the local probe-to-boundary readout is
onto. The implication is also formalized. The converse is false in general
and the stronger target theorem is not currently proved.

## Exact evidence and its limit

The faithful F101 m8 control from `K0_LOW_HEAD_EXTRA_PROBE_GATE_6900.md`
gives

```text
old low-head image rank             4734
compatible extra-probe image rank    526
joint image rank                    5260 = 4734 + 526.
```

The raw syntactic row counts are 5544 and 616, so neither individual map is
onto its raw row universe. This is why all correct statements use actual
ranges. The local readout is nevertheless onto `Boundary4`: the legal raw
columns `Y,R,S,Z` provide four axes, with

```text
FY = [eps^3 T] G
FR = d_R [eps^0] G
FS = d_S [eps^0] G
FZ = d_Z [eps^0] G - u1 FY.
```

Thus the m8 calculation proves the desired four-row quotient statement in
that chamber. It is evidence for the mechanism, not a dimension extrapolation
to the target.

## One-shot Hermite interpolation is RED

Killing 44 epsilon coefficients at every old point by one X-only locator
already requires degree

```text
44 * 262144 = 11,534,336,
```

while the literal raw X allowance is at most

```text
D = 47 * 180413 = 8,479,411.
```

The deficit is 3,054,925. Asking a uniform depth-44 Hermite interpolation at
the fresh point as well costs 11,534,380, a deficit of 3,054,969. Both
calculations are kernel-checked in the Lean file.
The finite m8 witness `Omega_nodes^(m-3) * Z` works only because its analogous
degree is 45 below the finite allowance 48. It is a non-scaling artifact and
must not be promoted.

## Accepted machinery audit

Three accepted interfaces are genuinely relevant:

1. `HrsCrtPairingBridge6900.hasseJetEquiv` is a full variable-depth Hermite
   equivalence. It can prescribe arbitrary Hasse residues at distinct nodes,
   but its output has the sum-of-depths degree bound. Used naively at depth 44
   it hits the RED calculation above.

2. `NodalRankTopCoefficientSurjectivity6900.
   exists_kernel_with_prescribed_top_coefficients` says that full row rank of
   a one-plus-J-word nodal matrix lets one append arbitrary leading
   coefficients while correcting all node values with lower coefficients.
   This is the right *shape*: pay for the old-node cancellation using an
   already-surjective lower block, and reserve only terminal coefficients.

3. `ActualNodalSliceRankSource6900.actual_sharper_top_surjective` specializes
   the preceding theorem to two active words and prescribes three leading
   coefficients in an actual nodal module. It is axiom-clean and target-sized.
   However, its current specialization is to `ConicSeedField`, `actualNodes`,
   `actualWords`, and degrees `212803-j` / `81732-j`. There is no proved map
   from this nodal module into the capped K0 raw source that intertwines its
   node equations with the 44-layer low-head contact.

Consequently, citing `actual_sharper_top_surjective` directly would leave the
main mathematical gap hidden. The smallest missing bridge is a K0-specific
causal recurrence adapter, not another rank count.

## Six hub-and-spoke constructions

No new large matrix was evaluated while generating these routes.

| route | construction | viability | information value | main risk |
|---|---|---:|---:|---|
| A: 3+1 nodal shipment | Route the three eps0 derivatives `(R,S,Z-u1Y)` through the accepted two-word top-coefficient theorem, and route `[eps^3 T]` through one adjacent scalar layer. | 6/10 | 9/10 | missing K0-to-nodal intertwiner |
| B: four sparse actuators | Start from legal `Y,R,S,Z`; multiply by staggered agreement-locator grades; cancel induced old rows by error CRT; check only the final 4x4 Schur block. | 7/10 | 8/10 | corrections may cross the q13 taper ceiling |
| C: dual customs audit | Assume a nonzero boundary covector lies in the old-head dual span, propagate it down the terminal recurrence, and contradict too many agreement zeros. | 7/10 | 10/10 | must prove the propagated certificate has degree at most the retained-bad threshold |
| D: layerwise cross-dock | Cancel old contacts one epsilon layer at a time with agreement/error CRT, reusing lower layers causally instead of paying one depth-44 X locator. | 8/10 | 9/10 | exact triangular K0 recurrence still unstated |
| E: passive-Z peeling | Triangularize in Z degree, reserve four primitive columns at the end, and use one error-value correction per epsilon layer. | 6/10 | 7/10 | passive shifts can consume L and active caps before the terminal layer |
| F: single-syndrome last mile | Combine the existing rank-three old boundary theorem with only one fresh covector/actuator, rather than proving all four rows at once. | 8/10 | 10/10 | depends on clean compatibility with the existing rank-three carrier |

Routes A and D describe the same likely scalable engine from opposite sides:
A is the endpoint/top-coefficient view; D is the causal layer-by-layer view.
Route F is the smallest consumer and should be preferred if the existing
rank-three proof is already connected to exactly the same source and head.
Route C is the best falsification/proof audit because it detects a genuine
global relation without constructing a huge primal matrix.

## Recommended next theorem

Do not attempt full fresh-probe interpolation. Prove a four-output (or, after
splicing the existing rank-three result, one-output) K0 recurrence lemma of
the following form:

```text
For every requested terminal vector b : Boundary4,
there is a legal capped raw source F such that
  oldLowHead(F) = 0
  freshReadout(F) = b.
```

The implementation should factor through an explicit small coefficient
space `C`:

```text
C --actuator--> K0RawSource
|                 |
oldCorrection     | oldLowHead
v                 v
old rows  =       old rows

C --endpoint--> Boundary4
```

and prove:

1. `actuator` preserves every dependent raw cap and the q13 X taper;
2. `oldLowHead.comp actuator = oldCorrection` coefficientwise;
3. the accepted nodal/HRS theorem makes `oldCorrection` cancellable using
   lower/earlier coefficients;
4. `freshReadout.comp actuator` has a unitriangular 4x4 endpoint (or one
   nonzero scalar after the rank-three splice).

This is the smallest interface that closes the global gap and is compatible
with verifier constraints. It avoids the 213-million-dimensional fresh
contact codomain and never relies on source dimension.

## Process guardrails

- A finite rank equality is a mechanism test only; it is not a target proof.
- Every proposed actuator must be checked against all five dependent caps
  before any interpolation theorem is invoked.
- Every use of nodal top-surjectivity must exhibit the map into the literal
  K0 raw source and an intertwining equation with `oldLowHead`.
- Reject any construction whose X cost contains `44*n` before investing in
  formalization.
- Keep all computations sparse and below 4.2 GB; no target dense matrix is
  needed for the four-row theorem.

## Lean receipt

`K0LowHeadFourRowCRT6900.lean` compiles under the capped runner. Its three
proved theorems report only the accepted axioms `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`, `native_decide`,
or `decide`.
