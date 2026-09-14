# K0 passive-Z ghost / three-moment focus

Date: 2026-09-14 UTC. Scope: lower-6900 exact-G, literal m47 raw source.
Verdict: **GO as a strictly smaller producer target; RED as an automatic
consequence of Ward or of three adjacent seed bands.**

## Focus result

```json
{
  "mechanism": [
    "Restrict the reverse-Hasse consumer to the upward-closed terminal tail i=44,45,46 instead of requesting all 47 coordinate equations.",
    "Adjoin one passive-Z successor layer to the chosen raw packet; at the target this is an actual source subspace, not an enlargement, because active degree is at most 64 while L=3757.",
    "Use the full literal WZ equation on that relative layer, retaining both the u1 times E term and the external-Z predecessor rather than applying the collapsed finite-wedge Stokes sum.",
    "On agreements substitute u1=Q and ask only for the three resulting aggregate adjoint equations; reverse-Hasse product-rule tails remain inside indices 44 through 46 and close by descending induction.",
    "Use Lambda_G cubed times one degree-less-than-e residual to kill agreement values and prescribe arbitrary error values one Hasse level at a time; K0LocatorErrorCRT6900 supplies this value CRT without a 47e Hermite cost.",
    "If the relative passive connecting map produces those three equations for the literal raw contact dual, the existing selected-error localization turns them into three separating functionals on the boundary-compatible dual space."
  ],
  "load_bearing_risk": "The unproved map is the relative passive-layer producer: after quotienting by the old literal contact image, its transpose must hit the three terminal reverse-Hasse equations for every packet-compatible dual. Ward alone does not give this, because a contact dual is only K-linear, adjacent Z bands are independent Krylov tests, and the nodewise u1 factor is polynomial data only on agreements. The route also fails if the actual three residual boundary moments are not represented by the upward-closed tail 44,45,46.",
  "first_test": "In the existing exact F_101 m8 matrix, take P to be the pre-passive packet and Delta_Z to be only legal one-step passive successors, form R={d in Delta_Z | C_Delta(d) lies in im(C_P)}, and compute the induced connecting map d |-> J_Delta(d)-J_P(p) modulo J(ker C_P). In parallel encode the compatible contact duals in reverse-Hasse order and restrict to indices 5,6,7. The binary gate is equality of kernels between the full connecting map and this three-row restriction, together with rank equal to the packet boundary cokernel dimension; one counterexample dual with zero final-three coordinates makes the hybrid RED.",
  "variants": [
    "Use an adaptive terminal tail of length equal to the packet-compatible corank and locator power equal to that tail length.",
    "Ask only for adjoint equality after pairing with the compatible dual, instantiating K0FullSourceShapeRealization for three fixed shape/index pairs rather than constructing pointwise error contact columns.",
    "Use the S*Y^46*R connector to absorb the degree-w-plus-one part of Q while the passive successor handles only the same-grade u1Z leakage.",
    "Replace one common passive layer by three rank-adaptively selected successor bands, then certify a single nonzero 3-by-3 connecting minor.",
    "Run the terminal-tail closure separately for each complete target shape and keep only shapes whose passive successor has a source-legal predecessor throughout the taper."
  ]
}
```

## What is newly GREEN

`K0PassiveGhostThreeMoment6900.lean` proves an upper-tail version of the
reverse-Hasse closure.  If aggregate multiplier equations are known only for
an upper-closed set `base <= i < depth`, then all diagonal moments in that
same set vanish.  Its depth-47 specialization uses only `44 <= i < 47`, so
the hypotheses are exactly three source-equation families; indices 0 through
43 never occur.  A selected-node locator then localizes any of these three
coordinates under the same restricted hypotheses.

The file also checks two literal target receipts:

```text
legal raw shape and z <= 3692  =>  its z+1 successor is legal,
3*g+e = 622970 < 2056934 = width(S*Y^48),
```

and hence the same grade-three error-value certificate fits the wider
`S*Y^47` and `S*Y^46*R` windows.  The value interpolation itself is exactly
`K0LocatorErrorCRT6900.exists_locatorGrade_for_error_values`; no full error
jet interpolation is invoked.

## RED artifacts checked

This route does not reuse the disproved boundary telescope.
`O2WardDiscreteStokesLiteralRed6900` proves that the three truncated Ward
edge forms collapse to the same bottom-edge functional and that the raw
reverse-index weighting leaves interior defects.  It also shows that an
arbitrary nodewise `u1` moment is not automatically a bounded polynomial
moment.  `K0HighYAdjacentSeedStop6900` proves that three consecutive external
Z bands do not force a fourth for an arbitrary K-linear dual.
`K0LiteralThreeCellQuotient6900` proves that the same-grade `u1*Z` cell must
be retained; deleting it recreates the already-falsified pair-only argument.

Thus the passive layer contributes only through its **relative connecting
map on packet-compatible duals**.  Neither source legality, the Ward identity,
nor the three-tail Hasse closure proves that map has full rank.

## Exact missing map

Let `P` be the already controlled raw packet, `P+` its closure under the one
chosen legal passive successor, `C` the literal complete m47 contact map, and
`J` the boundary map.  The required primal map is

```text
delta_Z : {v in P+ / P | C(v) = 0 in coker(C|P)}
          -> Boundary / J(ker(C|P)),
delta_Z([v]) = [J(v-p)]  where C(v)=C(p), p in P.
```

The three-moment theorem needed from the raw source is that the transpose of
`delta_Z`, after the exact raw-adjoint/HRS encoding, is detected by the three
coordinates `i=44,45,46`; equivalently its restriction to those coordinates
has the same kernel as `delta_Z*`.  In the existing Lean vocabulary this is a
three-pair specialization of `K0FullSourceShapeRealization`, with multipliers
from `Lambda_G^3 * K[X]_{<e}`, plus a separation statement for the surviving
packet-compatible boundary duals.  This is smaller than full confluence and
stronger than the local Ward identity; it is the sole unproved arrow in this
hybrid.

## Verification

The new Lean experiment compiles under the existing 8-GiB capped runner in
about four seconds.  Printed axioms are only `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorry`, `admit`, `decide`, or `native_decide`.

