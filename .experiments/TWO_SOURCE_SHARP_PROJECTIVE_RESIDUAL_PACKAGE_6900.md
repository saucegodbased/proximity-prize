# Two-source sharp projective residual package (6900)

## Result

`TwoSourceSharpProjectiveResidualPackage6900.lean` proves an exact same-witness
join between two previously separate facts:

1. the sharp two-source scalar refilter, with retained mass
   `263611557201785350` and scalar allowance `W >= 133225`; and
2. the projective-high agreement residual
   `interp(U0 + gamma * U1) - selected gamma = H_gamma * residual_gamma`,
   where `H_gamma` is the locator of the **actual** agreement set,
   `residual_gamma != 0`, and `deg residual_gamma <= 81730`.

The residual is supplied for every `gamma` in the exact `Good` returned by the
sharp refilter.  It is not attached to a separately chosen set of seeds.

The package deliberately retains the literal:

- `D : DataNine U`,
- `A : PrimitiveConicData U D.horizontal.grade`,
- `R : AlignedCrossData U D.horizontal.grade`,
- `Realizes A R`,
- `A.content.natDegree < 16000`,
- grade/rank/coprimality/nonzero-coordinate facts, and
- every source, factor, scalar, agreement, and retained-mass field returned by
  `exists_sharp_retained_fixed_scalar_family_W133225`.

Thus the join does not transplant the sharper retained bound or the residual
onto a different primitive-conic/cross/family witness.

## Construction

The constructor derives the rank-three coefficient shape from
`PrimitiveConicData.rank_three_line_seed_degree_le_two`, invokes the existing
sharp bridge unchanged, and then applies
`projectiveHigh_combination_degree_ge_agreement` plus the generic
`agreement_residual_factor_of_bounds` to each retained seed.  The only
projective input is the existing
`CanonicalHighTailDirectionIndependent IRSProfile.domain U` invariant.

## Exact endpoint fit

The old `ProjectiveHighDataElevenHighEClosedIncidenceLeaf` alone cannot
instantiate the sharp bridge because its weighted-leaf constructor discarded
exactly one needed upstream fact:

`leaf.conic.content.natDegree < 16000`.

`TwoSourceSharpProjectiveHighEIncidenceFrontier6900.lean` now closes this seam.
Its benchmark-facing theorem

`target_bad_family_small_or_twoSource_sharp_projective_highE_leaf`

proves, on the identical input `U/Gamma/agreement/selected`,

`Gamma.card < twoSourceMcaBudget`

or a nonempty enriched leaf.  The caller invokes the upstream weighted
frontier while `content < 16000` is still in scope, constructs the exact
DataEleven/conic/cross leaf, derives projective-highness, and performs the
sharp refilter before any field is discarded.  The enriched leaf has a
definitionally checked `.toIncidenceLeaf` map that forgets only the new sharp
package.

The same file also closes the second packaging seam.  It destructures the
literal `FixedScalarWeightedNoAdjacentHardCornerCondition` and runs the sharp
producer using its exact `B/E0/N0/Q`.  Therefore the sharp output itself keeps

`E0.natDegree < 18415`

and its scalar allowance satisfies the stronger exact window

`133225 <= W <= 149485`.

## Remaining mathematical gap

The joined package is not the missing no-leaf theorem:
it exposes a same-Good Padé/locator system, but no checked cross-seed eliminant
currently converts those varying locators and short residuals into a
contradiction.  Independent per-seed factor counting is insufficient.

## Verification

Both Lean files compile under the capped isolated library shim (about five and
eight seconds respectively).  `#print axioms` for every exported structure,
constructor, forgetful map, and endpoint theorem reports exactly:

`[propext, Classical.choice, Quot.sound]`.

There is no `sorry`, `admit`, `native_decide`, or `unsafe` declaration.
