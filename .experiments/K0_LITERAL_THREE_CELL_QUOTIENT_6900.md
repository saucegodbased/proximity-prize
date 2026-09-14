# K0 literal three-cell quotient: old adjacent-depth counterexample repaired

Status: **GREEN as a local/quotient identity; global taper realization still
OPEN**.

## What the old RED gate actually disproved

The literal contact expansion of the source monomial `Y*Z` is not a pair.
It has three terms:

1. the diagonal `Y*Z` cell;
2. the adjacent `u0*Z` cell;
3. the same-PC-grade leakage `u1*Z^2`.

`O2ABR4LiteralAdjacentDepthRed6900` deleted item 3 and correctly showed that
the resulting two-term induction is invalid.  In its exact quotient model
`Rat[X]/(X^3)`, the earlier numerator `1` annihilates the degree-`<2`
window, but multiplication by `X^2` produces a nonzero top pairing.  The
displayed pair-only numerator is `-X^2`.

## Corrected identity

The new module `K0LiteralThreeCellQuotient6900.lean` proves:

* `literal_YZ_three_cell_after_source`: a dual functional killing the
  literal `Y*Z` source column satisfies the complete three-term equation;
* `literal_YZ_three_cell_quotient_relation`: after assigning a quotient
  numerator to each of the three terms, the sum of all three numerators has
  zero quotient-top pairing;
* `critical_three_cell_after_contact`: the critical raw-S packet satisfies

  ```text
  nextY - u0 * base - u1 * nextZ = 0
  ```

  against every functional killing contact order `m+1`;
* `critical_three_cell_quotient_relation`: the corresponding numerator is
  literally `nY - n0 - nZ`, with the next-Z term retained;
* `old_pair_only_counterexample_closes_with_third_cell`: in the exact old
  witness the omitted leakage is `+X^2`, so

  ```text
  -X^2 + X^2 = 0.
  ```

  The pair-only remainder remains nonzero, while the full three-cell
  remainder and its pairing against every polynomial are zero.  Thus the
  published counterexample does **not** survive the corrected recurrence.

All declarations compile under the 8 GiB probe cap and audit to only
`propext`, `Classical.choice`, and `Quot.sound`.

## Target taper/source check

`m47_three_cell_and_SYR_connector_legal` verifies simultaneously, in the
green `(m,B,s,U,L)=(47,16,6,64,5107)` profile, the exact source legality of:

* `S*Y^47` with seed `Z^0`;
* `S*Y^47` with seed `Z^1`;
* the adjacent `S*Y^48` cell;
* the mixed connector `S*Y^46*R`.

The strict X widths used are respectively `2,188,005`, `2,188,005`,
`2,056,934`, and `2,188,006`.  The separately developing raw-adjoint module
names the connector predicate `k0CriticalSYRConnector` and its index subtype
`K0CriticalSYRConnectorIndex`.

## Exact remaining gate

This result removes one concrete logical obstruction; it does not yet prove
6900.  The missing theorem must construct *compatible global quotient
numerators* for the three bands (and connector), with the target X taper,
from a single legal source vector.  Equivalently, it must prove that the
nodewise Hasse/CRT adjoints commute with this three-cell combination while
cancelling agreement coordinates and producing the required boundary
coordinates.  Merely knowing each band is legal, or comparing dimensions,
does not supply that compatibility.

The next falsification criterion is therefore sharp: instantiate the actual
raw-adjoint/common-denominator map on these four legal bands.  A failure of
`nY - n0 - nZ` to stay within the tapered numerator windows is a new RED;
otherwise it is the needed bridge into the global boundary minor.
