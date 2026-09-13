# Fixed-scalar/pole aggregation audit (2026-09-12)

## Result

The fixed-scalar producer is a strong structural reduction, but its exported
predicate is not itself a bounded-count theorem.  In particular, an injective
family of sigma-fixed polynomials of degree `W` agreeing with one centre on
`A=180413` of `n=262144` nodes cannot be counted by pairwise root overlap in
the current window.  For the three relevant caps the basic Johnson numerator
is negative:

| `W` | `A-W` | `A^2-nW` |
|---:|---:|---:|
| 132103 | 48310 | -2081158263 |
| 149776 | 30637 | -6714029175 |
| 156003 | 24410 | -8346399863 |

Thus the standard relation bound `N*(A^2-nW) <= n*(n-W)` supplies no upper
bound on `N`.  The fixed-scalar pole data adds one operator witness and
root-freeness for `E0,Q`, but does not presently give a low-degree equation
in the scalar polynomial `B_gamma`, a bounded coefficient rank, or a common
agreement set.  Treating the scalar family as an ordinary fixed-centre RS
list and multiplying by a pole/fibre count is therefore unjustified.

## Exact logical boundary

`SelectedFamilyFixedScalarProducer6900` proves injectivity and preserves every
original agreement set.  `ActualFixedScalarPoleCondition6900` additionally
retains `Q` minimum, coprimality, orbit alternatives, and the window
`132103 <= W <= 156003`.  None of these fields relates two distinct
`B_gamma` beyond their already-known common-node root bound.  The existing
finite-base regular-jet consumer also requires a source-specific polynomial
`q(x,a)` and jet collision theorem; no such producer follows from pole
invariance alone.

This is a stop for the *bare aggregation* route, not a counterexample to the
benchmark theorem.  To revive it, add a proved source-level invariant such as
an affine coefficient subspace of dimension at most 30, a common low-degree
derivative equation, or an explicit pole-residue relation whose fibres are
bounded independently of `p`.  Existing rank work proves the opposite for
the whole retained family in the low-window witness (`rank > 30`), so rank-30
aggregation cannot be assumed.

## Reproducibility

The exact arithmetic is reproduced by
`fixed_scalar_pole_aggregation_audit_6900.py`; it uses only integer arithmetic
and has no finite-field search, evaluator, or verifier claim.
