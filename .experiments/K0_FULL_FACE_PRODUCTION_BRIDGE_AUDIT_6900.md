# K0 full-face production bridge audit

Date: 2026-09-15 UTC. Scope: lower 6900 only. This audit changes no
submission, score, or claim.

## Verdict

The new production bridge is **GREEN for its local ingredients** and **YELLOW
as a target associated-rank theorem**. It proves an exact homogeneous,
injective, complete-contact-zero local family of cardinality 24,948 inside a
local exact-degree source slice of cardinality 91,368. The arithmetic
difference is 66,420 per node. The file does not yet define the actual global
cap-3757 associated-face map or prove that its image factors through the
direct sum of these local maps. Therefore 23,088,879 remains a conditional
associated-kernel lower bound, not a proved global relation and not a rank-four
boundary claim.

## Semantic check against production localization

The inspected production definitions use

```text
global Y -> u0 + u1 Z + epsilon A
local  A -> R - epsilon S + epsilon^2 T
```

and hence the literal contact

```text
Y -> u0 + u1 Z + epsilon R - epsilon^2 S + epsilon^3 T.
```

`weightedVector_passiveDegree` uses both the positive and negative passive
weight bounds to prove equality, not merely an upper bound. Outer truncation
only removes epsilon coefficients, so it cannot introduce a lower passive
grade. `kernelFaceMake_injective` is inherited from the production triangular
initial-term theorem, and `kernelFaceMake_zero` uses the exact production
budget `r + 2a + b = m`. These facts support the local kernel count.

They do **not** supply independent global old corrections at the nodes. The
actual lift obstruction is still

```text
ker(top) -> Wlo / range(global old contact).
```

The m4 exact counterexample in `e522925` has obstruction rank 15 with two
errors and rules out treating local associated relations as automatically
globally liftable. The abstract obstruction and combined-connecting files keep
this distinction correctly and do not prove target rank four.

## Corrections made

1. The target face is cap 3757 over cap 3756. The earlier sibling file and
   note called the numerically identical stabilized slope the `3758 \\ 3757`
   face and even proved legality at cap 3758. They now state and prove the
   actual target `3757 \\ 3756` specialization. Its deterministic receipt now
   records `(oldCap,newCap)=(3756,3757)`.
2. A negative Nat margin had been encoded as
   `a - b = 0 - deficit`, which reduces to the vacuous equality `0 = 0`.
   It is now the information-preserving additive equality
   `a + deficit = b`.
3. The 91,368 source receipt no longer uses one large `decide`. At the target,
   the inner `h+y+r <= 64` cutoff follows from the finite-index bounds; after
   proving that fact with `omega`, Lean normalizes the much smaller closed
   sums. The remaining 24,948 kernel receipt is a compact `decide`, not
   `native_decide`.
4. Axiom printing now covers the injectivity, homogeneity, contact-zero,
   cardinality, and arithmetic lemmas rather than only the final arithmetic.

## Verifier/readiness audit

- `K0FullFaceCoupledCap6900.lean` imports only the permitted production module
  `ProximityPrize.SubmissionLower.LowerGeometry`.
- The abstract obstruction files use bare experiment imports. They are valid
  research modules but are not a flat submission root as-is; any candidate
  must copy/rename the reachable helpers into `SubmissionLower` and rerun the
  import-policy and size checks.
- No audited file contains `native_decide`, `sorry`, `admit`, an explicit
  `axiom`, or `unsafe` declarations.
- An isolated replay of the remaining compact kernel `decide` passed under
  `-M3500` and printed only `propext`, `Classical.choice`, and `Quot.sound`.
- The corrected sibling associated-face file passed under `-j1 -M3500`; all
  printed axioms were the same expected three (arithmetic receipts used only
  `propext`).
- The full production-module replay is recorded separately when
  `LowerGeometry` and the bridge finish under `-j1 -M4200`.

## Exact remaining formal chain

1. Package the 91,368-dimensional local exact face and its 24,948-dimensional
   kernel as an explicit local rank theorem.
2. Define the actual global cap-3757 associated-face map and prove the
   global-to-local factorization giving rank at most `262144 * 66420`.
3. Bound or kill the filtered obstruction to lift at least one associated
   relation through the global cap-3756 source.
4. Prove that a lift has nonzero image in the missing relative boundary line.

Only after all four steps is there a 6900 candidate worth verifier assembly.
