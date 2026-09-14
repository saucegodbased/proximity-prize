# Full187 A57 universal high-direction promotion: RED

Date: 2026-09-14  
Scope: exact universal-promotion countergate; no production/submission change  
Decision: **UNIVERSAL_PROMOTION_RED**, while commit `8b1b1fc` remains a valid
`LOCAL_BLOCK_GREEN` for its frozen target instance

## Composition header

```text
goal theorem:
  UniversalHighDirectionBadFamilyBound6900
quantifiers:
  universal high received direction; this countergate is one exact symbolic
  family, not a sampled random instance
frozen data:
  only the literal A57 window dimensions; u1 is changed to X^132103
source map:
  exact A57 quotient A + 37*u1*B in F[X]/(X^262144-1)
consumer implication:
  universal A57 diagonal surjectivity would be one input to the Full187
  reducer; the compiled endpoint cut is commit f8560b5
first unproved outgoing key:
  a structural branch handling low-complexity/high-degree received
  directions, or a reducer which does not require this A57 quotient onto
```

## Exact countergate

The frozen target A57 rescue at commit `8b1b1fc` uses

```text
A + 37*u1*B mod Omega,
Omega = X^262144 - 1,
deg A < 208036,
deg B < 76965.
```

Its size-54108 Hankel minor is nonsingular for the one precommitted target
coefficient sequence.  The compiled endpoint cut `f8560b5`, however,
quantifies over arbitrary received rows and assumes only that the canonical
received-direction interpolant has degree at least `132103`.

Take the exact legal high direction

```text
u1 = X^132103.
```

It has degree exactly `132103` and is nonzero at every point of the
multiplicative NTT domain.  No wraparound occurs because

```text
132103 + (76965-1) = 209067 < 262144.
```

Therefore `A` reaches only exponents `0..208035`, while `u1*B` reaches only
`132103..209067`.  Their union is `0..209067`, so the exact image rank is

```text
209068,
```

and its quotient defect is

```text
262144 - 209068 = 53076.
```

In particular the coefficient of `X^209068` is identically zero for every
legal pair `(A,B)`.  Since the entire source polynomial has degree below
`262144`, reduction modulo `Omega` changes nothing; `X^209068` is an explicit
unreachable quotient vector.

The coefficient obstruction, exact high degree, and root-free evaluation are
kernel-checked in

```text
.experiments/Full187A57UniversalHighDirectionCountergate6900.lean.
```

Its axiom audit contains no `sorryAx` and uses only standard kernel axioms.

## Benchmark-compatible retained-bad witness

This is not merely an irrelevant polynomial.  On any exact set `G` of
`180413` multiplicative-domain nodes, put

```text
U1(x) = x^132103,
U0(x) = -U1(x) on G and choose U0 differently off G,
gamma = 1,
P_gamma = 0,
A_gamma = G.
```

Then `P_gamma=U0+gamma*U1` exactly on `G`.  The restriction of `U1` to `G`
cannot be represented by a polynomial of degree at most `131071`: the
difference would have degree at most `132103` but at least `180413` distinct
roots.  Hence the original bad-row witness is present.  The family has only
one seed and is of course already count-small; the point is narrower and
load-bearing: the high-degree/bad-row hypotheses do not imply the A57
Hankel condition used by the frozen construction.

## Decision

Do not promote the A57 target-instance GREEN into the universal endpoint
chain.  The result at `8b1b1fc` is still exact and useful as a formula/frozen
regression certificate.  To make it theorem-facing, the proof needs one of:

1. a structural dichotomy which counts received directions with deficient
   A57 multiplication map by a separate family argument;
2. a different physical predecessor family whose quotient map is onto for
   every high/root-free direction; or
3. an actual-RHS theorem showing the universal benchmark packet never asks
   for the missing 53,076-dimensional monomial quotient.

Continuing the frozen target lex cascade alone cannot close
`UniversalHighDirectionBadFamilyBound6900`.
