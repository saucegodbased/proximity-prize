# Full187 lacunary fat-graph and reverse-Hasse dual interface

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production and the
accepted 6806 submission are unchanged.

## Verdict

The 60 descending Pascal equations behind the complete-depth projection are
the coefficient expansion of one closed lacunary identity:

```text
(Y-U)^60 * sum_(i=0)^22 binom(59+i,i) U^i Y^(22-i)
  = Y^82 + sum_(f=0)^59 c_f U^(82-f) Y^f,

c_f = (-1)^(60-f) binom(82,f) binom(81-f,22).
```

All coefficients of `Y^60,...,Y^81` vanish.  At a fixed node, take `U` to
be the constant-jet lift of the received value `u1(x)` and multiply by the
terminal coefficient polynomial `C`.  The desired local coefficient jets are
then exactly

```text
H_q(P_f)(x) = c_f * u1(x)^(82-f) * H_q(C)(x).
```

The executable checks that these scalars satisfy every one of the 60
descending Pascal recurrences over `F_2130706433`.  Thus the 126,315 residual
blocks are filtered realizations of one fat-graph relation, not arbitrary
independent row targets.  This explains both why the raw row-surjectivity test
in `b05608c` was too strong and why all its left duals vanish on the actual
residual in `b535ccc`.

This is not yet a strict-window solution.  The constant-jet representatives
can exceed the legal degree of `P_f`; the known `f=8,q=26,C=1` counterexample
still rules out simply taking every canonical all-node representative.  The
remaining question is precisely whether multiples of the graph-domain
generator can move this one relation into all tapered windows.

## Fat-graph formulation

Let

```text
Omega(X)=X^N-1,
U(X) = the degree-<N representative of the frozen u1 values,
I = (Omega(X), Y-U(X)).
```

The N graph points are pairwise comaximal.  Requiring all mixed Hasse
derivatives of total order below 60 to vanish at them is equivalently
membership in the fat graph ideal `I^60`.  The terminal problem asks for an
element

```text
F = C(X)Y^82 + sum_(f<60) P_f(X)Y^f in I^60
```

with the exact Full187 degree bound on every `P_f`.  The lacunary identity is
the local solution using only `(Y-U)^60`; adding generators
`Omega^a (Y-U)^(60-a)` is the algebraic form of the fringe/confluence freedom.
This is the right global object for the next computation.

## Exact dual interface on the multiplicative domain

The recent explicit dual formula for hyperderivative Reed-Solomon codes says
that dual Hasse orders are reversed and then changed by a local upper-
triangular matrix.  Treating the dual as a same-order Hasse code is false.
The formula used here is Theorem 8 of Li--Zhu--Fang--Zhang--Hu,
[Duality and Reverse Self-Dual Constructions for Hyperderivative
Reed-Solomon Codes](https://arxiv.org/abs/2607.19905) (2026).

For our domain the correction is especially small.  If `alpha^N=1`, put

```text
B(z)=((1+z)^N-1)/z.
```

For multiplicity `s` and
`A_alpha=((X^N-1)/(X-alpha))^s`, direct Taylor expansion gives

```text
H_l(1/A_alpha)(alpha)
  = alpha^(s-l) * [z^l] B(z)^(-s).
```

The bracketed scalar is independent of the node.  The executable constructs
and checks every truncated inverse series for `1<=s<=60`.  Therefore a strict
window cokernel can be represented by a low-degree dual polynomial, reversed
Hasse order, powers of `alpha`, and at most 60 universal scalars—there is no
need to materialize an enormous dual matrix.

## Next decisive gate

Use the corrected reverse-Hasse dual to pair the lacunary target with each
strict coefficient-window cokernel.  The first such nontrivial pairing is the
`54,086`-dimensional `P58/P59` gate already proved full rank in `b535ccc`.
The next audit must propagate this through all `f,q` layers and either:

1. construct a filtered representative of the single lacunary relation; or
2. emit the smallest explicit nonzero dual polynomial obstruction.

Only after that should the `u0` connecting tail and four-packet bridge be
reopened.

## Reproduction

```bash
python3 -B \
  .experiments/full187_lacunary_fat_graph_dual_interface_6900.py
```

Recorded run:

```text
exit 0; peak RSS 16,272 KiB
canonical sha256 7c6c173dd5c6a98e919039f2d049d59164bfc3694760e4ebe11fba39580c6324
script sha256    abed6b824010c96293adae07421fb256540234b8861571cff95f684ab491678a
```
