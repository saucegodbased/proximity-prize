# Full187 speedrunner divergence: six high-`V` families and exact best-candidate gate

Date: 2026-09-13 UTC. Scope: lower 6900 only. No production edits, rank
evaluation, or paper rereads.

The installed ADHD skill calls for five isolated generator agents. All four
team slots were already occupied, so this run used the requested speedrunner
frame as a scoped fallback rather than pretending the isolation requirement
was met.

## Brief

The corrected error filtration kills every mixed quintic and every fully
expanded normal row through error-`E` degree 17. The first literal row which
survives the elementary head and seed gates is

```text
H^6 * V^18 * J1^21
```

with 170,724 degrees of pure-seed room. It is not itself error-contact: the
constant part of `V^18` leaves contact order only six. The missing mechanism
must cancel all lower powers in the expansion about the error unit `V=1`.

## Six generated families

1. **Full-domain derivative separator.** Use `Omega=L*H` and
   `s=L*H'/Omega'`, which is zero on agreements and one on errors. Smooth it
   to third order with `sigma=10s^3-15s^4+6s^5`, then pair it with a
   third-order normal unit `U3` in `U3*(sigma-U3)^20`.

2. **Domain-uniformizer Taylor normals.** When the node polynomial has cheap
   derivative inverse, use `tau=Omega/Omega'` and its second-Hasse correction
   to build exact `U2=Y-tau R` and
   `U3=Y-tau2 R+tau2^2 S/2-QZ`, avoiding a generic inverse of `H'`.

3. **High-`V` Bernstein ladder.** Expand an error-centered degree-20
   projector across the first viable bands `b=18,...`, but give each
   `V^b J1^c J2^d` its own minimal locator/error-locator coefficient rather
   than multiplying a fixed `L^59` normal.

4. **`Omega` exchange ladder.** Repeatedly exchange `L*H` for the full-domain
   node polynomial inside adjacent `b` layers, aiming to cancel the wide
   pure-seed tails while retaining the error-unit binomial recurrence.

5. **Polarized high-row descent.** Start with the legal
   `H^6 V^18 J1^21` top row and polarize/differentiate in normal variables to
   create three boundary-linear descendants, restoring lost agreement order
   by transvectant rather than raw locator multiplication.

6. **Paired `J1/J2` seed syzygy ladder.** Couple adjacent high-`b` rows whose
   leading `(E,R,S)` coefficients form a triangular cancellation, using
   `L*H'=Omega'` on error roots to make the `Z` tails cancel without a generic
   CRT inverse.

The first family had the cleanest exact formula and the strongest chance of
collapsing the node-dependent normalization, so it was tested first. The
third and sixth remain the non-product directions after that test.

## Exact test of the derivative-separator family

At a simple error root, `H=0` and differentiation of `Omega=L*H` gives

```text
Omega' = L*H',       s=L*H'/Omega'=1.
```

At an agreement, `L=0`, so `s=0`. The smoothstep has exact endpoint factors

```text
sigma(s)   = s^3(10-15s+6s^2),
1-sigma(s) = (1-s)^3(1+3s+6s^2).
```

If `U3` has order three at agreements and `1-U3` has order three at errors,
then

```text
P3 = U3*(sigma-U3)^20
```

has agreement order at least 63 and error order at least 60. It vanishes at
the candidate graph `U3=0`, and its candidate-linear coefficient is exactly

```text
sigma^20.
```

This is the fatal source term. Since `s` contains `L`, `sigma` contains
`L^3`, hence `sigma^20` contains `L^60`. Any nonzero such coefficient has
degree at least

```text
60g = 10,824,780,
```

while the strict linear-`Y` cutoff is

```text
60g-w = 10,693,709.
```

The row is red by at least 131,071 before paying any denominator or
uniformizer cost. This is a sharp obstruction to the best derivative-
normalized separator product, not just an implementation inconvenience.

The identities, linear-boundary calculation, locator-power divisibility,
and degree STOP are Lean-checked in
`Full187DerivativeSeparatorProjectorStop6900.lean` with only standard
axioms.

## Convergence

- **STOP:** direct `Fi*(1-K)` projectors; single mixed `U1/U2/U3` unit
  products; the derivative-separator smoothstep product above.
- **OPEN, best remaining:** paired high-`b` cross-degree cancellation (ideas
  3 and 6), beginning no earlier than `b=18` and required to cancel its top
  active coefficients *before* applying the source cutoff.
- **Likely trap:** raw `Omega` exchange preserves total polynomial degree;
  it helps formulas and error normalization but gives no degree refund by
  itself.
- **Likely trap:** ordinary polarization loses contact order; multiplying
  back the lost locator power recreates the forbidden head.

The next exact gate is therefore a two- or multi-row high-`b` syzygy whose
entire top source shape cancels polynomially. A pointwise or associated-
graded cancellation is insufficient.
