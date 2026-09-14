# k=0 rank-defect adjoint to direct-HRS carrier gate

Date: 2026-09-14 UTC. Scope: exact-G lower 6900, profile
`(m,B,s,U,L)=(47,16,8,64,3757)` and `D=47*g`. This is a bounded
yes/no audit, not a target rank theorem or submission change.

## Verdict

**GREEN:** rank `<4` gives one nonzero four-boundary functional and one
compatible dual row of the literal complete contact map. No determinant,
cofactor, fixed pivot, or constant-rank assumption is needed.

**RED:** that fact cannot be fed directly into the current error-complement
HRS localization through one agreement-killing partial-locator carrier. The
canonical fourth carrier has top weight `47*g-1`, so even the linear factor
needed to kill its generic boundary value reaches the strict cutoff. The
whole m47 partial-locator/osculating packet has free X window at most 47; at
the lowest exact-G stratum an isolating multiplier must vanish at 81,730
other errors. It therefore cannot be nonzero at the selected error.

This is a precise incompatibility for the requested **direct single-carrier
HRS splice**, not a counterexample to rank four. A coupled recurrence using
lower-weight full-source terms and passive-seed shifts remains possible; it
must perform agreement elimination before the final error localization.

## 1. The cofactor-free rank-defect bridge is complete

Let

```text
C    : V -> (G-contact x E-contact),
beta : V -> K(X)^4,
B    = beta restricted to ker C.
```

If `finrank(range B)<4`, then `B` is not onto, so `B.dualMap` is not
injective. Equivalently there is a nonzero boundary covector `ell` whose
pullback annihilates `ker C`. Mathlib's

```lean
LinearMap.range_dualMap_eq_dualAnnihilator_ker
```

then gives one `eta` with

```text
beta.dualMap ell = C.dualMap eta.
```

This is formalized in
`K0AdjointDualCarrierGate6900.exists_nonzero_boundary_contact_dual_of_rank_lt_four`:

```lean
theorem exists_nonzero_boundary_contact_dual_of_rank_lt_four
    (contact : V →ₗ[k] S) (jet : V →ₗ[k] (Fin 4 → k))
    (hrank : finrank k (range
      (fullKernelFourJet contact jet)) < 4) :
    exists ell : Module.Dual k (Fin 4 → k), ell ≠ 0 /\
      exists eta : Module.Dual k S,
        jet.dualMap ell = contact.dualMap eta
```

For a finite node set, define the literal restriction

```lean
localDual eta x = eta.comp (LinearMap.single k (fun _ => T) x).
```

The compiled identity

```lean
sum_localDual_apply :
  (sum x, localDual eta x (v x)) = eta v
```

shows that this is an actual node decomposition of the same global dual row,
not separately chosen local functionals. Evaluating the adjoint relation on
a source vector with zero boundary jet and zero G-contact gives exactly

```text
sum_(x in E) eta_x(C_E(v)_x)=0.
```

The theorem

```lean
exists_compatible_dual_with_all_error_only_equations_of_rank_lt_four
```

bundles this for every member of an arbitrary literal carrier family. Thus
the old “cofactor compatibility” concern is removed completely. The only
remaining issue is constructing a sufficiently wide legal carrier family
with the two required zero properties and identifying its error blocks with
the HRS coordinates.

## 2. Why the direct agreement-killing carrier cannot be that family

Let `H subset G`, `|H|=w+1`, and `R=G\H`. The fourth agreement carrier uses

```text
B = Lambda_H^(m-1) Lambda_R^m,
F3 = B * (Y-P-(Z-gamma)q_H).
```

For every exact `g`, the top source weight is

```text
deg B + w
 = (47-1)(w+1) + 47(g-(w+1)) + w
 = 47*g-1.
```

Consequently:

```text
degree d>=1 multiplier: (47*g-1)+d >= 47*g,
boundary-killing X-xi:  (47*g-1)+1 = 47*g.
```

Both violate the literal strict cutoff. At `g=180413`, the complement
locator for one selected error has degree `81730`; multiplying F3 overshoots
the cutoff by `81729`.

This is not peculiar to F3. For a standard anchor osculating packet, put

```text
d=i+2r+3s <= m=47.
```

Its legal X shifts are exactly `0<=j<d`; its source weight is `47*g-d+j`.
Therefore every free multiplier has degree `<d<=47`. A polynomial of degree
below 47 which vanishes at the other 81,730 distinct errors is zero, hence
also vanishes at the selected error. The compiled theorem is

```lean
no_m47_partial_packet_multiplier_isolates_one_error
```

in `K0ExactGDirectHrsCarrierObstruction6900.lean`.

The raw source is wide enough before imposing agreement contact:

```text
47*180413 - 131071*64 = 90867 > 81731.
```

So the obstruction is exact: the agreement-killing prefactor consumes the
X window required by the error locator. A raw top-degree strip can hold the
locator but has neither zero G-contact nor, without an additional factor,
zero boundary jet. Passing from that raw strip to the agreement-killing
packet is precisely the coupled PC/seed elimination theorem still absent.
The existing intrinsic-key ordering cannot provide it: its adjacent-grade
confluence implication has a known exact counterexample.

In particular, `HrsGlobalDescendingMomentClosure6900` remains a valid final
step, but its `hsource` cannot be instantiated by multiplying F3 (or any one
m47 anchor packet) by all legal error locators. The complement locator bound
`81730<131071` is irrelevant after the actual carrier window has fallen to
at most 47.

## 3. General nonconstant T is not a first-Newton obstruction

Let `QG` be the degree-`<g` interpolant of `U1` on G and `q_H` the
degree-`<=w` interpolant on H. Existing agreement algebra gives

```text
QG-q_H = Lambda_H*T,  T ≠ 0
```

under retained badness. The new compiled strengthening is

```lean
theorem exists_nonzero_anchor_quotient_with_degree ... :
  exists T : K[X], T ≠ 0 /\
    QG-q_H = locator H*T /\
    T.natDegree < g-(w+1)
```

For the target, `T` can have as many as `g-w-1` coefficients; the tiny
one-extra-agreement chamber happened to make it a scalar `a`. Over the
generic boundary field `K(X)`, however, a nonzero polynomial T is already a
nonzero scalar. The agreement-normal determinant is the forced locator power
times `T`; no selection of a first Newton coefficient is required for that
agreement-side nonvanishing statement.

Thus a correct target recurrence should retain `T(X)` as one field element.
The genuinely nodewise split remains

```text
epsilon_i = U1(i)-QG(domain i):
  some epsilon_i ≠ 0  -> mismatch recurrence,
  all epsilon_i = 0   -> globally matched adjacent-carrier recurrence.
```

Replacing general T by the chamber scalar `a` would discard higher Newton
terms and is unjustified.

## 4. Smallest surviving theorem

The direct HRS carrier route is stopped. A surviving proof has to establish
one coupled statement of the following form:

```lean
theorem k0_coupled_agreement_elimination
  (ell eta hrelation supplied by the compiled adjoint bridge) :
  exists gerr : E -> K[X],
    -- obtained from the restrictions of this same eta
    (forall k in the required depth, forall V in a window containing
       the error-complement locator and all recurrence corrections,
       sum_x reversedHasse_x(V*gerr_x,k)=0) /\
    -- localized leading term
    ErrorMismatchOrMatchedCertificate ell gerr T epsilon
```

It must use lower-weight/full-source and passive-seed columns while cancelling
their G-contact contributions. It cannot be proved by treating the
near-cutoff partial-locator summands independently. The large external seed
range means a mixed X/seed Toeplitz recurrence is not excluded by the X
window obstruction, but its later-error Schur triangularity is new content.

## Verification

Compiled under the task-local 8 GiB cap:

```text
.experiments/K0AdjointDualCarrierGate6900.lean
.experiments/K0ExactGDirectHrsCarrierObstruction6900.lean
```

All printed theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. No broad grid or target-sized dense matrix was run.
