# Sharp TwoSource agreement-factor semilinear wedge: exact STOP

Date: 2026-09-15 UTC. Scope: lower target 6900, using only repository
artifacts. This does not change production, prove the selected-family bound,
build a candidate, or change the accepted score.

## Decision

**STOP for the unmodified coefficient-Frobenius wedge of the exact agreement
factor.** The construction is algebraically real and same-witness, but it
inherits essentially the entire natural identity debt. At the current sharp
TwoSource retained mass, at least

```text
263611557201785350 - 262144 = 263611557201523206
```

candidates own only nodes on which the wedge is the zero function of the seed,
not merely a nonzero equation that happens to vanish at that candidate.

This audit uses the current TwoSource budgets, not the older projective-high
retained budget:

```text
TwoSource MCA allowance       263836564062556785
sharp exception allowance        225006860771435
sharp retained Good           263611557201785350
```

Consequently a successful count on the sharp scalar branch must force
`Good.card < 263611557201785350` (or pay an equivalent all-branch bound).
The wedge controls at most `262144` active candidates and gives no bound on
the remaining `263611557201523206`, so it does not approach that consumer.

## 1. Exact same-witness construction

For an actual seed `gamma`, write

```text
C_gamma = canonical interpolation of U0 + gamma U1,
P_gamma = the selected degree-at-most-131071 polynomial,
L_gamma = support locator of the actual agreement set.
```

The projective-high endpoint and exact agreement-factor certificate give

```text
C_gamma - P_gamma = L_gamma R_gamma,
deg R_gamma <= 81730,
sigma(L_gamma) = L_gamma.
```

The sharp TwoSource scalar bridge keeps the same original
`U/Gamma/agreement/selected` and supplies, on a freshly retained `Good`,

```text
E P_gamma = a + gamma b + G(c + gamma d) S_gamma,
sigma(S_gamma) = S_gamma,
S_gamma(x_i) = centre_i on every owned agreement node,
sigma(centre_i) = centre_i.
```

The projective-high split is compatible with this larger branch: its small
alternative is already below `254684620614660120`, whereas the TwoSource
counterexample branch assumes at least `263836564062556785` original seeds.
Thus no family or selected-polynomial witness has to be exchanged to use both
facts.

Define

```text
A_gamma = E C_gamma - a - gamma b,
B_gamma = G(c + gamma d).
```

Then on the same seed

```text
A_gamma = B_gamma S_gamma + L_gamma (E R_gamma).       (1)
```

Applying coefficient Frobenius and eliminating the fixed scalar gives the
exact wedge

```text
Omega_gamma
  = sigma(B_gamma) A_gamma - sigma(A_gamma) B_gamma
  = L_gamma *
      (sigma(B_gamma) E R_gamma
        - sigma(E R_gamma) B_gamma).                    (2)
```

So `L_gamma | Omega_gamma` is genuine. It does not assume a common locator,
generic nonvanishing, moving-quotient routing, or a new support.

`ProjectiveHighAgreementFactorSemilinearWedgeStop6900.lean` proves the
abstract factorization (2) as `semilinear_wedge_factor`.

## 2. Why its node equations are identities

Write the fixed affine coefficient rows at an original node `i` as

```text
A0_i = E(x_i) U0(i) - a(x_i),
A1_i = E(x_i) U1(i) - b(x_i),
B0_i = G(x_i) c(x_i),
B1_i = G(x_i) d(x_i),

rho0_i = A0_i - B0_i centre_i,
rho1_i = A1_i - B1_i centre_i.
```

Evaluating the sharp scalar identity at any agreement owned by `gamma` gives

```text
rho0_i + gamma rho1_i = 0.                              (3)
```

Call a candidate active when it owns at least one node at which
`(rho0_i,rho1_i)` is not `(0,0)`. A nonidentity affine equation (3) has only
one seed root, so choosing one active node per candidate injects active
candidates into the `262144` original coordinates. Therefore

```text
#active <= 262144,
#identity-only >= #Good - 262144.
```

For an identity-only candidate `delta`, every node `i` in its actual agreement
set satisfies

```text
A0_i = B0_i centre_i,
A1_i = B1_i centre_i.
```

Because the centre value is Frobenius fixed, for **every fresh seed `z`**,

```text
sigma(B0_i + z B1_i) (A0_i + z A1_i)
  - sigma(A0_i + z A1_i) (B0_i + z B1_i) = 0.           (4)
```

Thus the relation attached to that owned node is the zero seed function. It
cannot be charged as a root of a nonzero eliminant. The Lean theorem
`identityOnlySeeds_semilinear_wedge_eq_zero` proves (4), while
`activeSeeds_card_le` and `identityOnlySeeds_card_lower` prove the exact
counting statement.

At the sharp retained threshold, the formal arithmetic specializes to

```text
#identity-only >= 263611557201523206.
```

This is stronger than the older identity-debt diagnosis and is the decisive
failure for the current TwoSource branch.

## 3. Seed-degree audit

Since `A_z` and `B_z` are affine in `z`, their coefficient-Frobenius images
are affine in `z^p`, where `p=2130706433`. The direct expanded wedge has seed
exponents

```text
0, 1, p, p+1.
```

Its safe univariate degree cap is therefore `p+1=2130706434`; coefficients
may cancel, but that cancellation creates more identity fibres rather than a
uniformly active low-degree equation. For comparison only, one such cap is
already larger than the older source-coordinate nonidentity budget:

```text
42700739 < 2130706434.
```

That older `42700739 / 1121769749` consumer is **not** being transplanted as
the TwoSource endpoint budget. The current STOP is already complete from the
sharp retained identity mass. The degree comparison merely blocks recycling
the old univariate consumer as a shortcut.

## 4. Divergent constructions tested and pruned

The following alternatives were generated before committing to the wedge.
Each was tested against exact in-repository identities rather than credited
from its generic shape.

1. **Coefficient-Frobenius wedge (equations (1)-(2)).** Exact locator
   divisibility survives. It is pruned as a total count because (4) proves
   that essentially all sharp retained candidates see only identity rows.

2. **Trace or norm descent of the same wedge.** Taking base-field coordinate
   projections or a field norm can lower the visible seed degree, but every
   such expression is still zero whenever the parent wedge is the zero seed
   function. It changes the degree ledger but leaves the decisive identity
   mass untouched.

3. **Three-seed affine cancellation.** Barycentric coefficients with
   `sum lambda_j = sum lambda_j gamma_j = 0` give

   ```text
   sum lambda_j L_j R_j = -sum lambda_j P_j.
   ```

   This is exact, but on a triple intersection it reduces to the already
   recorded selected divided-difference/root cap. The available common-node
   moments are below that cap; the agreement factors do not create a new
   global charge.

4. **Complement locator inside the identity universe.** For identity-only
   candidates the agreement support lies in the fixed identity universe, so
   one can replace `L_gamma` by its complementary split factor. The exact
   prescribed-remainder system still leaves at least `24063` relaxed locator
   directions, and counting ambient split components is vastly over budget.
   No compatibility classifier is created by the change of coordinates.

5. **Differentiate at the simple agreement roots.** Formally,
   `(C_gamma-P_gamma)'(x_i)=L_gamma'(x_i)R_gamma(x_i)` at an agreement node.
   But the benchmark supplies value agreement only. Neither `P_gamma'` nor a
   derivative of the received word is shared across candidates, so treating
   this as an extra owned equation would add a hidden jet-agreement premise.

6. **Eliminate the scalar modulo the pole orbit and use the free quotient.**
   The exact coprime-orbit decomposition retains a large arbitrary fixed tail;
   its node values form a seed-dependent word. The agreement factor does not
   make that quotient word fixed, and assuming it does is precisely the
   unsupported routing step already isolated elsewhere.

## 5. Reopening condition

Do not continue by expanding more conjugates of (2), taking its norm, or
building larger minors from the same rows. A viable agreement-factor
continuation must add at least one of the following genuinely new outputs on
the same sharp `Good`:

1. an active relation on the natural identity fibres themselves;
2. a proof that all but fewer than the needed total-count remainder of those
   fibres lie in a separately bounded exceptional class; or
3. a seed-degree descent whose nonzero/identity dichotomy is proved jointly
   with the agreement locator, rather than inherited from `(rho0,rho1)`.

Without one of these, exact divisibility by `L_gamma` is real but has zero
endpoint credit.

## Verification

The accompanying Lean file was checked under the repository's single-process
`-M3500` runner in about three seconds. Its printed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`; the direct wedge-identity lemma does not
use `Classical.choice`. The source contains no `sorry`, `admit`,
`native_decide`, or unsafe declaration.

