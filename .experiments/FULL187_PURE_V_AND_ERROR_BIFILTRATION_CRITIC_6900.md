# Full187 pure-V and error-bifiltration critic

Date: 2026-09-13 UTC. Scope: lower-6900 research only. No production,
claim, score, or accepted-6806 file was edited.

## Verdicts

1. The proposed highest-total-covariant-degree argument does **not** force
   `H^60` into every scalar multiplier. At an error node, `V=1+E+...`, and
   the independent `V` displacement `E` has literal contact weight three.
   After selecting the highest total degree and then the highest `V`
   exponent `b`, its distinguished top component sees only
   `a+3b<60`; the coefficientwise conclusion is at most
   `H^(60-3b) | p`. For `b>=20` it yields no error factor.
2. This correction still decisively stops the fixed 21-row **quintic**
   family, because there `b<=5` and hence at least `H^45` is forced. That
   result is separately formalized in
   `Full187ThreeNormalQuinticErrorFiltrationStop6900.lean`.
3. It does **not** stop the full high-degree covariant family. Under the
   corrected charge there are 2,493 source-positive legal triples in the
   target caps. The simplest is pure `V^20`, with no forced `H` factor and
   width 339,020. The mixed endpoint `(b,c,d)=(18,21,0)` still has margin
   170,724 after the visible `H^6` charge. These are surviving source rows,
   not a proof that the terminal RHS lies in their error image.
4. The suggested Taylor-flat multiplicative projectors are locally sound
   but source-impossible. For F0, the proposed `(8,11,10)` product has 29
   active factors. On `W=P=Z=0` every flat unit is `1-Y`, so
   `F0*(1-product)` has `Y^2` coefficient `29*L^59`. Its degree 10,644,367
   exceeds the literal `Y^2` cutoff 10,562,638 by 81,729. Denominator
   clearing only increases coefficient degrees.
5. Polynomial polarization does not repair that multiplicative F0 route.
   If a polynomial projector `S(X,Y)` has boundary value `S(X,0)=1`, every
   positive-Y coefficient of `L^59*Y*(1-S)` contains `L^59`; even the Y²
   strip is already below degree `59g`, so source legality forces all those
   coefficients to zero. Then `S=1`, contradicting its required vanishing
   at normalized errors. Cancellations among unrelated literal source rows
   remain outside this STOP.

## Literal normalized pure-V system

For `L=Lambda_G`, `H=Xi_E`, `Q=H^2`, and `V=Y-QZ`, the proposed ladder is

```text
h = sum p_k L^(60-k) V^k,  2<=k<=60,
    plus p_k V^k,           61<=k<=66.
```

Writing `q_k` for the actual coefficient of `V^k`, every strict source
window is the single uniform inequality

```text
deg q_k + 2*e*k < 60*g.
```

Since `V=1+local` at every error, matching `F0=L^59*V` is exactly the
bivariate fat-point condition

```text
sum q_k(X)V^k - L(X)^59 V in (H(X),V-1)^60.
```

This is a genuine tapered Hermite-Pade problem, not a universal polynomial
identity. The unknown coefficient dimension at the target is 33,673,037;
the ambient error-jet quotient has dimension
`81731*(1+...+60)=149,567,730`. A dimension deficit alone does not refute the
distinguished RHS.

The deterministic script
`full187_pure_v_hermite_ladder_control_6900.py` constructs the exact Taylor
matrix over F_101. Two ratio-faithful finite controls are red:

```text
(e,g,m)=(3,7,8):    matrix/augmented ranks 37/38, kernel 0;
(e,g,m)=(5,11,12):  matrix/augmented ranks 79/80, kernel 0.
```

Canonical output SHA256:

```text
e008084867285482b92f11cf183bf63bf2079adf9dd47e192a682ab503729365
```

These controls are evidence for a restricted-ladder STOP, but they are not
a target theorem. A target conclusion still needs an approximant-basis or
duality proof valid for arbitrary complementary locators.

## Formal countergate

`Full187HighestCovariantDegreeBifiltrationCountergate6900.lean` proves:

* the affine three-normal linear determinant is `L^3`;
* visibility `a+3b<60` implies only `a<60-3b`;
* the degree-21 osculating correction on `V=1+E` differs from the linear
  coordinate by `-(1+E)E^20`, whose literal contact truncation at 60 is
  zero despite a nonzero high-degree term;
* pure `V^20` and mixed `(18,21,0)` survive the corrected source charge;
* every nonzero positive projector coefficient multiplying `L^59` is
  source-red, and killing all such coefficients makes the projector one.

The capped targeted Lean replay is green. Printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`,
`decide`, `native_decide`, or custom axiom.

