# K0 compatible locator-lifted tower audit

Date: 2026-09-15 UTC. Scope: lower score 6900 only. This is an adversarial
audit of commits `45889b0` through `20ee01c`, plus a new target-specific
order-seven repair. It is not a `ProtocolClaim`, candidate, build, comparator
run, or submission.

## Executive verdict

There is one new, target-faithful order-seven architecture:

```text
H^37 * (p0 N^6 J + p1 N^5 C1 + p2 N^4 C2 + p3 N^7 Z),
deg_X pi <= M = 81731,
deg_Z pi <= K = 3.
```

At the compatible fresh boundary `J=0`, its four formal gradients are
diagonal in `(dJ,dC1,dC2,dZ)`, with pivots `N^6,N^5,N^4,N^7`. Composing
with the raw `(S,Y,R,Z)` change of coordinates multiplies the determinant by
`-2N^3`, so the boundary symbol is uniformly rank four whenever the fresh
point is outside the old domain and the characteristic is not two.

The large coefficient window is not heuristic. On the actual
projective-high selected leaf, agreement with the selected polynomial forces
the selected received direction to have degree at least `180413`. Its first
reversed scalar coefficient therefore occurs at index at most `81730`, and
the shifted `q*g` face is reached by `M=81731`.

The box is source-cap positive:

```text
unknowns                         4*(81731+1)*(3+1) = 1,307,712
top equations                   (81731+30879)*(3+2) = 563,050
uniform kernel-dimension margin                         744,662
worst active-face slack                                  18,464
```

The remaining order-seven theorem is still substantive: prove that the four
compatible boundary rows survive restriction to this top-cancellation
kernel for every target input satisfying the selected-direction support
hypothesis. Exact structured sparse tests are GREEN at `K=3`; they are not a
proof. Importantly, `K=2` has an exact target-faithful edge counterexample, so
the passive cap increase is load-bearing.

Even a GREEN order-seven theorem would be only one filtered rung. No existing
formal recurrence consumes it to finish K0. The same four-generator linear
lift is dimension-RED already at order eight, and every affine-linear raw
osculant tower is source-RED from order nine. A nonlinear tower remains open,
but orders 8 through 43 and the target final-three producer are not built.

## 1. Exact benchmark fit

The constants are

```text
n = 262144            full evaluation domain
g = 180413            agreement count / agreement-locator degree
e = n-g = 81731       maximal error count
w = 131071            active X weight
D = 47*g = 8479411    strict weighted-X cutoff
```

Let `N=X^n-1` be the full-domain locator and let `H` be the selected
agreement locator. The osculating coordinates have contact weights

```text
J  = Y-U0-U1*Z                         weight 1
C1 = N'J-NV                            weight 2
C2 = N^2 A-2NN'V+4N^2S+(2N'^2-NN'')J weight 3.
```

Therefore the four lifted generators have error contact exactly at least
seven:

```text
N^6 J,  N^5 C1,  N^4 C2,  N^7 Z.
```

At an agreement root, `H^37` supplies 37 additional orders, so the complete
packet has agreement contact at least 44. At an error root, `H` is a unit,
so it has only contact seven. This is an order-seven filtered actuator, not a
one-shot element of the complete old-low-head kernel.

At a compatible fresh boundary `J=0` and `N != 0`, the formal first-gradient
map is

```text
(c0,c1,c2,c3) ->
  (N^6 c0, N^5 c1, N^4 c2, N^7 c3).
```

The existing raw-coordinate change has determinant `-2N^3`. Thus the raw
boundary symbol is injective uniformly; no assumption `C1 != 0` or `C2 != 0`
is used.

What it advances is exactly the seventh error filtration. It does not by
itself solve any error value, preserve error orders 7 through 43, produce the
last three epsilon equations, or imply `TargetFourRowCRT`.

## 2. Why `M=e` reaches every actual selected input

For a selected seed `gamma`, write

```text
Q_gamma = canonical interpolant of U0 + gamma*U1,
deg P <= 131071.
```

The projective-high leaf gives `deg Q_gamma >= 133120`, so `P-Q_gamma` is
nonzero. On the agreement set it vanishes at at least `180413` distinct
points. If `deg Q_gamma < 180413`, then

```text
deg(P-Q_gamma) < 180413 <= number of roots,
```

forcing `P-Q_gamma=0`, contrary to the high-tail inequality. Hence

```text
deg Q_gamma >= 180413.
```

Canonical interpolation also gives `deg Q_gamma <262144`. If
`q=X^-1`, its first nonzero reversed scalar coefficient occurs at

```text
r = 262143-deg Q_gamma <= 81730.
```

The first lifted face is `q*g`, so its first live scalar term occurs by
`q^(r+1)`, at index at most `81731=M`. This is the correction to the earlier
false degree interval based only on the weaker `133120` lower bound for an
arbitrary projective direction. The boundary direction is the selected
`gamma`, and its agreement roots give the stronger degree `g`.

`K0CompatibleBoundaryAndTowerAudit6900.lean` kernel-checks both the root
argument and the reversed-support consequence.

## 3. Top faces, caps, and the passive-degree correction

In the top window shorter than `n`, the actual two-term locator
`N=X^n-1` is represented exactly by its leading term. After alignment with
the `N^7 Z` face, the four normalized series are

```text
-q*g,
-q^2*(theta+1)g,
-q^3*(theta+1)*(theta+2)g,
Z,
```

where `g(q,Z)` is affine in `Z` and `theta=q*d/dq`.

The worst data face is

```text
deg_X(H^37 N^7 Z) = 8510289 = D+30878.
```

After multiplying by an X coefficient of degree `M`, canceling
`M+30879=112610` leading coefficients leaves degree `D-1`. This top window
is below `n`, so no lower `-1` term of `N` folds into it.

The active faces are not canceled. The worst is

```text
37g + 6n + w + M = 8460947 = D-18464.
```

The other two active pivots are one and two degrees cheaper. Passive degree
is at most `K+1=4`, active total degree is at most one, and the literal
`B,s,U,L` caps are therefore loose.

### Why `K=3`, not `K=0` or `K=2`

Dimension surplus does not imply boundary survival. Small exact matrices
show that `K=0` often has boundary increment only two or three. More
importantly, the following edge instance is faithful to the only proved
target support condition:

```text
field F_101, m=4, overhang=5, alpha=89, gamma=18,
g_3=[56,85], g_4=[77,0], g_5=[16,0], g_6=[0,15].
```

The scalar series at `gamma` first lives at `r=m-1=3`, since
`56+18*85=71 !=0`. Exact ranks are

```text
K=0: top/joint/increment = 15/18/3
K=1:                       26/29/3
K=2:                       36/39/3   RED
K=3:                       46/50/4   GREEN
K=4:                       56/60/4
```

Thus `K=2` cannot be promoted. At `K=3`, an independent structured sweep
tested 32,400 families consisting of one prefix coefficient annihilated at
`gamma`, a normalized first live coefficient exactly at `r=m-1`, and one
arbitrary later coefficient, over grids of fresh X/Z points. It found zero
rank defects. A separate conditioned search tested 44,937 denser cases with
zero defects. These are exact modular ranks, but no finite search proves the
uniform target theorem.

The correct next statement is a Toeplitz/approximant lemma:

```text
if valuation_q(g(q,gamma)) <= M-1,
then the compatible four-row map is onto after restriction to
ker(top cancellation), for M=e and K=3.
```

It must be proved by a constructive approximant basis or its transpose
recurrence. It must not be inferred from the `744662` nullity lower bound.

## 4. Regression audit of the original order-seven packet

Commit `45889b0` used the eight pure weight-seven monomials. Its degree
cancellation space is real, but the boundary interpretation was wrong: the
probe chose random `J != 0`, while compatibility forces `J=0`.

At `J=0`, the only first-gradient directions are

```text
J*C1^3, J*C2^2       one common dJ axis,
C1^2*C2              one fixed dC1/dC2 combination,
coefficient Z shifts at most one dZ axis.
```

The covector `(0,C1,-2C2,0)` kills the image, so rank is at most three; at
`C1=C2=0` it degenerates further. Commit `20ee01c` formalizes this STOP and
corrects the probe and note.

The formerly advertised rung-six packet
`J^6,J^4C1,J^3C2,ZJ^6` also has zero gradient at compatible `J=0`. The
alternative `JC1C2,C1^3,C2^2,ZC1^3` has rank four only when
`C1*C2 != 0`; it is not a uniform replacement.

## 5. Exact order-eight and order-nine boundaries

### Linear lift is dimension-RED at order eight

The natural next four-generator packet would be

```text
H^36*(N^7J, N^6C1, N^5C2, N^8Z).
```

Its worst active face leaves only 18464 strict degrees of slack, so any
coefficient box must have `M<=18463`. Its data face has overhang 112609, so
top cancellation needs `M+112610` rows. At the maximal legal M, for every
passive cap K,

```text
4*(18463+1)*(K+1) < (18463+112610)*(K+2).
```

The box has negative dimension before an error row or boundary row is added.
This is kernel-checked in the Lean audit.

### Pure nonlinear order eight is only stratified OPEN

There are ten weight-eight semigroup monomials. The four forms

```text
J*C1^2*C2, C1^4, C1*C2^2, Z*C1^4
```

have compatible-symbol determinant `8*C1^10*C2^2`. A box
`M=15000,K=45` has top-cancellation margin 9952 and active slack 3471, but
the symbol is rank four only on `C1*C2 != 0`. There is no theorem charging or
excluding the two degenerate strata, and no joint-kernel proof even on the
generic stratum.

### The formal tower exists, but the affine-linear raw tower stops at nine

For scalar contact polynomials define

```text
T_r(N,C) = N*C' - r*N'*C.
```

If `X|N` and `X^r|C`, then `X^(r+1)|T_r(N,C)`. The Lean audit proves this
for every r. This is the scalar shadow of the already formal cubic contact
connection

```text
delta = d/depsilon + 2S*d/dR + 3T*d/dS,
delta(Y_contact)=R, delta(R)=2S, delta(S)=3T.
```

So there is no abstract failure to define covariants of weights 1 through
44. The failure is literal raw descent under the source cap.

For any affine-linear raw expression

```text
A*Y+B*R+C*S+data,
```

order-nine contact forces locally

```text
X^6|A, X^7|B, X^8|C.
```

At every distinct old node these factors globalize to
`N^6|A,N^7|B,N^8|C`. The S lane after the required agreement boost has

```text
35g + 8n + (w-2) = 8542676 = D+63265.
```

It is source-illegal even before a coefficient multiplier is charged. Thus
the proposed full **affine-linear** osculant/transvectant tower is precisely
STOPPED at order nine. Nonlinear covariants can share active faces and are
not ruled out by this theorem, but their simultaneous active-face
cancellation is wholly unproved.

## 6. Honest endpoint distance

A GREEN order-seven joint-kernel theorem would not make the route mechanical.
The unresolved work is:

1. Prove the `M=e,K=3` top-kernel-to-four-boundary theorem, and identify the
   exact error-row quotient it also controls.
2. Construct filtered corrections for error orders 8 through 43. There are
   37 post-cliff layers including order seven; only the first has a plausible
   target-faithful packet, and the linear architecture fails at the next two
   stages as above.
3. Prove the target-scaled final-three producer for epsilon orders 44,45,46.
   The existing corrected m8 connecting-transpose computation validates a
   finite consumer shape only; it does not supply the target equations.
4. Splice both producers into the literal low-head boundary consumer and then
   into the same-witness benchmark endpoint.

No existing theorem performs steps 2--4. In particular, neither a local
rank-four symbol, a positive approximant nullity, nor the formal
transvectant recurrence implies the global error-order induction.

## Formal artifact and replay

```text
.experiments/K0CompatibleBoundaryAndTowerAudit6900.lean
```

It proves:

- uniform raw-symbol injectivity for the lifted order-seven packet;
- the selected-direction degree and reversed-support bridge;
- exact `M=e,K=3` dimensions and all source caps;
- the linear lifted order-eight dimension STOP;
- the generic pure order-eight symbol and cap receipt;
- the all-r transvectant divisibility step;
- the affine-linear order-nine divisibility and source STOP.

Replay under a task-local allocator limit below 6 GiB:

```bash
.experiments/run_lean_6g_capped.sh \
  /home/g/proximity-prize-vm-clean-20260901/yukon-6900-work/.experiments/\
K0CompatibleBoundaryAndTowerAudit6900.lean
```

The printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorryAx`, `decide`, `native_decide`, or unsafe oracle.
