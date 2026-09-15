# K0 low-head extra-probe factorization and independence gate

Date: 2026-09-15 UTC. Scope: lower-6900 exact finite mechanism audit. No
production file, candidate, score, or submission is changed.

## Verdict

**GREEN in the faithful F101 m8 chamber.** The complete four-coordinate
boundary gradient factors through one compatible fresh-node low-head contact
probe. The induced readout has an explicit four-axis section. Most
importantly, the fresh probe image is exactly independent modulo the old
nine-node low-head image:

```text
rank old low head                  4,734
rank one fresh compatible probe     526
rank joint old + fresh probe       5,260 = 4,734 + 526
```

This turns the target missing premise into a concrete `(n+1)`-point
low-head strictness/interpolation theorem. It does not prove that target
theorem; the exact run is one finite receipt.

## 1. Why the boundary really factors through contact

Let

```text
G(eps,S,T,R,Z)
  = F(x+eps,
      u0+u1*Z+eps*R-eps^2*S+eps^3*T,
      R,S,Z).
```

Choose the fresh-node anchor so that

```text
u1 = Q(x),
u0 = P(x) - gamma*Q(x).
```

Then the raw graph point `(Y,R,S,Z)=(P,P',Hasse_2(P),gamma)` is represented
inside the local contact chart. For every raw source polynomial, the boundary
gradient is recovered by the following linear readout of `G`:

```text
F_Y = [eps^3*T] G
F_R = d_R ([eps^0] G)
F_S = d_S ([eps^0] G)
F_Z = d_Z ([eps^0] G) - u1*F_Y,
```

where the remaining `(S,R,Z)` variables are evaluated at
`(Hasse_2(P),P',gamma)`. The first identity is the important transverse
channel: ordinary eps-zero graph restriction alone would lose `F_Y`, but the
literal `+eps^3*T` term retains it.

The executable checks this identity coefficientwise on **all 11,178 source
monomials**, using the accepted signs and Hasse-normalized S boundary. It also
computes the boundary image of the kernel of the extra probe and obtains rank
zero. Thus factorization is checked both formula-by-formula and by exact
kernel rank.

The raw source monomials `Y,R,S,Z` are all legal and their local images map to
the four unit boundary axes. Hence the probe readout is surjective. This
argument requires that the low head contain epsilon order three. For the
final-three split this means `m>=7`; it applies to target `m=47` and the m8
control, but not to the m6/m4 controls.

## 2. Joint old-plus-extra rank

The frozen data are

```text
field F_101
(n,w,g,m,B,s,U,L) = (9,3,6,8,3,1,12,10)
agreement set      = {0,1,4,5,6,8}
low head           = eps orders 0,1,2,3,4
terminal tail      = eps orders 5,6,7
fresh point        = x=9
```

The raw row universes and actual image ranks are

| map | syntactic rows | source columns | image rank |
|---|---:|---:|---:|
| nine old-node low heads | 5,544 | 11,178 | 4,734 |
| one fresh-node low head | 616 | 11,178 | 526 |
| joint tagged map | 6,160 | 11,178 | 5,260 |

The codomain qualification is load-bearing. Neither local raw row universe is
fully hit. The exact statement is surjectivity onto

```text
range(oldHead) x range(extraProbe),
```

not onto the larger 6,160-dimensional syntactic row space. Equality of the
joint rank with the sum of the two image ranks is exactly the required
independence/strictness statement after replacing each codomain by its image.

Combined with the explicit surjective readout, this implies that boundary is
surjective on the old low-head kernel in the finite chamber. The abstract
linear algebra consuming this statement is in commit `f14a44f`,
`K0LowHeadExtraProbeBridge6900.lean`.

## 3. Compact finite minor and why it does not scale directly

The companion executable

```text
.experiments/k0_low_head_terminal_minor_extractor_6900.py
```

extracts a concrete 4-by-4 boundary minor. The certified old complete-kernel
boundary basis is

```text
(1,36,0,68), (0,1,0,13), (0,0,1,19)
```

in `(Y,R,S,Z)` order, with annihilator `(1,79,30,25)`. A canonical 39-term
raw relation supported only on `X^a Z` has zero low-head contact, nonzero
contact only in terminal orders 5,6,7, and boundary `(0,0,0,12)`. Its pairing
with the old annihilator is 98 and the resulting 4-by-4 determinant is 12.

This exposes a finite-size artifact rather than a target recurrence. The
relation is the all-node Hermite-locator mechanism

```text
Omega_nodes^(m-3) * Z.
```

At m8 its X degree is `5*9=45 < m*g=48`, so it is legal. At the target the
analogous degree is

```text
44*262144 = 11,534,336 > 47*180413 = 8,479,411,
```

so the same direct locator witness is source-illegal. The compact minor
certifies the finite detector but cannot be extrapolated. The extra-probe
joint-independence formulation is the meaningful target theorem.

## 4. Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_low_head_extra_probe_gate_6900.py

PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_low_head_terminal_minor_extractor_6900.py
```

Both scripts install a hard `4,200,000,000`-byte address-space cap. The first
probe replay took 130.369 seconds and peaked at 1,435,236 KiB. The minor
replay took 76.573 seconds and peaked at 1,132,324 KiB.

```text
extra-probe script SHA-256       71fc1f2507723fd13cb213442784c9ceea4cd231ee0a493bda99097486001d3c
extra-probe canonical SHA-256    64030a86bce5bf9c40e2cda5bb5a591f75db78bfcc295dd044c3591dfe0548c1
minor script SHA-256             35b53329e7652e42dbb6d8b87f0fb2410dbd65320d54c5222e18eda4d2bd0f8a
minor canonical SHA-256          54d2c486e173adf0f04fcd6c7c5bfa3c27e6d675000f9cb7fd96cbd4316de560
minor 39-term relation SHA-256   e236007be55d901d625c2137b3a12312ac68b410dfdc48d99cd196d93d7dc613
minor terminal vector SHA-256    3efae566f31d46a66707c254b63e106d9e637d8ad66a142ba64266403e890961
```

## 5. Remaining theorem

At target scale, define `OldHead` and `Probe` as the actual images of the
low-head contact maps. The new highest-value theorem is

```text
range rank at n old nodes plus one compatible fresh node
  = old image rank + one-node probe image rank.
```

Equivalently, every realizable fresh-node low-head contact vector can be
interpolated while preserving arbitrary realizable old-node low-head data.
The huge target dimension margin makes this plausible but does not prove it;
the weighted X taper and active/passive caps can create global coupling.

A target proof should exploit the polynomial/Hermite CRT structure of the
raw source or exhibit a predictable-degree/row-reduced basis. A larger B=4
full dense replay is not safe under 4.2 GB: the smallest target-shaped source
preflight already has over 62,000 columns before its much larger joint row
matrix. No such run is claimed here.
