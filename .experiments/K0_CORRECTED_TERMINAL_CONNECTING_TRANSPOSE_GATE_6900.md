# K0 corrected final-three connecting-transpose gate

Date: 2026-09-15 UTC. Scope: lower-6900 finite exact mechanism audit. This
changes no production file, score, candidate, or submission.

## Verdict

**GREEN for the original finite m8 mechanism chamber, under the accepted
formal contact and Hasse boundary conventions.** The old complete source has
a one-dimensional boundary cokernel. The passive-only successor connecting
transpose has rank one and kernel zero. Restriction to the final three
ordinary epsilon orders, modulo restrictions of pure contact annihilators,
also has rank one and kernel zero. The two kernels are exactly equal.

This supersedes, but does not retroactively validate, the withdrawn numerical
receipt in commit `11e1c94`. The new calculation is independent and faithful.
The old receipt remains withdrawn because it filtered compressed rows by `q`
and used ordinary `P''` at the boundary.

The result is **not** a target theorem. It does not construct the target m47
passive producer, establish the target boundary cokernel dimension, or lift a
target associated-face kernel through the single global old image.

There is also an important projection mismatch with two existing formal
receipts. `depth47_lastThree` really uses contact coefficients
`eps^44,eps^45,eps^46`, so its complementary head is `eps^0,...,eps^43`.
`K0TerminalDualDetection.target_head_ge_three_dimension_margin` and
`K0HeadKernelThreeAxes6900` instead study the opposite projection
`eps^3,...,eps^46`, obtained by removing the *lowest* three orders. Their
compiled arithmetic and abstract linear-algebra statements remain valid, but
they cannot be cited to transport this corrected final-three GREEN result.
The target now needs a new low-head (`eps<44`) boundary-surjectivity argument.

## 1. Correct semantics

The executable is

```text
.experiments/k0_corrected_terminal_connecting_transpose_gate_6900.py
```

Every reported rank is computed from the literal flattened substitution

```text
X -> x + eps
Y -> u0 + u1*Z + eps*R - eps^2*S + eps^3*T       modulo eps^m
```

with local rows ordered

```text
(node, eps exponent, S exponent, T exponent, R exponent, Z exponent).
```

The boundary gradient is evaluated in script coordinate order `(Y,R,S,Z)` at

```text
(Y,R,S,Z) = (P, P', Hasse_2(P), gamma) = (P,P',P''/2,gamma).
```

The script also checks deterministic source samples coefficientwise against
the compressed oracle after the exact conjugacy

```text
(q,E,V1,V2,Z) -> (eps=q+3*E, S=V2, T=E, R=V1, Z),
formal coefficient = 2^(V2-s_raw) * compressed coefficient.
```

Thus the final-three filter is on the actual epsilon weight `q+3E`, never on
`q` alone. Primitive `Y,R,S,Z` columns and their four boundary coordinate
gradients are asserted before any rank is interpreted.

## 2. Invariant being tested

Let `C0 : S0 -> T` be the old complete contact map and
`B0 : S0 -> Boundary4` its boundary map. Put

```text
I0 = B0(ker C0).
```

Let `C+` and `B+` be the maps after adjoining only the new positive-passive
columns. Let `Chead` retain precisely the complement of the final three
epsilon orders. Define

```text
I+    = B+(ker C+)
Ihead = B0(ker Chead).
```

Exact finite-dimensional duality gives the three separately reported
quantities

```text
old boundary cokernel dimension          = 4 - dim I0
relative connecting-transpose rank       = dim I+    - dim I0
final-three quotient detection rank      = dim Ihead - dim I0.
```

The kernel of the connecting transpose is the annihilator of `I+` inside the
annihilator of `I0`. The kernel of final-three restriction modulo pure contact
duals is similarly the annihilator of `Ihead`. Therefore the kernels agree
exactly iff `I+=Ihead`. The script checks equality by an exact rank computation
on the two four-dimensional boundary subspaces; it does not infer subspace
equality from matching dimensions.

## 3. Original m8 chamber

The frozen chamber is

```text
field F_101
(n,w,g,m,B,s,U,L_old) = (9,3,6,8,3,1,12,10)
agreement set          = {0,1,4,5,6,8}
candidate/tangent deg  = 3 / 4
old columns            = 11,178
new passive columns    = 1,860
new active L11 columns = 101, deliberately excluded
final-three eps orders = {5,6,7}
head complement        = {0,1,2,3,4}
```

The exact ranks are

| map | rows | columns | contact rank | nullity | `dim B(ker C)` |
|---|---:|---:|---:|---:|---:|
| old complete L10 | 14,535 | 11,178 | 10,861 | 317 | 3 |
| old + passive-only L11 | 16,560 | 13,038 | 12,321 | 717 | 4 |
| old head complement | 5,544 | 11,178 | 4,734 | 6,444 | 4 |

Consequently

```text
old Boundary4/I0 dimension                  1
relative compatible passive coefficient dim 400
full connecting-transpose rank/kernel       1 / 0
final-three quotient detection rank/kernel  1 / 0
Ihead = I+                                  exact: both Boundary4
```

This is the requested nonvacuous equality: the corrected final-three
coordinates detect the same missing fourth boundary direction as the full
relative passive connecting map.

## 4. Adversarial and target-scaled controls

All controls use arbitrary off-agreement received directions and alternating
nonzero errors. The rank triples below are

```text
contact rank / nullity / boundary-kernel-image rank.
```

| case | old | passive extension | head complement | old coker | connecting rank | final-three rank | result |
|---|---:|---:|---:|---:|---:|---:|---|
| small m4, old gain 3 | 984/31/3 | 1224/96/4 | 160/855/4 | 1 | 1 | 1 | GREEN |
| small m4, old gain 1 | 1228/5/1 | 1530/50/4 | 200/1033/4 | 3 | 3 | 3 | GREEN |
| exact target-ratio m5 | 3443/161/4 | 3949/258/4 | 847/2757/4 | 0 | 0 | 0 | vacuous |
| target-ratio ceiling m6 | 4719/45/3 | 5445/178/4 | 1463/3301/4 | 1 | 1 | 1 | GREEN |

The rank-three-cokernel m4 case is an important adversarial check: equality is
not an accident of every nonzero map between one-dimensional spaces. The
three final orders separate all three old compatible boundary-dual directions
and agree with the full passive connecting transpose.

The `m5` scaled control satisfies the exact target shape equations

```text
m=3B-1, s=B/2, U=4B
```

at `B=2`; it is already boundary-surjective and hence cannot test a missing
direction. The `m6` ceiling control at the same `B,s,U` is nonvacuous and is
GREEN. These finite controls reduce oracle uncertainty but cannot establish
scaling to `m=47,B=16,s=8,U=64`.

## 5. Reproduction and receipts

Run controls first, then the larger primary chamber:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_corrected_terminal_connecting_transpose_gate_6900.py \
  --case controls

PYTHONDONTWRITEBYTECODE=1 python3 \
  .experiments/k0_corrected_terminal_connecting_transpose_gate_6900.py \
  --case primary_m8
```

The executable installs a hard `4,200,000,000`-byte address-space cap. The
control suite replay took 45.252 seconds and peaked at 622,596 KiB. The
final primary replay took 260.819 seconds and peaked at 3,107,432 KiB. Exact
regression assertions pin every load-bearing rank above.

```text
script SHA-256              4f6a15df4fc6c77d351f08494af248929359fdf05b8835bdf355530f13a6e995
controls canonical SHA-256  aba7cf6542ca65081740b3f1f10f61b057e7c559564fdfe00524592ec6ce44b7
small m4 gain3 case         fc4ed60e8afc62ac32b8ec20f8b6cf4941d1699a5e9dfe48e973cf3deb8bdc81
small m4 gain1 case         ff688398ff9157acf8efcd7357fea41694ec6c0db80707d42bcb01dde979d4da
target-ratio m5 case        250637628611c1feafc03e33034789ee6d552c5e98d665a148be35d28f514343
target-ratio m6 case        2d23258c1833f4b18263e37577fef1d43aa980e522df5568e919d1ef817b6898
primary case                91ada844e33bdda7fc8b51046dbbf230ed38022920ba36bf04283d5cf15fe6b6
primary canonical          89fedde4798719accf255541c339e4a0a35011d44d963bcdd0921f1739c0c5d0
```

## 6. What is still open

The finite result restores confidence in the *shape* of the three-moment
consumer. It does not supply its target producer. The remaining target-native
statement must show that the actual cap-3757 passive layer realizes the three
terminal adjoint equations, modulo the one global old contact image, on every
compatible target dual. Separately, it must prove boundary surjectivity for
the complementary low head `eps^0,...,eps^43`; the existing high-head
`eps>=3` three-axis/Y witness interface addresses the opposite split. Local
associated-face homogeneity and the 66,420
per-node cap do not by themselves prove this global filtered lift.

The next useful extraction is a small invariant or symbolic recurrence that
forces `Ihead=I+` without constructing either large kernel. Until that is
proved, the target 6900 theorem and submission remain open.
