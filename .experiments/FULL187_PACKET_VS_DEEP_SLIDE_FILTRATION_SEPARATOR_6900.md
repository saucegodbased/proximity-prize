# Full187 packet versus deep-slide filtration separator

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission roots, score, and radius are unchanged.

## Verdict

The deep Hermite slide in commit `249b160` is a real cross-origin reduction,
and its 33 charge-13 A/B/C principal coordinates remain exactly clean.
However it has **zero raw-row overlap** with any of the exact packet columns
`F0,F1,F2,F3`:

```text
raw packet rows:       Z <= 1,       R+S <= 1;
deep-slide head rows:  Z=2674/2675, R+S >= 21.
```

More strongly, every contact tail of every physical source in the three-layer
slide has `Z>=2621`. At the first actual error node, normalized projection to
the contact scalar row `Z=0` annihilates the complete slide submodule, including
all nonprincipal and lower-grade tails, and pairs the exact partial-locator
`F3` syndrome to one. This is an explicit augmented separator with boundary
covector zero.

It is deliberately **not** a dual for the whole Full187 source: low-passive
source columns do hit the scalar row. It is a rigorous STOP for trying to use
the terminal slide itself as `Rlt13(F3)`. The necessary missing object is now
sharper:

> construct a low-passive correction/precycle for the exact packet, propagate
> every causal higher-`Z` tail, and prove that its terminal tail belongs to the
> deep-slide or mixed pivot/capacity image.

There is also a correction to the interpretation of the `7,282` row count.
Those are row shapes touched by the selected canceled provenance, not 7,282
aggregated coordinates proved zero. Unsupported higher Hasse orders feed 640
of those same shapes. The termwise cancellation in `249b160` is still valid,
and all 33 A/B/C principal rows are genuinely clean.

Artifact:

```text
.experiments/full187_packet_vs_deep_slide_filtration_separator_6900.py
```

## 1. Exact packet-side support

The current packets are

```text
F0 = Lambda_G^59 Y,

F1 = Lambda_G^58 (Lambda_G R - Lambda_G' Y),

F2 = Lambda_G^57
       (Lambda_G^2 S - 2 Lambda_G Lambda_G' R
        + (2 Lambda_G'^2-Lambda_G Lambda_G'') Y),

F3 = B (Y-P-(Z-gamma)q_H).
```

For the frozen target instance used by `11bc654`, `P=gamma=0`, so

```text
F3 = B (Y-Z q_H).
```

It is not a pure-`Z` packet.

The non-`X` source shapes of all four packets lie in

```text
{scalar,Y,R,S,Z}.
```

Coefficient-Hasse differentiation changes only the contact `T` exponent.
The literal order-two local substitution is

```text
Y -> u0 + u1 Z + E + T R - T^2 S/2,
R -> R,
S -> S,
Z -> Z.
```

Consequently every raw packet contact row obeys

```text
Z <= 1,  R+S <= 1,  E <= 1.                         (PACKET-FILTRATION)
```

The executable enumerates the complete shape envelope through contact cutoff
60. Its row counts are

```text
F0 294, F1 295, F2 297, F3 294; union 297.
```

Some literal coefficient combinations can only shrink these envelopes, so
the support separation below does not rely on a noncancellation assumption.

## 2. Exact slide-side support

Commit `249b160` starts with

```text
C_s(X) Y^61 R^(21-s) S^s Z^2621,  0<=s<=10,
```

and uses correction layers

```text
P8_s(X) Y^8 R^(21-s) S^s Z^2674,
P7_s(X) Y^7 R^(21-s) S^s Z^2675.
```

Its selected top-passive transitions are `f=8,q<=25` and `f=7,q<=26`.
For any such contact row,

```text
R+S
 = (21-s + f-aE-cS) + (s+cS)
 = 21+f-aE
 >= 21,
```

while its passive exponent is respectively 2674 or 2675. Thus every one of
the 7,282 selected row shapes is disjoint from `(PACKET-FILTRATION)`.
The exact intersections are

```text
F0 0, F1 0, F2 0, F3 0.
```

This answers the packet-relevance question literally: **none** of the 7,282
selected terminal rows is a raw packet row.

The statement extends from selected heads to every tail by a simpler
filtration. Local contact substitution never decreases the exponent already
present in the outer seed variable:

```text
source Z^z -> contact rows Z^(z+h), h>=0.
```

All three slide layers have `z>=2621`. Therefore their complete contact image,
without dropping or reducing any tail, lies in the coordinate subspace

```text
W_(Z>=2621).
```

Every packet contact lies in `W_(Z<=1)`. These coordinate subspaces are
disjoint.

## 3. Literal exact-F3 augmented separator

Use the actual target instance

```text
p=2130706433, N=262144, G=180413,
U0=0 on G and 1 on E,
U1=Xi_E^2 on G and X^81730 on E,
P=gamma=0.
```

Let `x_0` be error node index `180413`. The selected-seed contact scalar of
the exact F3 is

```text
B(x_0) = 1307960934 != 0 mod p.
```

Define the contact covector `lambda` to be projection onto

```text
(node,T,E,R,S,Z)=(180413,0,0,0,0,0)
```

multiplied by

```text
B(x_0)^(-1)=1664439266 mod p.
```

Take the four-boundary covector `mu=0`. Then

```text
lambda(contact(F3))+mu(boundary(F3)) = 1.
```

Every complete slide tail has `Z>=2621`, so

```text
lambda(contact(slide source))+mu(boundary(slide source)) = 0
```

for all choices of the eleven physical input polynomials and both Hermite
corrections. This includes every one of the 48-million-plus original source
tails; it does not rely on a principal projection or a tail count.

The full F3 error-syndrome hash agrees with `11bc654`:

```text
44284a2ae31b90315699b3f0a14947ea2007114bbd7460485287f2543d5de332
```

This proves

```text
(contact(F3),boundary(F3))
  notin range(complete three-layer slide contact, boundary).       (SEP)
```

The qualifier “three-layer slide” is load-bearing. Low-`Z` columns from the
complete Full187 source do not satisfy the separator equation, so `(SEP)` is
not a no-go theorem for the full producer.

## 4. q26 and the 7,282-row interpretation

The deep slide cancels these selected original provenance terms:

```text
f=8, q=0..25: 12,870 terms on 3,870 row shapes;
f=7, q=0..26: 10,692 terms on 3,412 row shapes.
```

So q26 does occur inside the advertised set: the `f=7,q=26` slice contains
396 terms on 396 rows. None intersects a packet row.

The first unsupported slice is `f=8,q=26`, with 495 terms on 495 rows. Again
none intersects a packet row. But 360 of those 495 shapes already occur among
the selected `f=8,q<=25` shapes. For example, the standard Hasse collision
trades

```text
(source s, cS=0, q=26)
  <-> (source s-1, cS=1, q=25),        s>=1.
```

The complete higher-order audit gives

| family | unsupported provenance | unsupported rows | selected rows hit |
|---|---:|---:|---:|
| f=8, q>=26 | 8,910 | 2,430 | 360 |
| f=7, q>=27 | 7,524 | 2,204 | 280 |

Thus only

```text
7282 - 360 - 280 = 6642
```

selected row shapes are support-clean against the higher-`q` provenance from
these same source lines. This does not retract the termwise cancellation: the
23,562 selected contributions do cancel exactly. It corrects only an
over-strong interpretation that their row coordinates as a whole vanish.

The 33 principal A/B/C rows are disjoint from every one of these higher-order
tails. Their exact principal reduction remains GREEN.

## 5. Process consequence

The terminal operator and the packet operator live at opposite ends of the
passive filtration. Continuing to simplify only the terminal principal block
cannot reveal an F3 lift. The correct causal object has three stages:

```text
exact low-Z packet syndrome
  -> low-Z source correction with the required boundary condition
  -> its complete increasing-Z contact tail
  -> terminal reduction by deep Hermite slide / mixed pivot-capacity cover.
```

Equivalently, the missing map is not a direct projection of F3 onto A/B/C. It
is the full lower-triangular Schur/back-substitution operator from the packet
row through passive grades `0,...,2703`. Any proposed `Rlt13(Fi)` must provide
a replayable witness for that transfer. A list of terminal heads, even when
those heads are exactly reducible, is insufficient.

Decision:

```text
GREEN  exact principal A/B/C slide and its 33 clean rows;
GREEN  exact F3-vs-complete-slide separator;
RED    direct identification of any of 7,282 rows with a packet row;
RED    interpretation of all 7,282 selected shapes as zero coordinates;
GO     causal low-passive packet precycle followed by terminal-tail reduction.
```

## 6. Reproduction

```text
prlimit --as=1073741824 --cpu=120 -- \
  python3 -B \
  .experiments/full187_packet_vs_deep_slide_filtration_separator_6900.py
```

Final replay used about 161 MiB peak RSS and 7.4 seconds. Stable hashes:

```text
canonical 4dc045eeed5d8b936ec43f37001976928f44f9f5d5f62a85536a0f0c129b64e1
script    ed699298c9cc5ae5b448d70d54c72a7f23faf1f2a928b1b4a1ad84bd7b77da91
```

