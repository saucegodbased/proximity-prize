# Full187 complete projection versus terminal carriers: endpoint STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission roots, score, radius, and the accepted 6806 proof are unchanged.

## Verdict

The complete-depth projection in commit `2d678e8` does **not** supply the
missing low-passive bridge, and it does not rescue the obsolete three-carrier
trellis theorem.

There are three exact conclusions.

1. The literal target packet

   ```text
   F3 = B (Y-P-(Z-gamma)q_H),
   ```

   with frozen `P=gamma=0`, is still separated from the whole complete-depth
   endpoint operator by its normalized scalar coordinate at the first error.
   This extends the separator in `08d0efe` from the older three-layer slide to
   all 11,220 correction blocks in `2d678e8`.

2. In the authoritative arbitrary-direction F101 chamber, adjoining the
   exact complete-depth endpoint analogue to the **whole legal three-carrier
   trellis** leaves all three individual defects equal to one and the joint
   defect equal to one. This remains true after a stronger augmentation by
   every legal endpoint fringe coefficient and every terminal-origin
   coefficient independently. An exact covector annihilates all 1,658
   augmented columns and evaluates on `(F0,F1,F2)` as `(19,7,66)`.

3. At the Full187 last carrier shift, the terminal carrier and the Pascal
   correction are not disjoint controls. Of the 120 raw `(f,r,s)` blocks in
   the three-carrier envelope, 119 are among the 11,220 projection blocks;
   only `(60,0,0)` is outside. The eight-carrier union has the same one-block
   exception, and seven of its eight carriers are supported wholly inside the
   projection block set. Thus endpoint closure is a coupled affine solve on
   reused physical coordinates, not a superposition of two independent
   constructions.

4. The new `b535ccc` first-fringe result makes one endpoint overlap cell
   genuinely GREEN, but it is not an earlier packet lift. Its certified
   `(r,s)=(11,10)`, `f=58/59` pair remains disjoint from every packet row
   even after the largest legal downward passive shift.

This is a STOP for the exact architecture

```text
three-carrier causal trellis + independently appended complete-depth absorber.
```

It is not a no-go theorem for an order-four/full-module precycle followed by a
joint endpoint solve, and it is not a dual for the whole Full187 source.

## 1. Literal F3 separator against all complete-depth endpoint blocks

The four exact packet heads retained throughout this audit are

```text
F0 = Lambda_G^59 Y,
F1 = Lambda_G^58 (Lambda_G R-Lambda_G'Y),
F2 = Lambda_G^57 (Lambda_G^2 S-2 Lambda_G Lambda_G'R
                   +(2 Lambda_G'^2-Lambda_G Lambda_G'')Y),
F3 = B(Y-P-(Z-gamma)q_H).
```

For the frozen target instance,

```text
p = 2130706433, N = 262144, g = 180413,
F3 = B(Y-Zq_H).
```

At the first error node, projection to the contact scalar coordinate

```text
(node,T,E,R,S,Z) = (180413,0,0,0,0,0)
```

has unnormalized F3 value

```text
1307960934.
```

Multiplication by its inverse

```text
1664439266 mod p
```

makes the pairing equal to one. Take the four boundary weights to be zero.
The full F3 error-syndrome hash is

```text
44284a2ae31b90315699b3f0a14947ea2007114bbd7460485287f2543d5de332.
```

Every terminal origin used by `2d678e8` has outer passive exponent

```text
L-J = 2703-82 = 2621.
```

Its correction blocks are

```text
P_f(X) Y^f R^r S^s Z^(L-f-r-s),
0 <= f < 60, r+s <= 21, s <= 10,
```

and hence have minimum outer exponent

```text
2703-59-21 = 2623.
```

Local contact substitution never lowers an already present outer `Z`
exponent. Therefore the normalized scalar covector annihilates every contact
tail of every terminal origin and every one of the 11,220 complete-depth
correction blocks, while pairing the literal F3 to one.

As in `08d0efe`, low-passive source columns can hit this coordinate. The
statement is exactly that the endpoint operator is not itself the precycle.

## 2. Exact F101 complete-endpoint augmentation

Use the later STOP's arbitrary-direction chamber

```text
F101,
(n,w,g,m,D,s,t,J,L)=(10,4,7,4,28,1,1,6,10),
error-direction offsets=(3,5,7).
```

The old exact base plus the whole legal three-carrier coefficient space in
all four shifts consists of 1,399 columns and has

```text
individual defects = (1,1,1), joint defect = 1.
```

For each legal `(r,s)` and `0<=f<4`, form the exact analogue of the
complete-depth correction block. Put

```text
width(r,s,f) = 28-4f-3r-2s,
qmax(r,s,f)  = min(floor(width/10)-1, 3-f).
```

The twelve canonical all-node prefixes contribute 190 literal monomial
columns. Adjoining all of them leaves the defects unchanged. More strongly,
adjoin:

```text
all complete-prefix correction columns       190
all legal correction-strip columns            244
all legal terminal-origin columns               15
```

with the origin and correction coefficients independent. The latter is a
strict superspace of the graph of any prescribed Pascal recurrence, including
all unprescribed higher-jet fringes. The defects are still

```text
(1,1,1), joint 1.
```

The deterministic upper-echelon/back-substitution covector has the exact
receipt

```text
augmented columns annihilated       1658
augmented source rank               1652
functional support                  1640
contact / boundary support       1628 / 12
values on F0,F1,F2              (19,7,66)
functional support sha256
55274f5911fe171a23c775c6c92b7228a6f595cf9159ba7defab4ab8281a6ce7
```

It uses contact rows at every node and passive seeds `0,...,10`, plus twelve
boundary coordinates. A deliberately attempted separator supported only
below the correction minimum seed six does **not** exist: on that truncation
all three projected defects are zero. Thus the surviving obstruction is a
genuine cross-seed compatibility relation, not a merely early-row support
gap.

This finite chamber falsifies a universal theorem claiming that the old
three-carrier precycle becomes complete after quotienting by the new endpoint
projection. It does not by itself falsify a target-specific order-four
construction.

## 3. Full187 last-layer physical overlap

At `m=60`, the raw three-carrier recurrence has the block envelope

```text
r=1,s=0, f=0,...,58;
r=0,s=0, f=0,...,60.
```

There are 120 distinct blocks. The complete-depth projection contains all
`f<60` blocks for every legal `(r,s)`, so its intersection with this envelope
has size 119. The unique outside block is

```text
(f,r,s)=(60,0,0).
```

For the eight order-four carriers

```text
(a,c)=(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),
```

the raw-support union again has 120 blocks and the same unique exception.
Every carrier except `(a,c)=(0,0)` lies entirely in the projection block set.
Across the three-carrier overlap there are 353 prescribed
`(f,r,s,q)` block/Hasse slots with `q<=2`.

This does not assert that every carrier coefficient is fixed or that an
intersection count proves inconsistency. It proves the narrower and
load-bearing fact: the last carrier layer and the complete-depth correction
write into the same physical source coefficients. Their endpoint equations
must be solved together.

## 4. The 54,086 first-fringe unit is not a packet prelift

Commit `b535ccc` proves that the tightest first residual pair

```text
(r,s,f)=(11,10,58), (11,10,59)
```

has coefficient windows `(470202,339131)`. After preserving the prescribed
order-zero jets, the remaining equation is `A+59*u1*B`; its high quotient is
a `54086 x 76987` Toeplitz map with a certified nonsingular `54086` Hankel
minor. This resolves that one shared endpoint equation and is positive
evidence for a coefficient-polynomial confluence cascade.

It does not supply the missing causal start. At the endpoint the two outer
passive exponents are `(2624,2623)`. Their largest common legal downshift is
2623, producing the legal Full187 sources

```text
Y^58 R^11 S^10 Z,       Y^59 R^11 S^10,
```

both of total grade 80. The certified common `f=58` channel is then at
passive seed one: the first source retains its outer `Z`, while the second
selects one `u1*Z` and 58 contact factors.

Every complete contact row of either source retains the outer
`R^11 S^10`, hence has `R+S>=21`; every exact packet row has `R+S<=1`.
Their raw packet-row intersection is zero. At the frozen zero graph their
total non-X degree is 80, so every first boundary partial also vanishes. In
particular the pair is annihilated by the literal F3 scalar coordinate at
`R=S=Z=0`.

Therefore the certified minor is an X-window unit inside a fixed
passive/derivative channel. It may help the **joint terminal tail solve**, but
it cannot initiate `F0..F3` before the carrier. A low-derivative analogue
would be a new full-vector calculation; the `54086` certificate does not
transport to it merely by deleting `R^11S^10`.

## 5. Minimal remaining bridge theorem

The old three-carrier route is closed. A viable bridge must now establish all
of the following in one typed or exact bordered calculation.

1. Use an arbitrary-direction complete state, at least the order-four
   eight-carrier/full-module state. The later overlap STOP already rules out
   repeating the selected `24 x 24` block as if adjacent shifts were
   disjoint; full-vector RHS membership and all unselected leakage are
   required.

2. Include the literal fourth packet. Existing eight-carrier receipts are
   three-RHS receipts for `F0,F1,F2`; they do not silently cover
   `F3=B(Y-P-(Z-gamma)q_H)`.

3. At the final shift, prove bordered membership of the complete carrier tail
   in the sum of the complete-depth projection graph and a simultaneous
   physical section for the 2,622,661 residual strong-capacity provenance
   terms. The coefficients on the 119 shared raw blocks must be one joint
   assignment.

   The `b535ccc` unit settles only the tight `f=58/59`, `q=1` cell of this
   compatibility problem. The multi-`f`, multi-`q` confluence cascade and all
   `u0` tails remain.

Equivalently, the next useful object is the full aggregate-row bordered map
for

```text
exact F0..F3 head -> complete causal carrier band -> joint endpoint quotient,
```

not another selected-row or principal-support scan.

## Reproduction and artifacts

```bash
prlimit --as=4294967296 --rss=4294967296 --cpu=420 -- \
  python3 -B \
  .experiments/full187_complete_projection_carrier_endpoint_gate_6900.py
```

Recorded stable hashes:

```text
canonical sha256 811439d7a0433dcf68ac83329f5c44d57a9bebf9f7367bfea119c91121e4fa05
script sha256    1d0a4f879a3a0ccb3c7498511d91e0121df02cd1310f6c9ca8b4799de53e958b
```

New files:

```text
.experiments/full187_complete_projection_carrier_endpoint_gate_6900.py
.experiments/FULL187_COMPLETE_PROJECTION_CARRIER_ENDPOINT_STOP_6900.md
```
