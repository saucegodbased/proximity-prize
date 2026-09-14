# Full187 charge-13 Hasse transpose, exact principal quotient, and Schur STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production, the
accepted 6806 proof, score, radius, and submission roots are unchanged.

## Verdict

There is now an exact, executable symbolic specification of the eleven
physical charge-13 streams at the target parameters. It includes every raw
contact row, the 47 positive-Hasse collisions hidden in the 33 advertised
principal rows, the strict tapered coefficient windows, and the complete
transpose equations.

The 33 principal polynomial outputs have a particularly small exact quotient:

```text
0 -> S13 --(T_A,T_B,T_C)--> S13^3 --(I_B,I_C)--> S13^2 -> 0.       (Q13)
```

Thus their cokernel is **two copies of the tapered module**, of dimension
`1,693,648`, before node evaluation and before any other contact tails. This
is a quotient statement, not a kernel construction. The isolated eleven-stream
block is raw-injective in the fixed `Xi_E^2` target instance (`bd2f679`). Any
useful final-grade class must cancel its A heads against other origins or
earlier grades while carrying its correlated B/C tails.

The target four-packet Schur operator is still undefined. The repository has
abstract mapping-cone types and local eliminator existence results, but no
concrete, provenance-preserving lower-prefix correction map. In particular,
the 33 principal rows are not a subcomplex: the same eleven streams produce
`10,011,293` distinct raw contact row shapes per node. Dropping those tails
would certify a different map.

Artifact:

```text
.experiments/full187_charge13_transpose_interface_spec_6900.py
```

It is a streamed exact-integer/finite-field audit, not a small-m grid and not a
dense target matrix.

## 1. The smallest physical coefficient module

At `(m,J,q,t,L)=(60,82,21,10,2703)`, charge 13 at the final passive grade has
the eleven physical origins

```text
c_s(X) Y^61 R^(21-s) S^s Z^2621,             0 <= s <= 10,
deg c_s < 76979+s.
```

Put

```text
S13 = direct_sum_(s=0)^10 K[X]_<76979+s.
```

Its dimension is

```text
dim S13 = sum_(s=0)^10 (76979+s) = 846824.
```

The common rectangle has dimension `11*76979=846769`; the ragged fringe has
dimension `1+...+10=55`. There are eleven physical streams, not 33 independently
selectable source polynomials.

The full target row module must distinguish the keys

```text
(node, T, E, R, S, Z).
```

For a source stream `t`, coefficient-Hasse order `q`, and choices
`0<=f<=61`, `0<=h<=61-f`, `aE+cS<=f`, the raw contact row is

```text
T = q+f-aE+cS,
E = aE,
R = 21-t+f-aE-cS,
S = t+cS,
Z = 2621+h,
```

and it survives precisely when

```text
q+f+2*aE+cS < 60.
```

For a basis coefficient `X^a`, its scalar at a node `x` is

```text
binom(61,f) binom(61-f,h)
* multinomial(f; aE,cS,f-aE-cS)
* (-1/2)^cS * u0(x)^(61-f-h) * u1(x)^h
* binom(a,q) * x^(a-q),
```

where `binom(a,q)=0` for `q>a`. This formula is the executable sparse operator
specification: it generates a requested column or transpose moment without
materializing the multi-trillion-coordinate target matrix.

Exact streamed census:

```text
fully expanded provenance contributions                 48,516,523
  lower-grade contributions                             47,315,598
  top contributions                                      1,200,925
distinct top row shapes per node                           241,475
distinct all-grade row shapes per node                  10,011,293
top row coordinates over all 262144 nodes           63,301,222,400
all-grade coordinates over all nodes             2,624,400,392,192
```

These are sparse row-key counts, not rank claims.

## 2. The three principal families and their hidden collisions

The advertised top, charge-13 choices are

```text
A: (f,aE,cS,h)=(7,6,1,54),
B: (f,aE,cS,h)=(8,5,3,53),
C: (f,aE,cS,h)=(8,6,1,53).
```

Their q=0 scalars modulo `p=2130706433` are

```text
kappa_A = 603758703,
kappa_B = 693269975,
kappa_C = 642373467,
kappa_C = 54*kappa_A,       4*kappa_B = kappa_C.
```

Positive coefficient-Hasse terms land on exactly the same physical row keys.
After dividing out the displayed nonzero scalars, the polynomial bands are

```text
(T_A c)_s = c_s - 2 H_1(c_(s+1)),

(T_B c)_s = c_s - 6 H_1(c_(s+1))
                  + 12 H_2(c_(s+2)) - 8 H_3(c_(s+3)),

(T_C c)_s = c_s - H_1(c_(s+1)),
```

with missing streams above ten equal to zero. At node `x`, these are further
multiplied by `kappa_A*u1(x)^54`, `kappa_B*u1(x)^53`, and
`kappa_C*u1(x)^53` respectively.

All 33 q=0 heads are present, but the same 33 row keys receive 47 additional
positive-Hasse contributions, for 80 provenance terms total. Their row-key
multiplicity histogram is

```text
1 term: 3 rows;  2 terms: 21 rows;  3 terms: 1 row;  4 terms: 8 rows.
```

The taper is exact rather than asymptotic:

```text
width(s+j)-j = (76979+s+j)-j = 76979+s.
```

Hence each `H_j` above maps the full source window into the exact output
window and every band is square upper-unitriangular on `S13`.

### Hasse derivatives are not composition powers

Here `H_j` is the j-th Hasse derivative,

```text
H_j(X^a)=binom(a,j) X^(a-j),
```

and composition obeys

```text
H_j o H_k = binom(j+k,j) H_(j+k).
```

Therefore B's band `(1,-6,12,-8)` is a Hasse-binomial translation band. It
must not be written as the ordinary operator composition `(1-2 H_1)^3`:
already `H_1 o H_1=2 H_2`.

## 3. Actual inverse and the basis-independent quotient interface

Normalize principal polynomial outputs by

```text
a=A/kappa_A,    b=B/kappa_B,    c=C/kappa_C,
```

before applying node weights. The A band has the recursive inverse

```text
c_10 = a_10,
c_s  = a_s + 2 H_1(c_(s+1)),                 s=9,...,0.       (AINV)
```

Equivalently,

```text
(T_A^-1 a)_s = sum_(j=0)^(10-s) 2^j j! H_j(a_(s+j)).
```

The script symbolically composes the Hasse bands in both orders and obtains
exactly `(1,0,...,0)`. Define

```text
I_B(a,b,c) = b - T_B T_A^-1(a),
I_C(a,b,c) = c - T_C T_A^-1(a).                         (COMPAT)
```

These are basis-independent linear maps on the tapered polynomial module.
The executable also derives their two convolution bands:

```text
T_B T_A^-1: (1,-4,-4,-32,-256,-2560,-30720,
             -430080,-6881280,-123863040,-2477260800),

T_C T_A^-1: (1,1,4,24,192,1920,23040,
             322560,5160960,92897280,1857945600).
```

Now `(I_B,I_C)(T_Ax,T_Bx,T_Cx)=0`. Conversely, if both compatibilities vanish,
take `x=T_A^-1(a)` to recover the triple. The compatibility map is onto since
`(0,b,c)` maps to `(b,c)`. This proves `(Q13)`, so

```text
S13^3 / image(T_A,T_B,T_C) ~= S13^2,
dim cokernel = 2*846824 = 1693648.                       (COK)
```

The statement is before node evaluation. Dividing by `u1(x)` is unnecessary
and is not valid uniformly for an arbitrary agreement interpolant of degree
less than `g`; it may vanish at a node. In the one frozen `Xi_E^2` instance,
`u1` is nonzero on G, which is enough for the independent raw-injectivity
receipt, but it is not a universal theorem.

## 4. Exact adjoint equations

For dual tapered streams `(alpha,beta,gamma)`, the pre-node principal
annihilator equation is

```text
T_A^*(alpha) + T_B^*(beta) + T_C^*(gamma) = 0.           (ADJ)
```

Since A is invertible, this is equivalently

```text
alpha = -(T_A^-1)^*(T_B^*(beta)+T_C^*(gamma)).           (ADJ-SOLVE)
```

Thus the formal principal annihilator is parametrized by two copies of the
tapered dual, matching `(COK)`. In coefficient coordinates, `H_j^*` sends an
output functional at coefficient `a-j` to source coefficient `a` with factor
`binom(a,j)`.

With node duals `lambda[F,s,x]`, the literal equation for every physical
source `t=0,...,10` and every `a<76979+t` is

```text
sum_(F in {A,B,C}) sum_(j in band(F), j<=t)
  kappa_F*d_(F,j)*binom(a,j)
  * sum_(x in Domain) u1(x)^h_F x^(a-j) lambda[F,t-j,x] = 0,   (NODE-ADJ)
```

where `h_A=54`, `h_B=h_C=53`, and

```text
d_A=(1,-2),  d_B=(1,-6,12,-8),  d_C=(1,-1).
```

Equation `(NODE-ADJ)` is only the principal projection. The complete raw
transpose equation is the sum over all `(f,h,aE,cS,q)` displayed in section 1.

## 5. Four packet residues and the exact augmented dual gate

Let `V0` be the complete prior source, `C0:V0->W` its raw contact map, and
`beta0:V0->K^4` its four-boundary map. Let `C13:S13->W` and
`beta13:S13->K^4` be the complete maps of these eleven streams, including all
nonprincipal rows. Finally let

```text
Packet : K^4 -> W x K^4
```

send basis vector `e_i` to the literal contact/boundary column of the current
named packet `F_i`. The fourth packet is

```text
B  = Xi_H^59 Xi_(G\H)^60,
F3 = B*(Y-P-(Z-gamma)q_H),
```

not pure constant Z. `HrsP4RHSAgreementContact6900` proves this F3 is source
legal and has full order-60 agreement contact zero; it does not give its
lower-prefix correction or error-side Schur image.

The exact requested containment is

```text
range(Packet) <= range [ C0 C13 ; beta0 beta13 ].         (PACKET)
```

Equivalently, every pair of duals `(lambda,mu)` satisfying

```text
C0^* lambda + beta0^* mu = 0,
C13^*lambda + beta13^*mu = 0                              (FULL-ADJ)
```

must also satisfy `Packet^*(lambda,mu)=0`. A nonzero packet pairing is an
exact RED certificate. If the packet target is specialized to `(0,e_i)`, this
becomes the familiar statement that `beta` is onto on `ker C`, and
`(FULL-ADJ)` must force `mu=0`.

## 6. Exactly which tails may not be discarded

The following data are load-bearing in any reduced charge-13 Schur operator:

1. The 47 positive-Hasse collisions already folded into the 33 principal row
   keys. Treating the heads as diagonal changes the operator.
2. The other `1,200,845` top-grade provenance terms outside those 80 head
   contributions.
3. All `47,315,598` lower-grade provenance terms of the eleven streams,
   including their `u0` powers and passive-Z row labels.
4. Every agreement and error node copy and its actual `u0/u1` value. A uniform
   theorem cannot localize by inverting `u1`.
5. The complete prior-prefix maps `C0` and `beta0`, not only their dimensions.
6. For each sharp Order2 pivot, its higher-contact remainder. The existing
   leading-term theorem proves uniqueness below the pivot weight but does not
   prove global closure or orient the remainder into already eliminated keys.
7. For each mixed agreement-Hermite/error-value CRT elimination, the chosen
   correction polynomial and its induced contact and boundary tails. The CRT
   capacity theorem proves existence of an interpolant, not a simultaneous
   linear section compatible with all source streams.
8. The exact contact and boundary columns of `F0,F1,F2,F3` in the same row-key
   convention.

The newer all-origin audit strengthens item 1: all 72,850 structured q=0
origins have tapered positive-Hasse same-row families. Charge13 is not an
exceptional diagonal block. Any cross-origin cancellation used to kill its A
heads must carry the corresponding B/C and lower-contact tails.

## 7. Why the present repository stops before a reduced Schur matrix

The available pieces do not instantiate the abstract mapping cone:

* `GlobalO2RawGradedMappingConeGate6900.lean` proves exact linear algebra for
  abstract maps named `C0`, `lower`, `top`, `beta0`, `betaT`, and `correction`.
  It supplies none of those target maps.
* `Full187StrongCapacityCRT6900.lean` proves that one set of prescribed local
  residues and error values has a polynomial interpolant inside a checked
  width. It does not choose a global linear correction section and does not
  replay the section's other contact/boundary outputs.
* `Order2FullLayerLeading6900.lean` proves a unique lowest-weight pivot and a
  higher-weight remainder. It does not enumerate, orient, or terminate all
  remainders in the finite target source.
* `bd2f679` proves the isolated charge13 source is raw-injective in the frozen
  target instance. Therefore the 11 streams alone cannot produce a kernel;
  cross-origin/multi-grade cancellation is mandatory, not optional cleanup.

Consequently there is no honest finite `R_<13` or correction operator to put
between `(Q13)` and `(PACKET)`. A principal-only solve can test the operator
implementation but cannot prove a Full187 packet lift. This is a decisive
definition/data STOP, not an inference that the desired theorem is false.

## 8. Reproduction and decision rule

Run under a small cap:

```text
prlimit --as=2147483648 --cpu=120 -- \
  python3 -B .experiments/full187_charge13_transpose_interface_spec_6900.py
```

The script asserts every target constant and count, both A-inverse
compositions, all strict taper identities, all 80 principal-row provenance
patterns, and the quotient dimensions. It emits hashes for the canonical
operator and transpose term list.

Recorded run:

```text
exit 0; elapsed 3.829 s; peak RSS 93,396 KiB
canonical sha256 2a151e742e50015bd7156435841409ebb49f74a85872b47a6b767f13a88ea6d0
script sha256    8708a3062295f332d61f7c8145d75e788d7b55e9e7bff6462e02357b8c38e09b
```

`.experiments/Charge13GraphQuotient6900.lean` independently proves over an
arbitrary ring module that an invertible first coordinate makes the graph map
injective, the two-residue compatibility map surjective, and its kernel equal
to the graph range. It builds with `lake env lean`, uses no `sorry`,
`native_decide`, or nonstandard axiom, and is the theorem-level exactness
behind `(Q13)`.

Decision:

```text
GREEN  exact raw 11-stream sparse operator and principal S13^2 quotient;
GREEN  exact principal and full-raw transpose equations;
GO     implement a provenance-preserving C0/lower correction reducer;
STOP   principal-only four-packet promotion or pure-Z1 substitution;
STOP   discarding positive-Hasse, lower-grade, pivot, CRT, or boundary tails.
```
