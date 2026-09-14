# Universal weighted scalar-list endpoint at W = 133221

Status: **FORMAL GREEN at W = 133221; faithful RED at W = 133222 for the
current counting architecture.**  This is a universal received-direction
endpoint improvement, not by itself a proof of the 6900 claim.

## Exact result

The 33 `*W1332216900.lean` modules are a mechanical retarget of the existing
weighted-list proof stack.  They prove, over every field of characteristic
`2130706433`, that a family of degree-at-most-133221 polynomials agreeing with
one received word at at least 180413 of 262144 injective evaluation nodes has
cardinality at most

```
250960796897672558.
```

This is below the DataEleven retained threshold
`253511670984674103` by exactly `2550874087001545`, and below the MCA
threshold `254684620614660120` by exactly `3723823716987562`.

The public conclusions are:

* `WeightedScalarListW1332216900.scalar_finite_list_card_le`;
* `WeightedScalarListW1332216900.scalarized_seed_family_card_le`;
* `WeightedScalarListW1332216900.scalarized_large_family_degree_obstruction`;
* `LowReceivedDirectionScalarSplit1332216900.scalar_count_or_received_direction_degree_ge`;
* `HighReceivedDirectionQuotientDegree1332216900.quotient_degree_ge_2150`;
* `DataElevenWeightedScalarW133221Endpoint6900.retained_same_witness_excess_ge_2151`.

Thus the universal projective scalar split forces

```
deg(receivedDirectionInterpolant) >= 133222
```

on the large-family branch.  After subtracting a degree-at-most-131071 code
anchor and dividing by a degree-131072 locator, the quotient has degree at
least 2150.  In the DataEleven same-witness notation the generic bridge gives

```
max(deg c, deg d) + deg Q + 2151 <= deg E0.
```

The bridge theorem states all hypotheses explicitly; it does not silently
identify its family with a DataEleven field.

## Exact optimizer receipt

The optimizer source is
`.experiments/weighted_scalar_w133219_full_optimizer_6900.cpp`, SHA-256
`3d9b2a147abdb1263f44ddce7d1d6a04be345a78d511cb0661ee4b0f15f7a8fe`.
The rebuilt executable used for the receipt had SHA-256
`f80ec4aea9b3a60a8a8de3e1466e4b7602f43f0ab6f5b999ed22bae3b8e3ef65`.

For W = 133221, exact slow mode returned:

```
BEST total=250960796897673279 target=263611557201785350
pk=59 pm=533 hk=1252 hm=11268 J=207 D=54 T=27
v=68740 qmin=2458014 qmax=11997570
cheap=236576105857455036
exits=704751208709671
cleanup=13679939831508572
helper K=113112257218380797
Jband(active exact)=113106722133102670
Dband(active exact)=112648991733881442
```

The optimizer's total includes an advertised `yOnly = 721` charge that the
composed semantic cover does not use.  The formal theorem's direct bound is
therefore `250960796897673279 - 721 = 250960796897672558`.  The optimizer's
printed target is its historical two-source allowance; the DataEleven and MCA
comparisons above are separate exact arithmetic theorems.

The main formal constants are:

```
primary (k,m,B,M,D,T) = (59,533,96160129,721,236,118)
primary pair sum       = 92375427127187459192
primary columns        = 346699946431821 remainder 208310 mod 266442
primary target rank    = 1322554236
primary kernel         = 288789837

helper (k,m,B,M,D,T)   = (1252,11268,2032893684,15259,5008,2504)
helper pair sum         = 18238030713311927937794940
helper columns          = 68450284539644380157 remainder 3546 mod 266442
helper target rank      = 260685624246315
helper kernel           = 113112257218380797

cheap cap               = 236576105857455036
exited-helper cap       = 704751208709671
nonactive cleanup       = 13679939831507851
formal direct cap       = 250960796897672558
```

`J = 207` is an internal jet-degree cutoff for the weighted helper product.
It is not the DataEleven connection-polynomial degree `deg Q` and gives no
implication `deg Q >= 202`.

## Faithful boundary control

Running the same exact optimizer at W = 133222 returned

```
BEST total=258391532555862528
pk=60 pm=538 hk=1306 hm=11754 J=208 D=55 T=27
```

This exceeds the DataEleven retained threshold by
`4879861571188425`.  Hence W = 133222 is RED for this exact proof
architecture.  This is the first adjacent-level control, rather than a toy
finite-field or frozen-U1 test.  Conversely, the W = 133221 theorem quantifies
over the received word and is therefore immune to a hostile monomial choice
of the high received direction.

## Reproduction and audit

Optimizer commands:

```sh
g++ -O3 -std=c++20 -fopenmp \
  .experiments/weighted_scalar_w133219_full_optimizer_6900.cpp \
  -o /tmp/weighted_frontier_fp
OMP_NUM_THREADS=12 /tmp/weighted_frontier_fp fullg 133221 slow
OMP_NUM_THREADS=12 /tmp/weighted_frontier_fp fullg 133222 slow
```

Every dependency was rebuilt in import order with commands of the form:

```sh
env LEAN_PATH=.experiments LEAN_ABORT_ON_PANIC=1 \
  lake env lean -o .experiments/NAME.olean .experiments/NAME.lean
```

The clean build covered all 33 W133221 modules and the three bridge modules,
4128 source lines / about 260 KiB.  The slowest arithmetic module completed
inside its 600-second timeout.  All printed public-axiom sets were subsets of
`[propext, Classical.choice, Quot.sound]`.  There are no `sorry`, `admit`,
`unsafe`, or `native_decide` commands in these sources (one module's prose
mentions `native_decide`).

## Packaging caveat

Directly importing the current DataEleven/V6 chain together with this stack
currently causes a pre-existing environment collision:

```
import Mathlib.RingTheory.Valuation.Integral failed, environment already
contains 'Valuation.Integers.integralClosure' from
ProximityPrize.SubmissionLower.V6
```

For that reason `DataElevenWeightedScalarW133221Endpoint6900.lean` is an
honest generic application theorem rather than a hidden import of the leaf.
`LowReceivedDirectionScalarSplit1332216900.lean` integrates directly against
`TargetLower` and supplies the universal endpoint without importing V6.  A
submission composition must resolve or route around the V6/Mathlib import
collision before importing both stacks in one root.
