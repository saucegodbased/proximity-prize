### 2026-09-15 update: cutoff-two arithmetic green; one-exception helper and joint-syndrome routes stopped

Accepted floor remains **6811** (`cdb451f`, submission `5240012`). There is
still no 6900 candidate or submission. The public research branch is now
current through `abf018c`:

https://github.com/saucegodbased/proximity-prize/tree/codex/6900-live-research

#### Exact cutoff-two branch

Commits through `6df2a16` give a same-witness split at `W=133225`. For the
fixed identity-node set `Z`, either

* `|Z|<=262142`, and at least `263611557201523206` retained seeds keep their
  full original 180413-node supports inside `Z`; or
* `|Z|>=262143`.

The small-`Z` source profile is now arithmetically viable with exact values

```text
primary (k,m,M,D,T) = (61,546,739,244,122)
helper  (k,m,M,D,T) = (1312,11810,15993,5248,2624)
primary target rank <= 1,477,453,392
helper target rank  <= 314,478,446,061,020
```

The target-rank Lean module builds in about seven seconds with peak allocator
usage below 0.8 GiB and prints only `propext`, `Classical.choice`, and
`Quot.sound`. Columns, bands, sources, and final list composition are still
being assembled, so this is not yet an endpoint theorem.

#### Exhaustive one-exception helper STOP

Commits `76b5345` and `abf018c` exhaust the current finite-prefix weighted
source family at `N=262143`, including all 23,609,180 admissible `(k,m)`
profiles and the clipped `m<8k` chamber.

For the old `J=211,D=55` primary split, no helper clears both loss bands. A
joint optimization over every source-positive primary profile then gives a
global STOP for this whole rectangular architecture:

* `D<=54`: no helper survives even the necessary D54 bound;
* `D=55`: ledger feasibility forces `J<=211`, already exhaustively stopped;
* `56<=D<=110`: feasibility forces `J<=203`, and no helper survives the
  necessary J203/D110 filters;
* `D>=111`: cheap plus cleanup terms exceed the retained floor before helper
  exits are charged.

Separate jet-heavy and derivative-heavy helpers do not repair it. There is no
J211 helper at all. Raising to J212 makes specialized helpers exist, but the
J212/D55 cheap term plus the globally least primary cleanup is already over
budget before either exit charge.

This is a STOP for the current weighted finite-prefix source/list rectangle,
not a theorem that W133225 is impossible by every architecture.

#### Near-total identity: exact rank STOP and a new conditional closure

Commit `7982ab7` proves that the most natural joint original/quotient syndrome
minor cannot close the `|Z|>=262143` branch. Exact division makes every
original error row a convolution of quotient-error rows plus one exceptional
geometric row. Hence the proposed 81,732-column row family is carried by only

```text
49,341 + 8,328 + 1 = 57,670
```

directions, a deficit of 24,062. The determinant is identically singular;
near-total identity supplies a rational kernel rather than transversality.

The same commit isolates a sharper positive gate. Choose exact 180413-node
badness-preserving supports; their split locators are automatically
seed-injective. If their node-membership predicates admit polynomials in the
seed of degree at most

```text
1,005,598,286,444,
```

then root-incidence counting gives

```text
|Good| <= 262144*d = 263611557201575936,
```

which is 209,414 below the retained lower bound. Thus a low-degree canonical
selection of the **actual split locator** would close this hard endpoint.
The missing producer is exactly that canonical selection: the recurrence
kernel has nullity at least 24,063, so existing RREF/cofactor vectors need not
specialize to the actual split locator. Arbitrary interpolation of the support
map costs about `|Good|-1`, roughly 262,144 times too much.

#### Current scheduling

1. Finish and compose the cutoff-two Lean stack for the `|Z|<=262142` branch.
2. Audit an L-shaped terminal count that isolates the single
   `(J=212,D=55)` corner instead of paying the full J212/D55 rectangle.
3. Attack the hard branch only through a canonical actual-locator producer or
   another invariant that breaks the proved one-spike gauge; the joint-minor,
   fixed-cap helper, and plain two-helper searches are retired.

All committed Lean receipts avoid `decide`, `native_decide`, `sorry`, and new
axioms. No submission is warranted until the hard structural branch and the
remaining scalar-degree window are both closed.
