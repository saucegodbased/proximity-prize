# Full187 target transition interface and structured-corner reduction

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production,
submission, `score.txt`, and `radius.txt` are unchanged; the accepted result
remains 6806.

## Verdict

The corrected 187-shape transition census is useful, but it is **not** a
THREE-RHS containment proof. The terminal `q=0` contact layer has 1,266,925
surviving `(r,s;f,aE,cS)` occurrences. Of these, 1,194,075 (94.2499%) have
enough coefficient width for an arbitrary agreement-side Hermite residue.
That percentage must not be described as error correction: the stronger
one-coefficient CRT that also prescribes an arbitrary value at every error
node is green for 1,186,372 occurrences (93.6418%), with 7,703 occurrences
agreement-only and 72,850 still structured even on the agreement set.

The existing sharp local order-two basis gives a substantial exact reduction
inside those 72,850 structured occurrences. It supplies a legal leading pivot
for 57,512 occurrences, collapsing to 16,328 distinct contact/seed rows. It
leaves 15,338 occurrences, collapsing to 7,726 distinct rows, in one explicit
low-`T` corner. This is a narrowly scoped GREEN license for the next sparse
transpose/confluence gate, not a lift: global interpolation tails and the four
target packets have not been propagated.

## 1. Literal edge rule and mandatory truncation guard

For a source tag

```text
X^a Y^y R^r S^s Z^z
```

choose `f<=y`, passive shift `h<=y-f`, `aE+cS<=f`, and coefficient-Hasse
order `q>=0`. Its contact row is

```text
(T,E,R,S,Z)
  = (q+f-aE+cS, aE, f-aE-cS+r, s+cS, z+h),
```

and the edge exists only when

```text
q+f+2*aE+cS < 60.                              (SURVIVE)
```

The physical source intervals are

```text
0 <= a < 60g-wy-(w-1)r-(w-2)s,
0 <= z <= 2703-y-r-s,
```

at `(n,w,g)=(262144,131071,180413)`. The script asserts `(SURVIVE)` on every
constructed edge. In particular, the formerly claimed edge
`Y^82 -> Y^81 Z` has contact weight 81 and is absent. The surviving top-pure
endpoint is `(f,h,aE,cS,q)=(59,23,0,0,0)` and has predecessor width
3,091,591, exceeding `n` by 2,829,447.

The census counts only `q=0` choices. This is the worst coefficient-Hasse
layer for the displayed scalar Hermite capacity because positive `q` raises
contact weight and lowers the required locator depth. It is not a count of
all literal positive-`q` rows, and all future graph edges must still check
`(SURVIVE)` rather than inherit a `q=0` edge blindly.

## 2. What the two Hermite thresholds mean

Put

```text
depth  = 60-(f+2*aE+cS),
width  = 60g-wf-(w-1)r-(w-2)s,
margin = width-g*depth
       = (g-w)f+g(2*aE+cS)-(w-1)r-(w-2)s.
```

Then `margin>=0` means that an arbitrary residue modulo
`Lambda_G^depth`, of degree below `g*depth`, fits in this coefficient strip.
This is exactly an agreement-prefix correction into `ker C_G`.

It does **not** say that arbitrary error-node data can be prescribed while
the agreement jet is held fixed. The corresponding scalar affine CRT needs

```text
width >= g*depth + e,        e=n-g=81731,
```

which is `margin>=81731`. The exact three-way split is

| scalar capacity | occurrences | fraction |
|---|---:|---:|
| agreement jet plus arbitrary error values | 1,186,372 | 93.6418% |
| arbitrary agreement residue only | 7,703 | 0.6080% |
| structured even on agreements | 72,850 | 5.7501% |

Even the strongest row in this table is only a scalar CRT fact. It does not
prove simultaneous packet boundaries, membership in `W=ker(J|ker C_G)`, or
containment of the three prescribed error RHS in `C_E(W)`.

## 3. Exact reduction of the 72,850 structured occurrences

The structured inequality depends on `(aE,cS)` numerically only through
`k=2*aE+cS`:

```text
49342*f + 180413*k < 131070*r + 131069*s.       (STRUCT)
```

Thus 1,056 distinct `(f,aE,cS)` types reduce to 406 capacity types `(f,k)`.
Necessarily `aE<=6`, `k<=13`, and the exact maximum `f` at each `k` is

```text
k:     0  1  2  3  4  5  6  7  8  9 10 11 12 13
max f:55 52 48 44 41 37 33 30 26 22 19 15 11  8.
```

For one structured origin define its `q=0` contact row

```text
T=f-aE+cS,  E=aE,  R=f-aE-cS+r,  S=s+cS,
d=E+R+S,    rho=max(E+S-10,0).
```

The sharp basis already formalized in `Order2SourceBasisScaffold.lean` and
`Order2FullLayerLeading6900.lean` has a pivot for this row precisely when

```text
max(0,d-21) <= a0 <= min(R,T-2*rho).            (PIVOT)
```

Taking the left endpoint gives exact basis indices

```text
qSource=d-a0, b=R-a0, eBasis=E,
kT=T-a0-2*rho, passiveSeed=h=82-r-s-f.
```

The executable checks on every such edge

```text
qSource<=21, eBasis<=min(E+S,10), d<=82, d+h=82,
kT+a0+2*rho+3*eBasis = T+3E = f+2*aE+cS < 60.
```

It also applies the exact source multiplier refund

```text
bonus=b+2*(min(E+S,10)-E),
multiplierWidth=60g-w*d+bonus.
```

Multiplying a maximally wide terminal coefficient by an arbitrary
degree-`<n` node interpolant fits every pivotable strip; the minimum strict
degree slack is 524,283.

The counts by the older raw-inverse labels are

| origin class | local pivot GREEN | unpivoted corner |
|---|---:|---:|
| raw diagonal | 22,110 | 0 |
| `E>0` | 28,599 | 13,413 |
| `2*cS>r` | 3,873 | 1,120 |
| `s+cS>10` after the preceding guards | 2,930 | 805 |
| total | 57,512 | 15,338 |

In the structured chamber `R` never causes `(PIVOT)` to fail. Every one of
the remaining 7,726 distinct contact/seed rows is characterized by the sole
cut

```text
T < max(0,E+R+S-21) + 2*max(E+S-10,0).          (CORNER)
```

The positive deficit (right side minus `T`) ranges only from 1 through 19.
This is the smallest honest combinatorial frontier found here.

## 4. What remains, and the cheapest decisive gate

The local basis theorem says its pivot is unique at the least contact weight;
all its other terms have strictly greater contact weight. A plausible global
proof therefore processes contact weight upward, using the checked X slack
to interpolate the leading coefficient and sending coefficient-Hasse and
basis remainders forward. The load-bearing missing statement is that this
orientation remains triangular after all nodes are combined, passive-seed
indices are retained, and the structured locator packets (including their
scalar/`Z` tails) are kept atomic.

The cheapest target-specific test is now smaller than a 187-shape ambient
rank computation:

1. quotient the symbolic transpose recurrence by the 57,512 licensed local
   pivots in increasing contact weight;
2. retain only the 7,726 `(CORNER)` rows and the higher-weight tails that land
   in them;
3. seed it with the exact three centered locator-normal packets and the `Z1`
   impulse;
4. check whether their four reduced residues vanish in the required Schur
   pattern.

A nonzero closed corner residue is an immediate target-specific STOP. Zero
support is only a reachability GREEN; coefficient propagation and the
boundary/error Schur statement still must be proved. The old `q=0`
`r+2s` components cannot serve as a cut because positive Hasse order changes
that charge and `E`-basis packets couple additional rows.

## 5. Reproduction and hashes

```text
prlimit --as=1073741824 --cpu=60 -- \
  python3 -B .experiments/full187_target_transition_dependency_interface_6900.py

canonical JSON SHA256
  e5eaf11f8a22e95d6852ff432cd2219d75153551f4f2f1a1ae90b2ccdb0f8ab9

script SHA256
  c6ab4fad2e641de18532ff1e4720ab0123c0296ddb64fc95951432f5d99323ea
```

Runtime was about 2.1 seconds under a 1 GiB address-space cap. No tiny
69-position control, finite-field rank inference, production module, or
submission artifact is used.
