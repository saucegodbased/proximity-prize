# K0 passive-value route: formal reduction, exact RED, and relative gate

Date: 2026-09-14 UTC. Scope: lower-6900 exact-`G`, no production change.

## Verdict

The passive-reach ablation is real, but its gain `3 -> 4` does **not** come
from multiplying an already-existing contact-kernel relation by `Z`.

For an old relation `v`, the literal product rule is

```text
C(Zv) = Z C(v),
beta(Zv) = gamma beta(v) + value(v) e_Z.
```

Thus a shifted old-kernel relation can escape the old normal image only if
`value(v) != 0`. The exact L10 audit proves that this value map is zero on
all 317 old kernel relations. Consequently every shifted normal is just
`gamma` times an old normal and the combined rank stays three.

The observed L11 repair is therefore a genuinely **relative connecting-map
relation**. One must construct a newly legal passive-layer vector `d` and an
old vector `p` such that

```text
C(d) = C(p),
lambda(beta(d) - beta(p)) != 0.
```

Then `d-p` is the new complete-kernel normal. This is more than retuning a
cap: the cap exposes the columns, but a new global relative-contact theorem
must prove their contact class is old while their boundary class is not.

## Exact finite falsifier

The script `.experiments/k0_l10_zshift_value_killer_6900.py` uses the frozen
degree-four F101 receipt and checks every canonical L10 kernel relation.
The exact outputs are:

```text
contact rank / nullity                         10861 / 317
old gradient rank                                      3
rank [old gradient ; scalar value]                      3
scalar-value map rank                                   0
nonzero specialization polynomials among 317            0
shifted-normal rank                                     3
old-plus-shifted-normal rank                            3
specialization degree bound                       <= 47
agreement multiplicity                            6*8=48
all L10 monomial Z-successors L11-legal                 yes
```

The reported canonical receipt begins `f433035f...`. This independently
falsifies the nonzero-value premise; it does not merely fail to find a
witness.

The same root-count reason persists at the target. For a reconstructed raw
polynomial `P`, specialize along the candidate polynomial `f` and boundary
seed `gamma`:

```text
trace(P) = P(X, f''/2, f, f', gamma).
```

The source inequality gives `deg trace(P) < 47*g`. Complete contact at each
of the `g` agreement nodes gives a root of multiplicity at least 47. Hence
`trace(P)=0`, so in particular its boundary value is zero. The accepted
source already contains the required ingredients:

- `SecondJetSpecialize.root_contact` converts local contact to node-power
  divisibility;
- `SecondJetSpecialize.specialization_degree` converts the weighted source
  inequality to the strict polynomial degree bound;
- `SecondJetVanish.eq_zero_of_contact_degree` performs the root count.

The lightweight formal companion
`.experiments/K0PassiveValueRootStop6900.lean` proves the same Hasse/root
statement directly. Its theorem
`oldKernelValue_eq_zero_of_depth47_root_bound` makes the entire old-kernel
value functional zero, and
`no_nonzero_oldKernelValue_of_depth47_root_bound` rules out the tempting
witness.

## Correct formal endpoint

`.experiments/K0PassiveValueNormalBridge6900.lean` proves all of the
following without fixed pivots or finite-dimensional assumptions:

1. Conditional value mechanism:
   `passive_difference_realizes_old_value` shows that
   `Zv-gamma*v` has boundary `value(v)e_Z`.
2. Its exact no-gain converse:
   `passive_shift_of_zero_value_stays_in_old_normal_range` shows that a zero
   old-kernel value map keeps every shifted normal in the old normal range.
3. The correct relative consumer:
   `normal_surjective_of_old_hyperplane_and_relative_repair` proves full
   normal surjectivity from an old residual hyperplane plus one pair `d,p`
   satisfying the two displayed relative equations.

For packet-compatible dual spaces of dimension greater than one, the family
version remains
`K0LineThenKill6900.normal_surjective_of_packet_separating_relative_family`:
one needs enough relative pairs to separate the whole compatible dual
space, not just one pair.

## Exact target cap legality

The cap side is green and is not the remaining uncertainty.

`K0PassiveValueNormalBridge6900` proves:

```text
target_rawShapeLegal_passive_succ_iff:
  for an already legal target monomial, its Z-successor is legal iff
  s+y+r+z < 3757;

target_L3756_to_L3757_passive_shift_legal:
  every cap-3756 monomial shifts into the cap-3757 target source;

target_rawShapeLegal_passive_succ_of_z_le_3692:
  the active cap <=64 gives a uniform legal successor for z<=3692;

target_y48_Z0_Z1_bands_legal:
  X^a Y^48 and X^a Y^48 Z are legal for every a<2188003.
```

This proves legality only. It does not turn any newly legal column into a
relative contact class.

The exact target margin flip makes this distinction load-bearing:

```text
cap L   source - 262144 * published one-node rank bound
3756                         -20,717,799
3757                          +2,371,080
```

The last layer adds 17,434,693,359 columns against 17,411,604,480 units of
all-node rank budget, improving the margin by 23,088,879. Thus cap 3756 is
not even known to have a contact kernel from the published dimension bound;
one cannot base the target proof on shifting a pre-existing cap-3756 kernel.
The attachment/relative connecting map is the target-native object.

## First unproved source hypothesis

If an old rank-three/residual-hyperplane stage has been constructed by some
other argument, the first missing producer is exactly:

```text
RELATIVE-PASSIVE-CONNECTING-NONZERO:
  there exist d in the new/legal passive scaffold and p in the old source
  with C(d)=C(p), but lambda(beta(d)-beta(p)) != 0.
```

Equivalently, the boundary map on the kernel of the connecting map

```text
new passive layer -> coker(C_old)
```

must be nonzero (surjective onto the residual line in the rank-three case).
No current m47 CRT, locator, or product-rule theorem proves this. The exact
finite ablation proves that some such relative class exists in its chamber,
but the first-pivot provenance depends on a large earlier passive scaffold
and does not provide a target-uniform formula.

For a higher-corank packet the required statement is the corresponding
separation/surjectivity of this relative boundary map, not merely
nonvanishing.

At the literal cap-3756/cap-3757 split even the old-hyperplane premise is not
currently available from dimension. A strongest end-to-end producer may
therefore need to prove the boundary rank of the whole relative kernel at
once, rather than first manufacturing a rank-three old stage.

## Build receipt

Both new Lean files compile independently with a 4 GiB Lean memory limit:

```text
lake env lean -j1 -M4000 .experiments/K0PassiveValueNormalBridge6900.lean
lake env lean -j1 -M4000 .experiments/K0PassiveValueRootStop6900.lean
```

Printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, `decide`, or `native_decide`.
