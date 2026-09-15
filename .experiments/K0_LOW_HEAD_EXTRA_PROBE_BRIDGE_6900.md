# K0 low-head extra-probe bridge

Date: 2026-09-15 UTC. Scope: lower-6900 corrected terminal route. This is a
formal interface, not a target interpolation theorem, candidate, or
submission.

## Result

The corrected last-three consumer uses contact coefficients
`epsilon^44, epsilon^45, epsilon^46`. Its complementary head is therefore
the **low** contact projection `epsilon^0,...,epsilon^43`. Older experiments
about the opposite `epsilon>=3` projection do not discharge this premise.

`K0LowHeadExtraProbeBridge6900.lean` records a small exact replacement target.
Let

```text
head  : Source -> OldHead
probe : Source -> Probe
readout : Probe -> Boundary4.
```

If the joint map `(head,probe)` is onto and `readout` is onto, then every
four-boundary value is realized by a source vector whose old low-head contact
is zero. Consequently the boundary map on `ker(head)` is onto. Feeding this
to the existing quotient-aware terminal detector proves that any compatible
complete-contact dual with zero terminal component has zero boundary
covector.

The intended target specialization makes `probe` the low-head contact at one
additional formal node and `readout` its four-coordinate boundary jet. This
turns the vague phrase "prove head rank four" into two concrete obligations:

1. a simultaneous `(n+1)`-point low-head interpolation/CRT theorem for the
   actual capped raw source; and
2. a local surjective readout from the extra low-head block to the four
   boundary coordinates.

## Capacity and the remaining gap

For the target raw source, the unchanged source dimension is
`65,061,789,117,960`. Replacing full multiplicity 47 by the low-head
multiplicity 44 changes the published one-node rank cap from `248,191,020`
to `213,740,910`. Thus the low-head source margin is

```text
65,061,789,117,960 - 262,144 * 213,740,910
  = 9,030,892,006,920.
```

Even subtracting one entire additional low-head block leaves
`9,030,678,266,010`. Capacity is therefore overwhelmingly sufficient for
the extra-probe formulation.

This arithmetic does **not** prove the joint map is onto. A dimension surplus
only constructs kernel vectors and cannot force a boundary rank. The
load-bearing theorem is the structured CRT/surjectivity statement for the
literal global source, including its weighted X taper and active/passive
caps. The bridge is useful precisely because it states that missing theorem
without silently replacing it by a dimension count.

## Verification

```bash
LEAN_PATH=.experiments lake env lean \
  .experiments/K0LowHeadExtraProbeBridge6900.lean -j1 -M4200
```

The replay takes about three seconds. All printed theorems use only
`propext` and `Quot.sound`; there is no `sorry`, `admit`, `decide`,
`native_decide`, explicit axiom, or unsafe declaration.
