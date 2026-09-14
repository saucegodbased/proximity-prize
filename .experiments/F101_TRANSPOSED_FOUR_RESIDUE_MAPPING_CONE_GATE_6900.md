# Transposed four-residue filtered mapping-cone gate

Date: 2026-09-14 UTC. Scope: lower-6900 source research only. Production,
submission, `score.txt`, `radius.txt`, and the accepted 6806 result were not
changed. There is no 6900 candidate.

## Verdict

The target-only transpose is implementable without constructing an ambient
contact cokernel or asking for a contact-kernel basis. It also exposes a
strictness failure that polynomial-rank gates conceal:

* in the exact `m=5` grade-`J+1` control, all three prescribed locator-normal
  Y/R/S right-hand sides are contained, but the filtered constant-Z1 class is
  not;
* after packing coefficient rows into four polynomials and localizing to
  `F_101(X)`, the same image has rank four and contains the four-target frame;
* therefore fraction-field four-rank is not a valid replacement for the
  coefficient-windowed THREE-RHS plus Z1 recurrence;
* in the `m=7` control, both grade `J` and grade `J+1` are contact-injective.
  All 129 terminal-diagonal relations map injectively through the connecting
  map, so the uniform first-shell recurrence is decisively STOP.

The `m=7` result stops only the proposed uniform `J -> J+1` extrapolation. It
does not bear on the target's 72,850 deeper structured transitions. Likewise,
the `m=5` Z1 failure is a discriminator for filtered versus localized
recurrences, not a counterexample to Full187.

## 1. Artifact audit and the missing distinction

The audit used `grep` because `rg` is unavailable in this workspace.

`FULL187_THREE_RHS_Z1_DUAL_TERMINAL_COUNTERGATE_6900.md` fixes the exact
minimal target. With `U=ker C_G`, `W=ker J_YRS`, and `D=C_E`, the three
corrections hold iff every `lambda` satisfying

```text
D* lambda in range(J*)
```

annihilates the three distinguished syndromes. Z1 is the separate condition
that `z*` not lie in `range(D,J)*`. The note and its Lean proof have SHA-256

```text
note eca83618af10961ee09ffffa9e0bf2f7de5b5323bb35678d288c401cf53a520e
Lean ea2c2206b20bd5804658b677f6d9fd87e7554c67a530677957f289afdd6246aa
```

`FULL187_DIRECT_DUAL_HERMITE_RECURRENCE_AND_CAPRICH_GATE_6900.md` proves the
local/global Hermite recurrences but also records exact failures of the fixed
annihilator and parameter-uniform direct-contact shortcuts. Its note and Lean
recurrence file have SHA-256

```text
note 778c7f004993a2d2227a6914404e6fefde37901c86b92e5e78889d612cb13c8b
Lean 7236d0c7a12c8b44dea5d39e2a3ea112b593f72c9e476e0d8ca88269f2b9c05c
```

`GlobalO2RawGradedMappingConeGate6900.lean`, SHA-256
`0783623abb18ffa22391477692fcc10a9da60e20fc83f1a3ffd334818da5b6c6`,
proves the exact prefix/terminal sequence and the Schur consumer, but
deliberately makes no rank claim. The current checkpoint,
`2026-09-13-current-checkpoint.md`, SHA-256
`d5e9c92f14c22b42c81b4668878fb28b65b5c44933ed37b302bab6f43cc4adc6`,
likewise leaves exactly THREE-RHS plus the independent Z1 class.

Commit `cd384ce` already stops the complete fixed order-four/full11 family:
248 new quotient modes leave all three RHS defects nonzero, and three exact
duals pair with `(F0,F1,F2)` with determinant 40 modulo 101. The new gate does
not enlarge that dead carrier list. It asks only what happens to the four
distinguished target residues in the complete filtered contact map.

## 2. Exact transposed construction

For a centered-grade prefix, let

```text
C_q : V_<=q -> W_<=q
```

be the complete literal contact map. Order grade-`q` source columns first and
top contact rows first. The script checks that every top row vanishes on every
lower-prefix column, so this is literally the transpose of the lower-triangular
block in the formal mapping cone.

Row-reduce `C_q`. For each legal coefficient covector `b` in only the four
linear boundary channels Y/R/S/Z, reduce `b` modulo `range(C_q*)`. Its free
coordinates are the restriction of `b` to `ker C_q`; no other contact-cokernel
class is generated. Stacking these remainders gives the exact coefficientwise
boundary image on the complete contact kernel without computing a kernel
basis.

The script makes two deliberately separate tests.

1. Over `F_101`, retain every legal coefficient row. Project to Y/R/S and
   test the three exact locator-normal columns. Separately test the pure
   constant-Z column in the full Y/R/S/Z image. This is the strict filtered
   THREE-RHS plus Z1 gate.
2. Pack each free-coordinate column into a four-polynomial residue and compute
   its rank over `F_101(X)`, using explicit nonzero polynomial minors. This is
   a useful localized recurrence diagnostic, but it is weaker because
   rational-function multipliers forget the source windows.

The three localized locator columns, padded with zero Z, together with pure
Z form an invertible four-frame. Thus localized containment is a genuine
rank-four statement. The `m=5` split below proves why it must not be promoted
to the filtered claim.

## 3. The decisive m5 discriminator

The control is

```text
(n,w,g,m,D,s,t,J,L)=(10,4,7,5,35,1,1,7,11),
offsets=(3,5,7), field=F_101.
```

Exact receipts are:

| maximum grade | source columns | contact rank/nullity | localized four-rank | exact YRS image rank | exact full image rank | RHS joint defect | Z1 defect |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 7 (`J`) | 2296 | 2296 / 0 | 0 | 0 | 0 | 3 | 1 |
| 8 (`J+1`) | 2751 | 2680 / 71 | 4 | 12 | 12 | 0 | 1 |

At `J+1`, all three individual RHS defects are `(0,0,0)`. Nevertheless the
Y/R/S projection and full Y/R/S/Z coefficient image both have rank 12, so
there is no nonzero Z direction on the Y/R/S-zero filtered kernel. In
particular pure constant Z1 has defect one.

By contrast, localization gives four independent polynomial residues. Its
basis SHA-256 is

```text
84afe948d60ecb1806cc168be0994eb1e493b1ef60b6ffe35d9e13ab900fb63b
```

and successive exact minor degrees/hashes are

```text
30   39f5bd9a869d416c7d9a4bba0102ccab86e79b0e65d9f9e6dbf71468f78aecda
61   231bab1f205e8b38ccf45c5f8dc8d0da4e835bbaa08f30f62cb0226a4c709e66
95   4eb73bcad631a30d1eb71e81acacc65c0ad4b7d29499c645520ab2f481ba05cf
127  678af9272de81caad6ff803c11638e764532a77fabf22e14dcca20be848956f0
```

The mapping-cone receipt is also exact:

```text
prefix rank/nullity           2296 / 0
terminal diagonal rank/nullity 380 / 75
full rank/nullity             2680 / 71
connecting rank/kernel           4 / 71
```

An independent one-off calculation did ask FLINT for the complete contact
kernel and then formed its coefficient boundary image. It reproduced contact
rank/nullity `2680/71`, Y/R/S rank and target defects
`12,(0,0,0),0`, full rank 12, and Z1 defect 1. Its packed kernel-boundary
column hash was

```text
78a9a21096ddc015fc6a49f6c6ecdacbeeb91b220a0f9a6fc54dd898b0e09019
```

This independent check is not used by the main executable; it validates the
transpose remainder calculation.

## 4. The m7 first-shell STOP

The second control is

```text
(n,w,g,m,D,s,t,J,L)=(10,4,7,7,49,1,1,9,13),
offsets=(3,5,7), field=F_101.
```

| maximum grade | source columns | contact rank/nullity | localized four-rank | RHS joint defect | Z1 defect |
|---:|---:|---:|---:|---:|---:|
| 9 (`J`) | 5260 | 5260 / 0 | 0 | 3 | 1 |
| 10 (`J+1`) | 6119 | 6119 / 0 | 0 | 3 | 1 |

The grade-10 terminal diagonal has rank/nullity `730/129`. The connecting map
has rank/kernel `129/0`: every diagonal relation is killed before it becomes a
complete contact cycle. This exactly agrees with the independent
kernel-generating gate `f101_n10_m7_first_shell_target_gate_6900.py`, canonical
SHA-256
`a65d2dbd8fa7a0c5a9cc1351b69662f509ff95bfcbf7110425cde84ced54be02`.

This is a clean STOP for a universal `J+1` first-shell rule. It is not a STOP
for the target, whose terminal shell has large positive surplus and whose
remaining recurrence is deeper than this two-prefix test.

## 5. Correct target truncation and refund

Every literal contact edge obeys

```text
q + f + 2*aE + cS < 60.
```

For the same-grade `q=0,aE=cS=0` specialization this forces `f<=59`. Hence a
grade-82 source has passive refund `h>=23`, and

```text
D - 59*w = 3,091,591 > n=262,144
```

by 2,829,447. The old imagined `Y^82 -> Y^81 Z` same-grade edge does not
exist, so no conclusion here relies on the earlier literal-PC window STOP.

For `aE=0`, the raw target row

```text
(T,R,S)=(f+cS,f-cS+r,s+cS)
```

has the diagonal source

```text
(y',r',s')=(f+cS,r-2*cS,s+cS)
```

whenever `2*cS<=r` and `s+cS<=10`. Its weighted charge is exactly preserved:

```text
w(f+cS)+(w-1)(r-2*cS)+(w-2)(s+cS)
  = w*f+(w-1)*r+(w-2)*s.
```

In the target `q=aE=0` census there are 173,910 surviving terms: 43,670 are
in this easy diagonal sector, 123,820 have `2*cS>r`, and 6,420 hit curvature
overflow after the `2*cS` guard. Thus genuine confluence work lies in
`aE>0`, `2*cS>r`, or curvature overflow, not in the easy raw diagonal.

Commit `0624791` gives the corrected terminal Hermite census. Of 1,266,925
surviving contact choices, 1,194,075 are agreement-Hermite green and 72,850
need a structured low-`f` recurrence. The latter collapse to 1,056 unique
`(f,aE,cS)` types, all with `2*aE+cS<=13`; every extra charge at least 14 is
green. The current census and Lean sources have SHA-256

```text
census canonical 67fd33c85a6cef2809e6ef048f7d4915c1b9546ccd413481654c55108fcbe4e3
census script    3c0fb82a99bcca19e6aebbce7d02b925570f2de337ddc5c71eb002d068766a7d
Lean refund      5141a30e2fdecdcfa5456de907445ccdb4f3b4cb3d83a4ed52fcb7c148617b79
```

There are eleven apparent `h=2,f=59,r+s=21,aE=cS=0` product cliffs, but they
are not transition obstructions. Contact weight 59 has Hermite depth one;
reduce `u1^2*p` modulo the all-node locator to degree below `n`, and the
predecessor window is wider than `n`. Thus all eleven are linearly GREEN. The
one-degree equality stops only the unreduced-product ansatz. The actual
structured frontier remains the 72,850 low-`f`/deeper cases, not eleven
leading moments.

## 6. Next exact target-only probe

Do not build an ambient 187-channel cokernel and do not revisit fixed full11
carriers. Quotient out the 1,194,075 unconditional Hermite-green choices,
apply the raw diagonal extension above, and carry only four coefficientwise
residues seeded by `(F0,F1,F2,Z1)`.

The cheapest first layer is extra charge 13. The whole structured census has
only 33 choices and three transition types there:

```text
(f,aE,cS)=(7,6,1), (8,5,3), (8,6,1).
```

Build the exact sparse transposed connecting map for just these three types,
with coefficients retained modulo the all-node locator and with the legal
strict windows left in place. Test the four seeded residues, especially the
Z residue after imposing Y/R/S zero. A nonzero leading filtered residue gives
an immediate dual STOP. If all four vanish, descend to extra charge 12, which
has only 21 types and 352 choices, and continue one charge layer at a time.

The m5 discriminator is the acceptance test for that implementation: it must
return THREE-RHS green and Z1 red. Any implementation returning only
localized rank four has silently inverted a polynomial or discarded a
coefficient cutoff and is not the target recurrence.

## 7. Reproduction and hashes

The executable is

```text
.experiments/f101_transposed_four_residue_mapping_cone_gate_6900.py
```

with SHA-256

```text
68282bc22745463d03c5158165e76d378557ec650ae87e5575007bc3f1056f0a
```

Commands:

```text
prlimit --as=6442450944 --rss=6442450944 \
  python3 .experiments/f101_transposed_four_residue_mapping_cone_gate_6900.py \
  --case m5

prlimit --as=6442450944 --rss=6442450944 \
  python3 .experiments/f101_transposed_four_residue_mapping_cone_gate_6900.py \
  --case m7
```

Final canonical receipts are

```text
m5 ee1ae7938258bad5f5326a9e28c586b8ff01c59548e18c23f640b3315b8a624b
m7 db16c60eec7a12fee97160aaab2cfa834bf7e12a6e0ec32d0af3c6934c28c11b
```

The final m5 run took 17.77 seconds and peaked at 457,464 KiB RSS. The final
m7 run took 128.27 seconds and peaked at 2,226,160 KiB RSS. Both stayed below
the explicit 6 GiB address-space and RSS limits. The main executable never
called `nullspace` and never materialized an ambient kernel or cokernel.

Final process decision:

```text
STOP  localized four-rank as a filtered THREE-RHS+Z1 proof
STOP  fixed full11 and uniform J+1 first-shell recurrence
GO    four coefficientwise residues on the 72,850 low-f/deeper cases,
      starting with the three extra-charge-13 transition types
```
