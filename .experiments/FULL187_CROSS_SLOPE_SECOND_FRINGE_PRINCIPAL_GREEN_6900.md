# Full187 cross-slope second fringe: exact principal GREEN

Date: 2026-09-14

## Decision

**GREEN for the two named aggregate principal rows.**  The isolated
`(r,s)=(11,10)` shifted-Padé defect `7797` is not a defect of the physical
same-key system.  The neighbouring complete `q=0` coefficients

```text
P59^(10,10)  at outer Z=2624, width 470201 > N
P59^( 9,10)  at outer Z=2625, width 601271 > 2N
```

occur with scalar `1` in the two consecutive physical rows.  After retaining
all fixed terminal correlations and every other same-key origin, the exact
all-node block matrix is

```text
[ I_N       0 ]
[ K_actual  I_N ].
```

It has determinant `1`, rank `2N=524288`, and cokernel dimension `0` over
`F_2130706433`, for every value of the actual induced operator `K_actual`.
Thus these controls absorb the isolated `7797`-dimensional Padé cokernel.

This is deliberately **not** a GREEN for the full Full187 construction.  It
does not close the later-passive-`Z` outputs or positive-`u0` connecting tails
created by the two choices.  It says exactly that the old four-by-two
single-stream RED certificate cannot be promoted to a physical obstruction
without first quotienting the adjacent-slope pivots.

## Reproduction

From the repository root:

```bash
python3 .experiments/full187_cross_slope_second_fringe_confluence_6900.py
```

Observed receipt:

```text
decision                  GREEN_TWO_PRINCIPAL_ROWS_UNITRIANGULAR
same-key origins          row1=8, row2=20
rank / cokernel           524288 / 0
isolated defect removed   7797
canonical SHA-256         25d9183244332f41a53942f4b3da5557abf06ac22e70ae2c252cba57117d87eb
script SHA-256            2cc322266c4428bd112384a59eaf5782ce5c97b5a0df720a0a3f418af4f4de29
peak RSS                  35308 KiB
runner wall time          about 0.4 s
```

The executable uses only exact integer and target-field arithmetic.  Peak RSS
is reported by `resource.getrusage`; it is about 34.5 MiB, far below the 3 GiB
experiment ceiling.

## Literal expansion convention

For a source `Y^k`, choose `f` copies of

```text
contactY = E + T R - T^2 S/2,
```

`h` copies of frozen `U=u1`, and `rem=k-f-h` copies of `u0`.  Choosing `aE`
copies of `E` and `cS` copies of `-T^2S/2` gives target key

```text
(T,E,R,S,Z) =
(q+f-aE+cS, aE, f-aE-cS+r, s+cS, z+h)
```

and exact scalar

```text
binom(k,f) binom(k-f,h)
* f!/(aE! cS! (f-aE-cS)!) * (-1/2)^cS.
```

`Hq` below is the coefficient Hasse derivative.  `U` is frozen, so it stays
outside `Hq`.  The script inverts this key formula over all 187 physical
shapes and all `P0,...,P59`; it does not start from a hand-selected list.

## Row 1: every same-key origin

The first target key is

```text
(T,E,R,S,Z) = (59,0,69,10,2624).
```

Writing `C_rs` and `Pk_rs` for the physical shape `(r,s)`, its complete raw
aggregate is

```text
  [ H1(P58_11,10) + 59 U H1(P59_11,10)
    + binom(61,58) U^3 H1(C_11,10) ]

+ [ P59_10,10 + binom(62,59) U^3 C_10,10 ]

- 29 [ P58_12,9 + 59 U P59_12,9
       + binom(61,58) U^3 C_12,9 ].
```

The `-29` is the literal `cS=1` contact scalar `-58/2`.  This exposes the
curvature-neighbour `(12,9)` collision that a pure `s=10` enumeration omits.
There are exactly eight origins:

|kind|`(r,s)`|`k/y`|`f,h,aE,cS,q`|width|scalar before `U^h Hq` mod `p`|
|---|---:|---:|---:|---:|---:|
|C|(12,9)|61|(58,3,0,1,0)|76988|2129662723|
|P|(12,9)|58|(58,0,0,1,0)|470201|2130706404|
|P|(12,9)|59|(58,1,0,1,0)|339130|2130704722|
|C|(10,10)|62|(59,3,0,0,0)|76988|37820|
|P|(10,10)|59|(59,0,0,0,0)|470201|1|
|C|(11,10)|61|(58,3,0,0,1)|76989|35990|
|P|(11,10)|58|(58,0,0,0,1)|470202|1|
|P|(11,10)|59|(58,1,0,0,1)|339131|59|

All eight have `u0` power zero.

## Row 2: every same-key origin

The next target key is

```text
(T,E,R,S,Z) = (59,0,68,10,2625).
```

Its twenty origins group into six exact Pascal/contact brackets:

```text
  [ H2(P57_11,10) + 58 U H2(P58_11,10)
    + 1711 U^2 H2(P59_11,10)
    + binom(61,57) U^4 H2(C_11,10) ]

+ [ H1(P58_10,10) + 59 U H1(P59_10,10)
    + binom(62,58) U^4 H1(C_10,10) ]

+ [ P59_9,10 + binom(63,59) U^4 C_9,10 ]

- 29 [ P58_11,9 + 59 U P59_11,9
       + binom(62,58) U^4 C_11,9 ]

- (57/2) [ H1(P57_12,9) + 58 U H1(P58_12,9)
           + 1711 U^2 H1(P59_12,9)
           + binom(61,57) U^4 H1(C_12,9) ]

+ 399 [ P57_13,8 + 58 U P58_13,8 + 1711 U^2 P59_13,8
        + binom(61,57) U^4 C_13,8 ].
```

Here `1711=binom(59,57)`, `-57/2` is interpreted in the target field, and
`399=binom(57,2)/4`.  Thus the exhaustive audit adds the curvature diagonals
`(11,9)`, `(12,9)`, and `(13,8)` to the three `s=10` brackets.  The executable
prints every one of the twenty widths and mod-`p` scalars and asserts them
against a frozen exact signature.  Every origin again has `u0` power zero.

## Exact correlated section

Let `b1` be the value of the whole first aggregate except
`H0(P59_10,10)`.  It includes, rather than frees or discards,
`binom(62,59) U^3 C_10,10` and the seven other listed origins.  Prescribe the
actual all-node coefficient jet by

```text
x20 := H0(P59_10,10) = -b1.
```

This is legal because its width `470201` contains a complete `N=262144`
q=0 Hermite block.  It is the physical coefficient polynomial; no arbitrary
row variable has been added.

Fix any deterministic legal interpolation/continuation section for this
prescription.  Its induced higher jets, and all dependent `d20` corrections,
define an actual linear operator `K_actual`.  Let `b2` be the second aggregate
with those induced terms retained but without `H0(P59_9,10)`.  It includes
both the fixed `C_9,10` terminal term and the entire correlated `d20 q1`
bracket.  Now prescribe

```text
x19 := H0(P59_9,10) = -b2 = -b2_fixed - K_actual x20.
```

Its width `601271` contains two complete node-Hermite blocks, hence certainly
the required q=0 block.  It cannot feed backward into row 1 because its outer
passive exponent is already `2625`, while contact expansion never lowers `Z`.
This proves the block-unitriangular matrix and its explicit section without
assuming anything about `K_actual`.

Equivalently, if both rows are presented with arbitrary right sides, the
inverse is

```text
x20 = -b1,
x19 = -b2 - K_actual x20.
```

No identification among `C_11,10`, `C_10,10`, `C_9,10`, or the curvature
terminal coefficients is made.

## Outgoing-tail audit and precise stopping point

The script enumerates every structural target of each pivot coefficient,
including the higher coefficient Hasse jets induced by a fixed q=0
interpolation section.

For `P59_10,10` at outer `Z=2624`:

```text
principal occurrences                         1
named next-row occurrence                     1
other u0-free occurrences                109173
distinct u0-free target keys             109175
positive-u0 occurrences                 4083068
minimum nonprincipal u0-free Z              2625
```

For `P59_9,10` at outer `Z=2625`:

```text
principal occurrences                         1
other u0-free occurrences                109174
distinct u0-free target keys             109175
positive-u0 occurrences                 4083068
minimum nonprincipal u0-free Z              2626
```

The exact invariant is stronger and simpler than the counts: for a `P59`
source, an agreement-visible term has `h=59-f`, hence output passive exponent
`Z_out=z+59-f`.  Survival at `f=59` forces `aE=cS=q=0`, the unique unit pivot.
Every other `u0`-free term has `f<59` and therefore `Z_out>z`.  The first
pivot's `f=58,h=1,q=1,aE=cS=0` term is precisely its occurrence in row 2.

So the two-row section is causally sound, but it exports a large strictly
later-`Z` boundary plus positive-`u0` terms.  The next honest task is to close
that exported boundary under the same-key aggregate order.  Reporting this as
a full construction would be an overclaim.

## Authority and frozen inputs

This audit implements the literal `residual_expression` / contact convention
and complete-depth widths from:

```text
d9c351812caded22dd2cf90abfa6892b830180854d68fdff641bcf4037c7bcae
  full187_all_noncapacity_pascal_hermite_slide_6900.py
e6de6ca5273bcae6e369b7ffd779c815a393c6e7e3494ee8853f7c3ab1d46969
  full187_complete_depth_pascal_hermite_slide_6900.py
af09d1069bee7abe9ddf9225d46521dfd20271d87e52ec7d5c96c3f37115c913
  full187_terminal_lowT_hasse_closure_audit_6900.py
```

The isolated RED being superseded only at this principal scope is commit
`500026a0541391228975c90430b741f6c7586305`, with input artifacts:

```text
9098972b5ea3da9c54453c8f58a8a0ea02dfe0bb565c965e7979019f3ca60a2a
  full187_second_fringe_order_basis_data_6900.py
8b3164645e61a5d776f9ee6646556bf876ec5d4b4710902519806e15cbf512a6
  full187_second_fringe_order_basis_gate_6900.cpp
a1201966d5669ece91b114560c8bac93a541749449d153fa6a873d85a1b5282a
  FULL187_SECOND_FRINGE_C1_SHIFTED_PADE_STOP_6900.md
```

The first-fringe authority commits requested for this follow-up are
`b535ccce84967a94f9640e4c1101eb2de4f3fd69` and
`919209534d70e261f083594a62e92fd0ae9b67fe`.
