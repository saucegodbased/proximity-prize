### Lower 6900 breakthrough: full legal source has exact boundary gain four in the capacity-positive gate

Verified floor remains **6810** (`09d8a2a`, submission
`1852e895-c0db-46ad-8705-e0c92d638224`).  This is a research result, not a
6900 candidate or submission.

The decisive full-source discriminator has finished.  Over F101, on the
faithful capacity-positive profile

```text
(n,w,g,m,B,s,U,L,k,n0) = (8,3,5,8,3,1,12,16,0,1)
full source columns        17,679
published local bound       2,179 per node
dimension-forced margin       247
literal contact rows       23,720
```

the exact destructive RREF results are

```text
rank(contact)                    17,411
contact kernel dimension            268
rank([contact; 4 boundary rows]) 17,415
boundary image of contact kernel       4
```

Thus the full legal source realizes all four boundary directions in this
model.  This classifies the prior sparse-family failure correctly: the
9,964-column `{1,R}` + subcritical-S + one SYR connector + two critical-cell
family was injective, but the omitted high layers rescue a 268-dimensional
kernel and all four conormal directions.  They are not dispensable padding.

Exact receipts:

```text
contact canonical SHA256
3ebfbdb8b5583f4384e4bb1d862b96a440de9322b0329f71b736378d2c4cf8af

augmented canonical SHA256
4cc1465cab2e6c01795573d9969acba36ef585ecc1998835f2cd8188cb8e200f

augmented runtime       800.112 seconds
augmented peak RSS      5,741,820 KiB (~5.48 GiB)
```

The receipt uses trial 811, agreement set `{0,1,3,4,6}`, seed 0, candidate
degree 4, and tangent degree 4.  The matrix was `23,724 x 17,679`; it ran
under a hard 7.5 GiB process cap.  The computation is exact finite-field
linear algebra, not a floating-point or heuristic rank estimate.

The research branch is

https://github.com/saucegodbased/proximity-prize/tree/codex/6900-live-research

New formalization progress also removes a build-process blocker.  Rebuilding
the 49k-line `LowerFoundation` aggregate repeatedly exceeds an 8.19 GiB Lean
cap near line 49,300, so that route is frozen.  Commit `63f2744` instead
extracts an 11 KiB Mathlib-only literal raw-index/contact core and compiles it
in 11 seconds.  It includes the exact dependent `budget/yCount/Index`, raw
basis reconstruction, localization/contact composite, and typed selectors.

The simultaneous top faces

```text
h+y+r=64, 2h+r=16, h=0..8
r=16-2h, y=48+h
```

now have a compiled typed constructor in the actual raw source.  Every face
has uniform X width 90,883 and Z width 3,694, so every face contains at least
47 consecutive legal X indices.  Axiom audit: only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry`, `decide`, or
`native_decide`.

What remains, honestly: the finite gain-four result proves that there is no
obvious underlying full-source rank obstruction, but it does not transport
to the target field/profile automatically.  The next hard theorem is a
literal 47-coordinate Hasse observation block on the typed top shell,
followed by global propagation through every weighted-cap seam.  We will stop
the recurrence route if that block is not unitriangular/non-singular or if a
seam requires an out-of-source neighbor.  In parallel we are attributing the
four gains among the omitted `SR`, `R^2`, and `R^3` layers so the target
theorem can be made as small and explicit as possible.
