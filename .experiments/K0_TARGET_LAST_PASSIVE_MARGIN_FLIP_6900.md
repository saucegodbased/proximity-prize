# K0 target last-passive-layer margin flip

Date: 2026-09-14 UTC. Scope: exact integer source/rank arithmetic for the
lower-6900 k0 profile. This is a structural receipt, not a conormal theorem or
submission candidate.

## Exact result

For

```text
(n,g,m,B,s,U,k,n0)=(262144,180413,47,16,8,64,0,1),
```

the literal relaxed-source column count and published all-node rank budget
near the final passive cap are:

```text
L       source columns       local rank    source - n*rank
3748    64,904,876,877,729   247,593,240      -205,428,831
3749    64,922,311,571,088   247,659,660      -182,339,952
3750    64,939,746,264,447   247,726,080      -159,251,073
3751    64,957,180,957,806   247,792,500      -136,162,194
3752    64,974,615,651,165   247,858,920      -113,073,315
3753    64,992,050,344,524   247,925,340       -89,984,436
3754    65,009,485,037,883   247,991,760       -66,895,557
3755    65,026,919,731,242   248,058,180       -43,806,678
3756    65,044,354,424,601   248,124,600       -20,717,799
3757    65,061,789,117,960   248,191,020        +2,371,080
```

Thus the exact target is the first cap in this final ten-layer interval at
which the existing dimension certificate is positive. The last layer adds

```text
source columns                    17,434,693,359
one-node rank budget                      66,420
all-node rank budget              17,411,604,480
net margin improvement                23,088,879
```

and changes the certified margin from `-20,717,799` to `+2,371,080`.

## Interpretation

This makes the passive-layer connecting map target-native rather than a
finite-model curiosity. The cap-3756 source is not known to have any global
contact kernel from the published dimension bound, so a proof based on
shifting an already-existing old kernel is structurally mismatched. The
right object is the relative map created while the cap-3757 face is attached:

```text
new passive columns whose contact lies in the old contact image
  -> boundary modulo the old kernel's boundary image.
```

The exact m8 ablation independently found this distinction: active-face-only
columns leave gain three, passive reach alone restores gain four, and direct
`Z` shifts of old kernel relations are being audited separately. The target
arithmetic does not prove that the relative boundary map has rank four. It
does prove that the last passive layer is load-bearing for the only current
source-existence certificate, so that relative map is the correct theorem to
prioritize.

## Reproduction

Run:

```bash
python3 .experiments/k0_target_last_passive_margin_flip_6900.py
```

The script imports the literal integer transcriptions of
`SecondJetRelaxedGlobalCounts.coefficientCount` and
`SecondJetRelaxedCounts.rankBound` already cross-checked against the accepted
6810 definitions. It constructs no finite-field matrix and uses negligible
memory.

```text
canonical result SHA-256 c74a4a1728aaccbbe5b369b3d142b65c7cd4a9490504e5e0dc49dda7d8970948
script SHA-256           6c2435314ff7bb622780cebae587ea4540bd655e38a10e29d159b312b129df90
```
