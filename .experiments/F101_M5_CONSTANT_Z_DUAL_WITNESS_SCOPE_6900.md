# m5 constant-Z dual witness and scope correction

Date: 2026-09-14 UTC. Scope: lower-6900 research only. Production and the
accepted 6806 submission are unchanged.

The exact coefficientwise transpose calculation through every legal m5
passive grade has a particularly simple normalized separator for the naive
pure constant-Z target:

```text
ell = coefficient extraction at (Z, X-degree 0).
```

At grades 8, 9, 10, and 11, `ell` annihilates the complete contact-kernel
boundary image and pairs to one with pure constant Z. Its support is the
single row `(coordinate,degree,coefficient)=(3,0,1)` in every grade. Although
the boundary image contains many nonzero Z rows of X-degree 2 and above, its
constant-Z row is identically zero. The boundary ranks remain 12 while the
contact-kernel nullities are 71, 146, 221, and 296.

This explains the stable defect more sharply than a rank count, but it is not
a Full187 Z obstruction. The control contains the evaluation node zero, and
more importantly pure `e_Z` is not the correct fourth multiplicity-m packet.
The exact source-facing target is

```text
F3 = Lambda_H^(m-1) Lambda_(G\H)^m
       * (Y-P-(Z-gamma)q_H).
```

The independent shifted-domain audit in commit `f7330e6` proves that this
literal F3 packet is jointly correctable with F0/F1/F2 even while both pure Z
and bare normalized `Lambda_G Z` remain red. Therefore the present witness is
a STOP only for the standalone-Z replacement and passive-depth inference; it
must not be used as a target counterexample.

Reproduction:

```text
ulimit -v 4194304
python3 .experiments/f101_m5_z1_dual_witness_6900.py
```

The recorded run took 45.13 seconds and peaked at 760,804 KiB under the 4 GiB
address-space cap.

```text
canonical SHA-256 855750f434afd330cd3e5e1162f00f4b2adaf404559bfec7f3cd745dfcdbe89b
script SHA-256    b30a6e0eb347fc16675ac6379318c0a34e7d235e32b1c8df1a7bdc1687b74502
witness SHA-256   a812aaddfdedbe8ef86a4a720a32387bb38aee62c930bcfa5db02dc1a4f3eb66
```
