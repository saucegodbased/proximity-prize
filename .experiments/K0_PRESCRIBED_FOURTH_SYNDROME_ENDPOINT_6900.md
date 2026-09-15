# K0 prescribed fourth-syndrome endpoint: exact GREEN, scalable carrier OPEN

Date: 2026-09-15 UTC. Scope: lower-6900 research only. This note records
finite exact linear algebra over prime fields. It is not a target theorem, a
Lean proof, or a submission claim.

## Verdict

The broad statement “the complete successor face is freely liftable once
`L >= U`” is false, including on the target side `2g-w<n`. The narrower
endpoint needed by the current argument nevertheless survives every exact
control in this audit:

```text
old contact-kernel boundary image rank = 3
successor contact-kernel boundary image rank = 4
```

This happens even though most successor-face relations are obstructed. In the
primary control, only 8 of 82 top-face kernel directions lift, but at least one
of those eight has nonzero value under the unique missing old boundary
covector. An adversarial off-agreement perturbation destroys the pretty sparse
face formula and still leaves the same `3 -> 4` endpoint.

The strongest honest status is therefore:

- **GREEN:** the literal prescribed missing boundary syndrome is hit in the
  stated target-sign, old-rank-three controls;
- **RED:** generic successor-face liftability and universal `L>=U` strictness;
- **OPEN:** a target-valid symbolic producer or theorem. The compact carrier
  found below has exponent `g`, which is source-legal in the small controls but
  not at the target, where `g=180413` while the active cap is only `U=64`.

## Exact dual criterion

Let `V0` be the old source, `F` the new face, and `V=V0+F`. Let

```text
C0 : V0 -> E0              old complete-contact map,
C  : V  -> E               successor complete-contact map,
D  : V  -> B = F_p^4       boundary (Y,R,S,Z).
```

Old columns have no successor top-contact rows, so `ker C0` embeds in
`ker C`. Put `W0=D(ker C0)`. When `dim W0=3`, choose the unique projective
covector `ell` with `ker ell=W0`. Then

```text
dim D(ker C)=4
  iff there exists v in ker C with ell(D(v)) != 0
  iff ell o D does not belong to rowspace(C).
```

Because `ell o D|V0` kills `ker C0`, it belongs to `rowspace(C0)`. Thus the
last condition says exactly that the old contact-row identity represented by
`ell` **cannot be extended across the new face**. This is the single-missing-
syndrome dual criterion; it is elementary finite-dimensional linear algebra,
not a heuristic rank correlation.

Equivalently, stacking the four boundary rows onto contact adds one more
cokernel obstruction than contact alone. In the primary control the contact
obstruction is 74 and the contact-plus-boundary obstruction is 75.

## Primary exact control and smallest certificate

The primary profile is

```text
(n,w,g,m,B,s,U,L,k,n0)=(8,3,5,5,4,2,7,7,0,1),  p=101,
agreement nodes={0,1,2,3,4}, candidate degree=3, tangent degree=4,
2g-w-n=-1.
```

Thus it has the target ratio sign and a genuinely positive successor top-face
kernel. Exact dimensions are

```text
old / face columns                         3304 / 765
contact ranks old / top / full            3299 / 683 / 4056
contact nullities old / full                 5 / 13
top kernel / obstruction / liftable         82 / 74 / 8
boundary ranks old / full                     3 / 4
```

In boundary coordinate order `(Y,R,S,Z)`, the normalized missing covector and
one normalized escaping boundary vector are

```text
ell = (1,24,41,29),       b = (96,14,33,36),       ell.b = 1 mod 101.
```

The smallest possible boundary-rank certificate is a `4 x 4` minor. The
deterministic certificate uses columns

```text
(12,78,21,76), (13,86,77,25), (11,63,78,81), b
```

and has determinant `81 mod 101`. The first three columns come from the old
contact kernel; the fourth comes from the full contact kernel.

Among the seven escaping columns in FLINT's deterministic nullspace basis,
the sparsest full witness has support `2001 = 1995 old + 6 face` and SHA256

```text
a77bbcd83439cc47be20b043095747b6c6cced0a45f24b859fe7585b6ea25561.
```

This is **not** claimed globally support-minimal. Its face projection is,
however, an unusually clean six-cell expression:

```text
58 X^22 Z^8 + 13 X^18 Y Z^7 + 75 X^14 Y^2 Z^6
+ 26 X^10 Y^3 Z^5 + 88 X^6 Y^4 Z^4 + 43 X^2 Y^5 Z^3
= 58 X^2 Z^3 (X^4 Z - Y)^5                         mod 101.
```

More generally, in all five polynomial-tangent controls the selected face
projection is verified coefficient-by-coefficient to be

```text
M(X) Z^(L+1-g) (Q(X) Z-Y)^g,
```

where `Q` is the recovered tangent polynomial. This explains the six cells
(`g+1` here), including dense `X` support when `Q` is dense.

## Robustness sweep

Every row below is an exact literal-contact computation. The contact
substitution is

```text
X=x+eps,
Y=u0+u1 Z+eps R-eps^2 S+eps^3 T  modulo eps^m,
```

and the third boundary coordinate is the faithful Hasse coefficient
`S=Hasse_2(P)=P''/2`.

| control | p | contact ranks old/top/full | top kernel/obs/lift | boundary | det | support old+face | tangent-power carrier |
|---|---:|---:|---:|---:|---:|---:|---|
| prefix/max/minimal, gamma 0 | 101 | 3299/683/4056 | 82/74/8 | 3->4 | 81 | 1995+6 | yes |
| same, gamma 5 | 101 | 3299/683/4056 | 82/74/8 | 3->4 | 81 | 1997+6 | yes |
| same data | 17 | 3299/683/4056 | 82/74/8 | 3->4 | 12 | 1910+6 | yes |
| spread nodes, mid candidate | 101 | 3299/683/4056 | 82/74/8 | 3->4 | 6 | 2009+6 | yes |
| random nodes, zero candidate, spike tangent | 101 | 3299/683/4056 | 82/74/8 | 3->4 | 80 | 2216+66 | yes |
| all three error directions shifted by +1 | 101 | 3299/710/4056 | 55/47/8 | 3->4 | 86 | 2396+445 | **no** |

The last row is the important adversarial control. There `u1` no longer
agrees with the recovered tangent polynomial on any error node. The escaping
witness uses 31 face cell types and all raw/`R`/`S`/`R^2+` sectors, so the
sparse tangent-power identity is genuinely gone; the prescribed rank-one
syndrome gain remains.

An independent larger target-sign control uses

```text
(n,w,g,m,B,s,U,L)=(12,5,8,6,4,2,8,8), p=101.
```

It has old/face columns `8091/1628`, contact ranks
`8082/1424/9701`, top kernel/obstruction/liftable dimensions `204/195/9`,
old/full contact nullities `9/18`, and boundary ranks `3->4`. This independently
repeats the endpoint with substantially larger `n,m,g`; it is available as
the script's `--large-only` mode.

## Why the generic claim is dead

For comparison, a literal target-sign arbitrary-error control at

```text
(n,w,g,m,B,s,U,L)=(12,5,8,4,2,1,5,5), p=101
```

has old/face columns `1342/368`, contact ranks `1342/357/1710`, top kernel
dimension 11, obstruction 11, zero liftable face directions, and boundary
ranks `0->0`. A second `s=2,B=4,m=5,U=L=7` target-sign control has top kernel
59 and obstruction 59. Therefore neither `L>=U`, target ratio sign, nor
positive face surplus alone implies any lift.

## Reproduction and receipts

```text
python3 .experiments/k0_prescribed_fourth_syndrome_endpoint_6900.py --summary
python3 .experiments/k0_prescribed_fourth_syndrome_endpoint_6900.py --large-only --summary
```

Default six-case sweep before adding the optional larger-mode switch:

```text
canonical receipt SHA256  4346f83bfde3bc617d417c6abece63140b60731c52c8b4cdb2380f536facf7b3
wall time                  113.461 s
peak RSS                   643056 KiB
address-space cap          4200000000 bytes
```

Current script and independent larger replay:

```text
script SHA256              572db0f94236712f689a6cc8d9ed996151e5655bb91a940b6cb38c4596e3b913
larger canonical SHA256    9fbfdf1ff2d2bb64e57ea769224bd722980055e107bbb75b0e9ff3a0a5137ae4
larger wall time           243.622 s
larger peak RSS            3010796 KiB
larger address-space cap   4200000000 bytes
```

The first larger replay tried to materialize FLINT's full nullspace and was
correctly stopped by the 4.2 GB address-space limit. The committed
`--large-only` path instead uses the exact identity

```text
rank(D restricted to ker C) = rank([C;D]) - rank(C),
```

so it obtains the same boundary endpoint by two ranks, without materializing
the large kernel. The script enforces the cap and asserts every old-rank-3 and
full-rank-4 result.
