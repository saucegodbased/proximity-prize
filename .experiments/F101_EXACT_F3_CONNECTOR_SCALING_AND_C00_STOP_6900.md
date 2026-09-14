# Exact F3 connector scaling and the pure-C00 STOP

Date: 2026-09-14 UTC. Scope: lower-6900 research only. This note records
exact coefficientwise finite controls and a theorem-shaped source-legality
statement. It is not a Full187 theorem, candidate, score, or submission.

## Decision

The m=4 matched control has a useful but accidental rank-one collapse. Modulo
the complete grade-6 source, the exact `F0,F1,F2,F3` packet has quotient rank
one and is spanned by the pure centered shell

```text
C00 = (Y-QZ)^4 Z^3.
```

This does **not** persist. In the same chamber at m=5 and m=6, the exact
packet has quotient rank four, while `C00` is a fifth independent class.
Consequently there is no universal nonzero scalar relating the four packet
residues to `C00`; the m=4 scalar row must not be extrapolated to m=60.

The reusable positive fact is narrower: `C00` is universally source-legal
at exact `g`, and its agreement contact vanishes. What remains is a coupled,
coefficient-sensitive connecting-map theorem. The first higher-m controls
show that whole derivative-shape groups can close the packet even though one
canonical centered monomial cannot.

## The exact m=4 connecting class

The fixed control is

```text
F_101,
(N,w,g,m,D,q,t,J,L)=(10,4,7,4,28,1,1,6,10),
G={0,...,6}, E={7,8,9}, Q=Xi_E^2,
H={0,...,4},
F3=Lambda_H^(m-1) Lambda_(G\H)^m (Y-q_H Z).
```

All calculations use the literal all-node contact map and coefficient rows;
there is no passage from `F_101[X]` to `F_101(X)`. The grade-at-most-6
prefix has 1,351 columns and rank 1,351. Each of the four exact packets has
defect one, but their joint quotient rank is one. Relative to `F0`, their
residue scalars are

```text
(F0,F1,F2,F3) = (1,6,3,61) [F0]                 in F_101.
```

The deterministic source solve is exactly

```text
[F0] = 4 [ C(C00) ],
```

so the induced `1 x 4` connecting row relative to `[C(C00)]` is

```text
(4,24,12,42).
```

Each complete grade-7 derivative-shape group `(0,0)`, `(0,1)`, or `(1,0)`
separately contains this common class. Their inclusion-minimal source
representatives are, respectively,

```text
 4 (Y-QZ)^4 Z^3,
62 S (Y-QZ)^4 Z^2,
11 R (Y-QZ)^4 Z^2.
```

This is an exact description of this finite connecting map, not a universal
formula. The agreement four-normal determinant remains the separate identity

```text
unit * Lambda_G^(4m-3) * (Q-q_H)/Lambda_H.
```

It proves independence of the intended agreement packet when the final
factor is nonzero; it does not force the connecting scalar above to remain
nonzero.

## The m=5 and m=6 falsification

The same `N,w,g,Q,H` and exact packet were replayed with

```text
m=5: (D,J,L)=(35,7,11), prefix rank 2296,
m=6: (D,J,L)=(42,8,12), prefix rank 3582.
```

In both cases all four packet residues are nonzero and have joint quotient
rank four. The pure shell residue is nonzero but independent:

```text
rank(packet)=4,
rank(packet + C00)=5.
```

At m=5, the complete raw `(r,s)=(0,0)` first-shell group nevertheless closes
all four packets. Neither the `R` group, the `S` group, nor `R+S` does. Thus
the minimal shape set is `{(0,0)}`, but four different coefficient
combinations inside that group are needed; `C00` alone is not enough.

At m=6 no single group closes the packet. The unique inclusion-minimal shape
set is

```text
{(0,0),(1,0)}.
```

Pure plus curvature remains defect four, and slope plus curvature without
the pure group remains defect four. This evolving pattern is the highest-risk
part of any m=60 extrapolation.

### Arbitrary-error replay

The complete test was repeated after replacing the error-node values of `Q`
by `Q+(3,5,7)`, while leaving every agreement value and the exact four
normals unchanged. At m=5 the result is robust: the raw pure group alone still
closes all four packets. At m=6 the matched two-shape answer is **not** robust.
The unique inclusion-minimal set becomes

```text
{(0,0),(1,0),(0,1)}.
```

Every proper subset leaves all four packets individually at defect one and
joint defect four. Thus `{pure,R}` is a matched-direction artifact at m=6;
the smallest candidate supported by this arbitrary-error replay includes the
curvature group as well. All three shapes lie in conservative103. This is a
finite robustness gate, not a proof for arbitrary symbolic error values.

## Exact universal source-legality statement

Put `D=m*g`, assume `deg Q <= g-1`, `w<g`, `m<=J+1`, and `J+1<=L`. Expanding

```text
C00 = (Y-QZ)^m Z^(J+1-m)
```

gives, for `0<=f<=m`, a term proportional to

```text
Q^(m-f) Y^f Z^(J+1-f).
```

It obeys every literal source cap:

```text
active degree             f <= m <= J+1,
derivative shape          (r,s)=(0,0),
combined Y/R/S/Z degree   f + (J+1-f) = J+1 <= L,
X degree                  <= (m-f)(g-1).
```

The exact weighted-width gap is

```text
m*g - ((m-f)(g-1) + w*f)
  = m + f*(g-w-1) > 0.
```

Equivalently, relative to the largest admitted integer X degree, the slack is

```text
(m*g-w*f-1) - (m-f)(g-1)
  = m-1 + f*(g-w-1).
```

For Full187,

```text
(m,g,w,J,L)=(60,180413,131071,82,2703),
g-w-1=49341,
```

so all 61 expansion layers are legal. The minimum strict slack is exactly 59
at `f=0`; at `f=60` it is 2,960,519. The seed exponents range from 83 down to
23. At an agreement the centered value has positive contact weight and its
60th power vanishes in the order-60 truncation.

These facts are already proved over an arbitrary field in the green,
axiom-audited working-tree module `HrsCenteredShellUnit6900.lean`, notably
`centered_shell_weighted_term_lt`,
`pureCenteredShell_mem_passiveSourceSpan`, and the local agreement-contact
lemmas. They establish membership and contact, not packet connectivity.

## Complete-source legality is not safe103 terminal membership

The conservative 103-shape audit concerns monomials on the literal deleted
face

```text
y+r+s=J,   y+r+s+z=L.
```

The unshifted `C00` has combined grade `J+1=83`, not `L=2703`. Even after
multiplication by `Z^(L-J-1)`, every expanded term has active degree
`f<=60<J=82`; it therefore does not lie on the deletion face at all. Its
complete-source legality does not depend on the safe103 theorem. Abstractly
its derivative shape `(0,0)` is of course one of the conservative103 shapes.

The m=6 finite connector additionally uses raw shape `(1,0)`, also in
conservative103. For a completely arbitrary `Q` of degree `g-1`, a naive
centered companion

```text
R (Y-QZ)^60 Z^22
```

need not be source-legal. Its `f=0` term can have cost

```text
60(g-1) + (w-1) = D + 131010,
```

which exceeds the largest admitted cost `D-1` by 131,011. The analogous `S`
companion can exceed it by 131,010.

That worst-case warning does **not** apply to the intended retained-bad
direction `Q=Xi_E^2`. Here `e=N-g=81731`, hence

```text
deg Q = 2e = 163462,
g-deg Q = 16951,
deg Q-w = 32391.
```

For `R^r S^s (Y-QZ)^60 Z^(23-r-s)`, the exact width gap at centered layer
`f` is at least

```text
60*(g-deg Q) + f*(deg Q-w) - (w-1)r - (w-2)s.
```

It is minimized at `f=0`. For `(r,s)=(1,0)` the gap is 885,990, giving
strict integer slack 885,989; for `(0,1)` it is one larger. Thus the honest
centered first-slope and first-curvature companions are target source-legal
for `Xi_E^2`. More generally this crude degree bound admits `r+s<=7` (subject
to the actual derivative caps). Only an arbitrary-degree-Q theorem needs a
taper or a coupled cancellation.

## Scaling discriminator

A second exact chamber uses the smallest positive second-derivative weight:

```text
N=7, w=3, g=5, E=2, Q=Xi_E^2, D=5m,
J=m+1, L=J+1, q=t=1.
```

Here the prefix is injective and the four packet residues have quotient rank
four. The unique minimal first-shell shape set is `{(0,0),(1,0)}` for every
tested `m=4,5,6,7,8`. This stable run is evidence against immediate growth of
the required slope order: the largest observed `r` remains one. It is not a
recurrence proof, and changing the chamber can change the answer (as the
primary m=4/m=5 comparison already demonstrates).

The same small chamber with nonmatched error offsets `(3,5)` was then tested
at m=7 and m=8. In both cases the unique minimal subset is exactly

```text
{(0,0),(1,0),(0,1)}.
```

At both multiplicities pure plus slope reduces the joint defect from four to
two (and solves only `F1`), but curvature is required for the remaining three
packets. The all-three group closes coefficientwise. Thus the arbitrary-error
sequence through m=8 still has maximum derivative exponents `r=s=1`; there is
no finite evidence that the required order grows like m or threatens the
safe103 bounds. This is the strongest current scaling evidence for a fixed
three-shape Schur block, but it remains finite evidence.

## Reproduction and receipts

```text
python3 .experiments/f101_matched_f3_terminal_shape_minimizer_6900.py
python3 .experiments/f101_m456_pure_centered_connector_discriminator_6900.py --case m5
python3 .experiments/f101_m456_pure_centered_connector_discriminator_6900.py --case m6
python3 .experiments/f101_small_matched_connector_scaling_6900.py --m 7 --jet-offset 1
python3 .experiments/f101_small_matched_connector_scaling_6900.py --m 8 --jet-offset 1 --offset-errors
python3 .experiments/full187_centered_three_companion_legality_6900.py
```

Observed exact receipts before this note was written:

```text
m4 connector canonical    6051da479adba552dfe771c69fec583fe7a6e49849f4a0aa6415c7a0a4c70c60
m5 shape canonical        c30341a79f57c93f47b5745c21537a4ec01e1ab096109166cc1a0e596dd0e66b
m6 shape canonical        e09a66988d0b8f09b0f62cbecb328eb40910294664f2856b2c41f8b395aa0cfe
m5 offset canonical       5ae6bc8b2c03a4e5d1fe0118bc8b8b06fcab6260a5d547c0370a416d1d5befa4
m6 offset canonical       37893a7a4fd298a13ecb88ac219c72afb36430b852bc1184014600ef9f2d45d3
small m7 canonical        fffdf5ac5c2d144e3c748bac5e54b7ae6daeec4adbc086cc52a7b9383025b4c0
small m8 canonical        d42900a36f42abf2c542d863ba4df030994086da17be77c7434bfe16ccd5e334
small offset m7 canonical fdb61c88b4461527ff962550d31d26598a46607e4b03c54c990a94923d85b34a
small offset m8 canonical 2936772077e2e1e0dd40d1502b6ad38827d5f6b0881676d1cde76326c905811e
target width canonical    f918c4b693ffdc1169b91c0810cf51a92c5045ddddd1b84982dacb996080b75e
```

Peak RSS was 87 MiB for the detailed m=4 connector, 185 MiB for m=5, 376 MiB
for matched m=6, 589 MiB for offset m=6, 219 MiB for the small m=7 scaling
control, and 382 MiB for m=8. Every run stayed below the external 4 GiB cap.

## Next theorem, with the false shortcut removed

Do not try to prove that one pure centered shell universally maps to the four
normals. The exact next target is a shape-tapered connecting statement:

> modulo the complete grade-82 prefix, the coefficientwise images of the
> legal centered/raw `(0,0)`, `(1,0)`, and `(0,1)` first-shell groups contain the four exact
> `F0,F1,F2,F3` residues, with a determinant whose leading term survives the
> Full187 strict X windows.

The finite results identify a plausible three-shape robust interface and
decisively remove both the rank-one/C00 shortcut and a universal two-shape
shortcut. They do not prove the displayed target.
